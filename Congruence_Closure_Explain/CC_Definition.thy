chapter \<open>Congruence Closure Algorithm with Explain Operation\<close>
theory CC_Definition
  imports 
    "../Union_Find_Explain/Explain_Correctness" 
begin

section \<open>Definitions\<close>

text \<open>The input equations to this congruence closure algorithm need 
      to be curryfied and flattened into terms of depth at most 2,
      by introducing the "apply" function \<open>f\<close> and new constants.
      
      The constants of the equation are represented by natural numbers,
      so that they can be also used as index of the union-find array.
      Each natural number represents an arbitrary constant, 
      which is not related to the number it is represented by.

      For example the equation \<open>2 \<approx> 5\<close> should be interpreted as \<open>c\<^sub>2 = c\<^sub>5\<close>.\<close>

datatype equation = Constants nat nat ("_ \<approx> _" 51)
  | Function nat nat nat                 ("F _ _ \<approx> _" 51)

datatype pending_equation = One equation
  | Two equation equation

term "a \<approx> b"
term "if (F a b \<approx> c) = F a b \<approx> c then False else True"
term "(F a b \<approx> c) = (F a b \<approx> c)"

text \<open>Data structure for the congruence closure operations (merge, are_congruent and explain):
  \<open>cc_list\<close>: parents of the union-find-like tree data structure without path compression
  \<open>use_list\<close>: for each representative \<open>a\<close>, a list if input equations \<open>f b\<^sub>1 b\<^sub>2 = b\<close>,
              where \<open>a\<close> is the representative of either \<open>b\<^sub>1\<close> or \<open>b\<^sub>2\<close>.
  \<open>lookup\<close>: table indexed by pairs of representatives \<open>b\<close> and \<open>c\<close>, 
            which stores an input equation \<open>f a\<^sub>1 a\<^sub>2 = a\<close> s.t.
            \<open>b\<close> and \<open>c\<close> are representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close> respectively,
            or None if no such equation exists.
  \<open>pending\<close>: a list whose elements are input equations a=b, or pairs of input equations 
             (f(a1, a2)=a, f(b1, b2)=b) where ai and bi are already congruent for i in {1, 2}. 
  \<open>proof_forest\<close>: tree-shaped graph, with the sequence of merge operations as edges
  \<open>pf_labels\<close>: for each edge in the \<open>proof_forest\<close>, a label with the input equations
  \<open>input\<close>: a set of the input equation, useful for proofs
\<close>
record congruence_closure =
  cc_list :: "nat list"
  use_list :: "equation list list"
  lookup :: "equation option list list"
  pending :: "pending_equation list"
  proof_forest :: "nat list"
  pf_labels :: "pending_equation option list"
  input :: "equation set"

text \<open>For updating two dimensional lists.\<close>
abbreviation upd :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list"
  where 
"upd xs n m e \<equiv> xs[n := (xs ! n)[m := e]]"

text \<open>Finds the entry in the lookup table for the representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close>.\<close>
abbreviation lookup_entry :: "equation option list list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> equation option"
  where
"lookup_entry t l a\<^sub>1 a\<^sub>2 \<equiv> t ! rep_of l a\<^sub>1 ! rep_of l a\<^sub>2"

fun lookup_Some :: "equation option list list \<Rightarrow> nat list \<Rightarrow> equation \<Rightarrow> bool"
  where
"lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a) = (\<not>Option.is_none (lookup_entry t l a\<^sub>1 a\<^sub>2))"
| "lookup_Some t l (a \<approx> b) = False"

\<comment> \<open>Should only be used if \<open>lookup(a\<^sub>1, a\<^sub>2)\<close> is not None and if the equation is not of the type (a = b)\<close>
fun link_to_lookup :: "equation option list list \<Rightarrow> nat list \<Rightarrow> equation \<Rightarrow> pending_equation"
  where
"link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) = Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (the (lookup_entry t l a\<^sub>1 a\<^sub>2))"
  \<comment> \<open>This should not be invoked.\<close>
| "link_to_lookup t l (a \<approx> b) = One (a \<approx> b)"

\<comment> \<open>Should only be used if \<open>lookup(a\<^sub>1, a\<^sub>2)\<close> is not None and if the equation is not of the type (a = b)\<close>
fun update_lookup :: "equation option list list \<Rightarrow> nat list \<Rightarrow> equation \<Rightarrow> equation option list list"
  where
"update_lookup t l (F c\<^sub>1 c\<^sub>2 \<approx> c) = upd t (rep_of l c\<^sub>1) (rep_of l c\<^sub>2) (Some (F c\<^sub>1 c\<^sub>2 \<approx> c))"
  \<comment> \<open>This should not be invoked.\<close>
| "update_lookup t l (a \<approx> b) = t"

fun left :: "pending_equation \<Rightarrow> nat"
  where
"left (One (a \<approx> b)) = a"
| "left (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)) = a"
  \<comment> \<open>This should not be invoked.\<close>
| "left a = undefined"

fun right :: "pending_equation \<Rightarrow> nat"
  where
"right (One (a \<approx> b)) = b"
| "right (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)) = b"
  \<comment> \<open>This should not be invoked.\<close>
| "right a = undefined"

text \<open>Implementation of the proof forest\<close>

function (domintros) add_edge :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
"add_edge pf e e' = (if pf ! e = e then (pf[e := e']) else add_edge (pf[e := e']) (pf ! e) e)"
  by pat_completeness auto

lemma add_edge_rel: "rep_of_rel (l, x) (l, y) \<longleftrightarrow> add_edge_rel (l[y := y'], x, y) (l, y, y')" 
proof
  show "rep_of_rel (l, x) (l, y) \<Longrightarrow> add_edge_rel (l[y := y'], x, y) (l, y, y')"
    by (induction "(l, x)" "(l, y)" rule: rep_of_rel.induct)(auto simp add: add_edge_rel.intros)
next
  show "add_edge_rel (l[y := y'], x, y) (l, y, y') \<Longrightarrow> rep_of_rel (l, x) (l, y)"
    by (induction "(l[y := y'], x, y)" "(l, y, y')" rule: add_edge_rel.induct) (auto simp add: rep_of_rel.intros)
qed

function (domintros) add_label :: "pending_equation option list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> pending_equation \<Rightarrow> pending_equation option list"
  where
"add_label pfl pf e lbl = (if pf ! e = e then (pfl[e := Some lbl]) else add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)))"
  by pat_completeness auto

fun propagate_loop
  where
"propagate_loop rep_b (u1 # urest) 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
=
  propagate_loop rep_b urest (
    if (lookup_Some t l u1)
    then 
      \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l u1#pe,
            proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
    else
      \<lparr>cc_list = l,
            use_list = u[rep_b := u1 # (u ! rep_b)],
            lookup = update_lookup t l u1, 
            pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
)"
| "propagate_loop _ [] cc = cc"

abbreviation propagate_step
  where 
"propagate_step l u t pe pf pfl ip a b eq \<equiv> 
  propagate_loop (rep_of l b) (u ! rep_of l a)
    \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"

function (domintros) propagate :: "congruence_closure \<Rightarrow> congruence_closure"
  where
"propagate \<lparr>cc_list = l, use_list = u, lookup = t, pending = [], proof_forest = pf, pf_labels = pfl, input = ip\<rparr> = 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = [], proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
| "propagate 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr> = 
(let a = left eq; b = right eq in
  (if rep_of l a = rep_of l b 
    then propagate \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
    else
      propagate (propagate_step l u t pe pf pfl ip a b eq)
))"
  by pat_completeness auto

lemma propagate_simps1[simp]:
  assumes "propagate_dom cc"
"pending cc = []"
shows "propagate cc = cc"
  using assms propagate.psimps propagate.pelims by fastforce

lemma propagate_simps2[simp]:
  assumes "propagate_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
"rep_of l (left eq) = rep_of l (right eq)"
shows "propagate 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
 = propagate \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  using assms propagate.psimps unfolding Let_def by auto

lemma propagate_simps3[simp]:
  assumes "propagate_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
"rep_of l (left eq) \<noteq> rep_of l (right eq)"
shows "propagate 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
 = propagate (propagate_step l u t pe pf pfl ip (left eq) (right eq) eq)"
  using assms propagate.psimps unfolding Let_def by auto

fun merge :: "congruence_closure \<Rightarrow> equation \<Rightarrow> congruence_closure"
  where 
"merge \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
(a \<approx> b) = 
  propagate 
    \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"

| "merge \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
(F a\<^sub>1 a\<^sub>2 \<approx> a) = 
(if (lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a))
  then propagate \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>
  else \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>
)"

text \<open>The input must be a valid index (a < nr_vars cc \<and> b < nr_vars cc)\<close>
fun are_congruent :: "congruence_closure \<Rightarrow> equation \<Rightarrow> bool"
  where
"are_congruent \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (a \<approx> b) = 
    (rep_of l a = rep_of l b)"
| "are_congruent \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
    (case lookup_entry t l a\<^sub>1 a\<^sub>2 of
      Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<Rightarrow> (rep_of l a = rep_of l b)
    | None \<Rightarrow> False
)"

text \<open>For the initialisation of the congruence closure algorithm.\<close>
abbreviation 
"initial_cc n \<equiv> \<lparr>cc_list = [0..<n], use_list = replicate n [], lookup = replicate n (replicate n None),
                  pending = [], proof_forest = [0..<n], pf_labels = replicate n None, input = {}\<rparr>"

end
