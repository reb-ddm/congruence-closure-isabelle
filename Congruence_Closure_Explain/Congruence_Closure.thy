chapter \<open>Congruence Closure Algorithm with Explain Operation\<close>
theory Congruence_Closure
  imports 
    "../Union_Find_Explain/Explain_Proofs2" 
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

datatype equation = Constants nat nat ("_ \<approx> _")
  | Function nat nat nat                 ("F _ _ \<approx> _" 51)

datatype pending_equation = One equation
  | Two equation equation

term "a \<approx> b"
term "if F a b \<approx> c = F a b \<approx> c then False else True"
term "(F a b \<approx> c) = (F a b \<approx> c)"

text \<open>Data structure for the congruence closure operations (merge, are_congruent and explain):
  \<open>cc_list\<close>: parents of the union-find-like tree data structure without path compression
  \<open>use_list\<close>: for each representative \<open>a\<close>, a list if input equations \<open>f b\<^sub>1 b\<^sub>2 = b\<close>,
              where \<open>a\<close> is the representative of either \<open>b\<^sub>1\<close> or \<open>b\<^sub>2\<close>.
  \<open>lookup\<close>: table indexed by pairs of representatives \<open>b\<close> and \<open>c\<close>, 
            which stores an input equation \<open>f a\<^sub>1 a\<^sub>2 = a\<close> s.t.
            \<open>b\<close> and \<open>c\<close> are representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close> respectively,
            or None if no such equation exists.
  \<open>proof_forest\<close>: tree-shaped graph, with the sequence of merge operations as edges
  \<open>pf_labels\<close>: for each edge in the \<open>proof_forest\<close>, a label with the input equations
  \<open>input\<close>: a list of the input equation, useful for proofs
\<close>
record congruence_closure =
  cc_list :: "nat list"
  use_list :: "equation list list"
  lookup :: "equation option list list"
  proof_forest :: "nat list"
  pf_labels :: "pending_equation option list"
  input :: "equation set"

text \<open>For updating two dimensional lists.\<close>
fun upd :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list"
  where 
"upd xs n m e = xs[n := (xs ! n)[m := e]]"

text \<open>Finds the entry in the lookup table for the representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close>.\<close>
abbreviation lookup_entry :: "equation option list list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> equation option"
  where
"lookup_entry t l a\<^sub>1 a\<^sub>2 \<equiv> ((t ! (rep_of l a\<^sub>1)) ! (rep_of l a\<^sub>2))"

fun lookup_Some :: "equation option list list \<Rightarrow> nat list \<Rightarrow> equation \<Rightarrow> bool"
  where
"lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a) = (\<not>Option.is_none (lookup_entry t l a\<^sub>1 a\<^sub>2))"
| "lookup_Some t l (a \<approx> b) = False"

fun lookup_None :: "equation option list list \<Rightarrow> nat list \<Rightarrow> equation \<Rightarrow> bool"
  where
"lookup_None t l (F a\<^sub>1 a\<^sub>2 \<approx> a) = (Option.is_none (lookup_entry t l a\<^sub>1 a\<^sub>2))"
| "lookup_None t l (a \<approx> b) = False"

\<comment> \<open>Should only be used if \<open>lookup(a\<^sub>1, a\<^sub>2)\<close> is not None and if the equation is not of the type (a = b)\<close>
fun link_to_lookup :: "equation option list list \<Rightarrow> nat list \<Rightarrow> equation \<Rightarrow> pending_equation"
  where
"link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) = Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (the (lookup_entry t l a\<^sub>1 a\<^sub>2))"
  \<comment> \<open>This should not be invoked.\<close>
| "link_to_lookup t l (a \<approx> b) = One (a \<approx> b)"

fun set_lookup :: "equation option list list \<Rightarrow> equation list \<Rightarrow> nat list \<Rightarrow> equation option list list"
  where
"set_lookup t [] l = t"
| "set_lookup t ((F a\<^sub>1 a\<^sub>2 \<approx> a)#xs) l = 
    set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) xs l"
  \<comment> \<open>This should not be invoked.\<close>
| "set_lookup t ((a \<approx> b)#xs) l = set_lookup t xs l"


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
text \<open>To show: pfl ! e = None iff pf ! e = e\<close>

abbreviation propagate_step
  where 
"propagate_step l u t pf pfl ip a b pe \<equiv> \<lparr>cc_list = ufa_union l a b,
        use_list = u[rep_of l a := [], rep_of l b := u ! rep_of l b @ filter (lookup_None t l) (u ! rep_of l a)],
        lookup = set_lookup t (filter (lookup_None t l) (u ! rep_of l a)) l, 
        proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a pe, input = ip\<rparr>"

function propagate :: "pending_equation list \<Rightarrow> congruence_closure \<Rightarrow> congruence_closure"
  where
"propagate [] cc = cc"
| "propagate (pe # xs) \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> = 
(let a = left pe; b = right pe in
  (if rep_of l a = rep_of l b 
    then propagate xs \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
    else
      propagate (xs @ (map (link_to_lookup t l) (filter (lookup_Some t l) (u ! rep_of l a))))
      (propagate_step l u t pf pfl ip a b pe)
))"
  by pat_completeness auto

lemma propagate_simp2:
  assumes "propagate_dom ((pe # xs), cc)"
          "a = left pe" "b = right pe" "rep_of (cc_list cc) a = rep_of (cc_list cc) b"
        shows "propagate (pe # xs) cc = propagate xs cc"
  using assms congruence_closure.cases propagate.psimps unfolding Let_def 
  by (metis congruence_closure.select_convs(1))

lemma propagate_simp2':
  assumes "propagate_dom ((pe # xs), \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)"
          "a = left pe" "b = right pe" "rep_of l a = rep_of l b"
        shows "propagate (pe # xs) \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> = propagate xs \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  using assms congruence_closure.cases propagate.psimps unfolding Let_def 
  by presburger

lemma propagate_simp3: 
  assumes "propagate_dom ((pe # xs), \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)"
          "a = left pe" "b = right pe" "rep_of l a \<noteq> rep_of l b"
    shows"propagate (pe # xs) \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> = 
           propagate (xs @ (map (link_to_lookup t l) (filter (lookup_Some t l) (u ! rep_of l a))))
              (propagate_step l u t pf pfl ip a b pe)"
  using assms propagate.psimps unfolding Let_def 
  by presburger

lemmas propagate_simps[simp] = propagate.psimps(1) propagate_simp2 propagate_simp3

fun merge :: "congruence_closure \<Rightarrow> equation \<Rightarrow> congruence_closure"
  where 
"merge \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (a \<approx> b) = 
  propagate [One (a \<approx> b)]  \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"

| "merge \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
(case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
Some eq 
      \<Rightarrow> propagate [Two (F a\<^sub>1 a\<^sub>2 \<approx> a) eq] \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>
| None 
      \<Rightarrow> \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)), 
          proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>
)"

text \<open>The input must be a valid index (a < nr_vars cc \<and> b < nr_vars cc)\<close>
fun are_congruent :: "congruence_closure \<Rightarrow> equation \<Rightarrow> bool"
  where
"are_congruent \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (a \<approx> b) = 
    (rep_of l a = rep_of l b)"
| "are_congruent \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
    (case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
      Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<Rightarrow> (rep_of l a = rep_of l b)
    | None \<Rightarrow> False
)"

text \<open>For the initialisation of the congruence closure algorithm.\<close>
abbreviation 
"initial_cc n \<equiv> \<lparr>cc_list = [0..<n], use_list = replicate n [], lookup = replicate n (replicate n None),
                  proof_forest = [0..<n], pf_labels = replicate n None, input = {}\<rparr>"


section \<open>Explain definition\<close>

text \<open>The highest node is in this case the same as the rep_of, because we do not 
      have the optimisation of checking which equivalence class is bigger, 
      we just make the union in the given order. When adding this optimisation,
      a highest_node function must be also implemented. \<close>

text \<open>There are three variables changed by the function \<open>explain_along_path\<close>: 

      The overall output of explain
      The Union Find list of the additional union find, which is local to the explain function
      The list of pending proofs, which need to be recursively called with cc_explain
      
      These are the three values returned by this function.\<close>

function explain_along_path :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    (equation set * nat list * (nat * nat) list)"
  where 
"explain_along_path cc l a c = 
(if rep_of l a = rep_of l c 
then
  ({}, l, [])
else
  (let b = (proof_forest cc) ! rep_of l a in 
    (
    case the ((pf_labels cc) ! rep_of l a) of 
        One a' \<Rightarrow>  
          (let (output, new_l, pending) = explain_along_path cc (ufa_union l a b) (rep_of l b) c
          in ({a'} \<union> output, new_l, pending))
\<comment> \<open>wieso ist das überhaupt legal\<close>
        | Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b') \<Rightarrow> 
          (let (output, new_l, pending) = explain_along_path cc (ufa_union l a b) (rep_of l b) c
          in ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, new_l, [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] @ pending))
    )
  )
)"
  by pat_completeness auto


function cc_explain :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> (nat * nat) list \<Rightarrow> equation set"
  where
"cc_explain cc l [] = {}"
| "cc_explain cc l ((a, b) # xs) =
(if are_congruent cc (a \<approx> b)
then
  (let c = lowest_common_ancestor (proof_forest cc) a b;
   (output1, new_l, pending1) = explain_along_path cc l a c;
   (output2, new_new_l, pending2) = explain_along_path cc new_l b c
  in
    output1 \<union> output2 \<union> cc_explain cc new_new_l (xs @ pending1 @ pending2))
else cc_explain cc l xs)
"
  by pat_completeness auto


end