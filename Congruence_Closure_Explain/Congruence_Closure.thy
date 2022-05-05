chapter \<open>Congruence Closure Algorithm with Explain Operation\<close>
theory Congruence_Closure
  imports 
    Explain_Proofs2 
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
\<close>
record congruence_closure =
  cc_list :: "nat list"
  use_list :: "equation list list"
  lookup :: "equation option list list"
  proof_forest :: "nat list"
  pf_labels :: "pending_equation option list"

text \<open>For updating two dimensional lists.\<close>
fun upd :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list"
  where 
"upd xs n m e = xs[n := (xs ! n)[m := e]]"

fun lookup_Some :: "equation option list list \<Rightarrow> equation \<Rightarrow> bool"
  where
"lookup_Some t (F a\<^sub>1 a\<^sub>2 \<approx> a) = (\<not>Option.is_none ((t ! a\<^sub>1) ! a\<^sub>2))"
| "lookup_Some t (a \<approx> b) = False"

fun lookup_None :: "equation option list list \<Rightarrow> equation \<Rightarrow> bool"
  where
"lookup_None t (F a\<^sub>1 a\<^sub>2 \<approx> a) = (Option.is_none ((t ! a\<^sub>1) ! a\<^sub>2))"
| "lookup_None t (a \<approx> b) = False"

\<comment> \<open>Should only be used if \<open>lookup(a\<^sub>1, a\<^sub>2)\<close> is not None and if the equation is not of the type (a = b)\<close>
fun link_to_lookup :: "equation option list list \<Rightarrow> equation \<Rightarrow> pending_equation"
  where
"link_to_lookup t (F a\<^sub>1 a\<^sub>2 \<approx> a) = Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (the ((t ! a\<^sub>1) ! a\<^sub>2))"
  \<comment> \<open>This should not be invoked.\<close>
| "link_to_lookup t (a \<approx> b) = One (a \<approx> b)"

function set_lookup :: "equation option list list \<Rightarrow> equation list \<Rightarrow> nat list \<Rightarrow> equation option list list"
  where
"set_lookup t [] l = t"
| "set_lookup t ((F a\<^sub>1 a\<^sub>2 \<approx> a)#xs) l = 
    set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) xs l"
  \<comment> \<open>This should not be invoked.\<close>
| "set_lookup t ((a \<approx> b)#xs) l = set_lookup t xs l"
  by pat_completeness auto
termination by lexicographic_order

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

function add_edge :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
"add_edge pf e e' = (if pf ! e = e then (pf[e := e']) else add_edge (pf[e := e']) (pf ! e) e)"
  by pat_completeness auto

function add_label :: "pending_equation option list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> pending_equation \<Rightarrow> pending_equation option list"
  where
"add_label pfl pf e lbl = (if pf ! e = e then (pfl[e := Some lbl]) else add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)))"
  by pat_completeness auto
text \<open>To show: pfl ! e = None iff pf ! e = e\<close>

function propagate :: "pending_equation list \<Rightarrow> congruence_closure \<Rightarrow> congruence_closure"
  where
"propagate (pe # xs) \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl\<rparr> = 
(let a = left pe; b = right pe in
  (if rep_of l a = rep_of l b 
    then propagate xs \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl\<rparr>
    else
      propagate (xs @ (map (link_to_lookup t) (filter (lookup_Some t) (u ! rep_of l a))))
      \<lparr>cc_list = ufa_union l a b, 
      use_list = (u[rep_of l a := []])[rep_of l b := (u ! rep_of l b) @ (filter (lookup_None t) (u ! rep_of l a))], 
      lookup = set_lookup t (filter (lookup_None t) (u ! rep_of l a)) l,
      proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a pe\<rparr>
))"
| "propagate [] cc = cc"
  by pat_completeness auto


function merge :: "congruence_closure \<Rightarrow> equation \<Rightarrow> congruence_closure"
  where 
"merge cc (a \<approx> b) = propagate [One (a \<approx> b)] cc"

| "merge \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
(case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
Some eq 
      \<Rightarrow> propagate [Two (F a\<^sub>1 a\<^sub>2 \<approx> a) eq] \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl\<rparr>
| None 
      \<Rightarrow> \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)), 
          proof_forest = pf, pf_labels = pfl\<rparr>
)"
  by pat_completeness auto

fun are_congruent :: "congruence_closure \<Rightarrow> equation \<Rightarrow> bool"
  where
"are_congruent \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl\<rparr> (a \<approx> b) = 
    (rep_of l a = rep_of l b)"
| "are_congruent \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
    (case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
      Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<Rightarrow> (rep_of l a = rep_of l b)
    | None \<Rightarrow> False
)"

text \<open>For the initialisation of the congruence closure algorithm.\<close>
abbreviation 
"initial_cc n \<equiv> \<lparr>cc_list = [0..<n], use_list = replicate n [], lookup = replicate n (replicate n None),
                  proof_forest = [0..<n], pf_labels = replicate n None\<rparr>"


end