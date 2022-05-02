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
  | Function nat nat nat                 ("F _ _ \<approx> _" )

datatype pending_equation = One equation
  | Two equation equation

term "a \<approx> b"
term "F a b \<approx> c"

text \<open>Data structure for the congruence closure operations (merge, are_congruent and explain):
  \<open>cc_list\<close>: parents of the union-find-like tree data structure without path compression
  \<open>class_list\<close>: stores for each representative a list with all the constants of the class (maybe not useful) 
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
  class_list :: "nat list list"
  use_list :: "equation list list"
  lookup :: "equation option list list"

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
    set_lookup (t[rep_of l a\<^sub>1 := (t ! rep_of l a\<^sub>1)[rep_of l a\<^sub>2 := Some (F a\<^sub>1 a\<^sub>2 \<approx> a)]]) xs l"
  \<comment> \<open>This should not be invoked.\<close>
| "set_lookup t ((a \<approx> b)#xs) l =
    set_lookup t xs l"
  by pat_completeness auto
termination by lexicographic_order

function propagate_one :: "congruence_closure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> congruence_closure"
and propagate :: "pending_equation list \<Rightarrow> congruence_closure \<Rightarrow> congruence_closure"
  where
"propagate_one \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr> a b =  
(if rep_of l a = rep_of l b 
    then \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr>
  else 
    propagate (map (link_to_lookup t) (filter (lookup_Some t) (u ! rep_of l a)))
    \<lparr>cc_list = ufa_union l a b, 
    class_list = (c[rep_of l a := []])[rep_of l b := (c ! rep_of l b) @ (c ! rep_of l a)],
    use_list = (u[rep_of l a := []])[rep_of l b := (u ! rep_of l b) @ (filter (lookup_None t) (u ! rep_of l a))], 
    lookup = set_lookup t (filter (lookup_None t) (u ! rep_of l a)) l\<rparr>
)
"
|
"propagate ((One (a \<approx> b))#xs) cc = propagate xs 
\<comment> \<open>TODO: insert edge into proof forest\<close>
(propagate_one cc a b)"
| "propagate ((Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))#xs) cc = propagate xs 
\<comment> \<open>TODO: insert edge into proof forest\<close>
(propagate_one cc a b)"
| "propagate [] cc = cc"
  \<comment> \<open>These should not be invoked.\<close>
| "propagate ((One (F a1 a2 \<approx> b))#xs) cc = cc"
| "propagate ((Two (a \<approx> b) eq\<^sub>2)#xs) cc = cc"
| "propagate ((Two eq\<^sub>1  (a \<approx> b))#xs) cc = cc"
  by pat_completeness auto


function merge:: "congruence_closure \<Rightarrow> equation \<Rightarrow> congruence_closure"
  where 
"merge \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr> (a \<approx> b) = 
propagate [One (a \<approx> b)] \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr>"

| "merge \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
(case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
Some eq 
      \<Rightarrow> propagate [Two (F a\<^sub>1 a\<^sub>2 \<approx> a) eq] \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr>
| None 
      \<Rightarrow> \<lparr>cc_list = l, class_list = c, 
use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
lookup = t[rep_of l a\<^sub>1 := (t ! rep_of l a\<^sub>1)[rep_of l a\<^sub>2 := Some (F a\<^sub>1 a\<^sub>2 \<approx> a)]]\<rparr>
)"
  by pat_completeness auto

fun are_congruent :: "congruence_closure \<Rightarrow> equation \<Rightarrow> bool"
  where
"are_congruent \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr> (a \<approx> b) = 
    (rep_of l a = rep_of l b)"
| "are_congruent \<lparr>cc_list = l, class_list = c, use_list = u, lookup = t\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
    (case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
      Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<Rightarrow> (rep_of l a = rep_of l b)
    | None \<Rightarrow> False
)"

text \<open>Implementation of the proof forest\<close>

function add_edge :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
"add_edge pf e e' = (if pf ! e = e then (pf[e := e']) else add_edge (pf[e := e']) (pf ! e) e)"
  by pat_completeness auto

text \<open>For the initialisation of the congruence closure algorithm.\<close>
abbreviation 
"initial_cc n \<equiv> \<lparr>cc_list = [0..<n], class_list = replicate n [], use_list = replicate n [], lookup = replicate n (replicate n None)\<rparr>"


end