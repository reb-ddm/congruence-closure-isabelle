chapter \<open>Congruence Closure Algorithm with Explain Operation\<close>
theory Congruence_Closure
  imports 
    Explain_Proofs2 
begin

datatype 'a equation = Constants 'a 'a ("_ \<approx> _")
  | Function 'a 'a 'a                 ("F _ _ \<approx> _" )

datatype 'a pending_equation = One "'a equation"
  | Two "'a equation" "'a equation"

term "a \<approx> b"
term "F a b \<approx> c"

record congruence_closure =
  uf_list :: "nat list"
  class_list :: "nat list list"
  use_list :: "nat equation list list"
  lookup :: "nat equation option list list"


fun lookup_Some :: "nat equation option list list \<Rightarrow> nat equation \<Rightarrow> bool"
  where
"lookup_Some t (F a\<^sub>1 a\<^sub>2 \<approx> a) = (\<not>Option.is_none ((t ! a\<^sub>1) ! a\<^sub>2))"
| "lookup_Some t (a \<approx> b) = False"

fun lookup_None :: "nat equation option list list \<Rightarrow> nat equation \<Rightarrow> bool"
  where
"lookup_None t (F a\<^sub>1 a\<^sub>2 \<approx> a) = (Option.is_none ((t ! a\<^sub>1) ! a\<^sub>2))"
| "lookup_None t (a \<approx> b) = False"

\<comment> \<open>Should only be used if \<open>lookup(a\<^sub>1, a\<^sub>2)\<close> is not None and if the equation is not of the type (a = b)\<close>
fun link_to_lookup :: "nat equation option list list \<Rightarrow> nat equation \<Rightarrow> nat pending_equation"
  where
"link_to_lookup t (F a\<^sub>1 a\<^sub>2 \<approx> a) = Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (the ((t ! a\<^sub>1) ! a\<^sub>2))"
  \<comment> \<open>This should not be invoked.\<close>
| "link_to_lookup t (a \<approx> b) = One (a \<approx> b)"

function set_lookup :: "nat equation option list list \<Rightarrow> nat equation list \<Rightarrow> nat list \<Rightarrow> nat equation option list list"
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
and propagate :: "nat pending_equation list \<Rightarrow> congruence_closure \<Rightarrow> congruence_closure"
  where
"propagate_one \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr> a b =  
(if rep_of l a = rep_of l b 
    then \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr>
  else 
    propagate (map (link_to_lookup t) (filter (lookup_Some t) (u ! rep_of l a)))
    \<lparr>uf_list = ufa_union l a b, 
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


function merge:: "congruence_closure \<Rightarrow> nat equation \<Rightarrow> congruence_closure"
  where 
"merge \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr> (a \<approx> b) = 
propagate [One (a \<approx> b)] \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr>"

| "merge \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
(case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
Some eq 
      \<Rightarrow> propagate [Two (F a\<^sub>1 a\<^sub>2 \<approx> a) eq] \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr>
| None 
      \<Rightarrow> \<lparr>uf_list = l, class_list = c, 
use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
lookup = t[rep_of l a\<^sub>1 := (t ! rep_of l a\<^sub>1)[rep_of l a\<^sub>2 := Some (F a\<^sub>1 a\<^sub>2 \<approx> a)]]\<rparr>
)"
  by pat_completeness auto

fun are_congruent :: "congruence_closure \<Rightarrow> nat equation \<Rightarrow> bool"
  where
"are_congruent \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr> (a \<approx> b) = 
    (rep_of l a = rep_of l b)"
| "are_congruent \<lparr>uf_list = l, class_list = c, use_list = u, lookup = t\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a) = 
    (case (t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 of
      Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<Rightarrow> (rep_of l a = rep_of l b)
    | None \<Rightarrow> False
)"

end