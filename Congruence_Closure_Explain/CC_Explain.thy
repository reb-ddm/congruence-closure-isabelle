section \<open>Correctness proofs for congruence closure\<close>
theory CC_Explain
  imports CC_Invars 
begin 



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

function (domintros) explain_along_path :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
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
          (let (output, new_l, pending) = explain_along_path cc (ufa_union l a b) b c
          in ({a'} \<union> output, new_l, pending))
        | Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b') \<Rightarrow> 
          (let (output, new_l, pending) = explain_along_path cc (ufa_union l a b) b c
          in ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, new_l, [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] @ pending))
    )
  )
)"
  by pat_completeness auto

lemma explain_along_path_simp1:
  assumes "rep_of l a = rep_of l c"
  shows "explain_along_path cc l a c = ({}, l, [])"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path.domintros by blast
  then show ?thesis using explain_along_path.psimps 
    by (simp add: assms)
qed

lemma explain_along_path_simp2:
  assumes "rep_of l a \<noteq> rep_of l c"
"(pf_labels cc) ! rep_of l a = Some (One a')"
"(output, new_l, pend) = explain_along_path cc (ufa_union l a ((proof_forest cc) ! rep_of l a)) 
((proof_forest cc) ! rep_of l a) c"
  shows "explain_along_path cc l a c = ({a'} \<union> output, new_l, pend)"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path.domintros sorry
  then show ?thesis using explain_along_path.psimps unfolding Let_def
    by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(5))
qed

lemma explain_along_path_simp3:
  assumes "rep_of l a \<noteq> rep_of l c"
"(pf_labels cc) ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))"
"(output, new_l, pend) = explain_along_path cc (ufa_union l a ((proof_forest cc) ! rep_of l a)) 
((proof_forest cc) ! rep_of l a) c"
  shows "explain_along_path cc l a c = ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, new_l, [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] @ pend)"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path.domintros sorry
  then show ?thesis using explain_along_path.psimps unfolding Let_def
    using assms case_prod_conv option.sel pending_equation.simps(6) equation.simps(6) 
    by (metis (no_types, lifting))
qed

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


text "To show about pfl: left a = i and right a = pf ! i or opposite
also it's never None if pf ! i ~= i."

fun pending_set_explain :: "(nat * nat) list \<Rightarrow> equation set"
  where
"pending_set_explain pend = set (map (\<lambda>(a,b) . (a \<approx> b)) pend)"

lemma explain_along_path_correctness:
  assumes "ufa_invar pf"
"a < length pf"
"c < length pf"
"path pf c pAC a"
"length l = length pf"
"explain_along_path \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr> l a c = (output, new_l, pend)"
shows "(a \<approx> c) \<in> Congruence_Closure (representatives_set l \<union> output 
\<union> pending_set_explain pend)"
  using assms proof(induction arbitrary: "output" new_l pend l pAC rule: rep_of_induct)
  case (base i)
  then have "c = i" using path_root by auto
  then show ?case by blast
next
  case (step i)
  then show ?case proof(cases "rep_of l i = rep_of l c")
    case True
    then have "i \<approx> c \<in> Congruence_Closure (representatives_set l)"
      using CC_same_rep_representatives_set[of l i c] step by argo
    then show ?thesis 
      using Congruence_Closure_split_rule by auto
  next
    case False
    with step path_butlast have path_to_parent: "path pf c (butlast pAC) (pf ! i)" 
      by blast
    obtain output' new_l' pend' where recursive_step: "explain_along_path
     \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>
     (ufa_union l i (pf ! i)) (pf ! i) c = (output', new_l', pend')"
      using prod_cases3 by blast
    with step path_to_parent recursive_step have "(pf ! i \<approx> c) \<in>
 Congruence_Closure (representatives_set (ufa_union l i (pf ! i)) \<union> output' 
\<union> pending_set_explain pend')" by simp
    show ?thesis proof(cases "the (pfl ! rep_of l i)")
      case (One a')
      then have *: "pfl ! rep_of l i = Some (One a')" sorry
(*TODO add pfl invar, similar to pending invar*)
have dom: "explain_along_path_dom
     (\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>, 
l,i, c)" sorry 
   have "(output, new_l, pend) = ({a'} \<union> output', new_l', pend')" 
     using step(8) explain_along_path_simp2[OF False] One False * sledgehammer
     by (auto split: pending_equation.splits prod.splits)
      then show ?thesis sorry
    next
      case (Two x21 x22)
      then show ?thesis sorry
    qed
  qed
qed

subsection \<open>Correctness of explain\<close>

lemma cc_explain_correct:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain cc ([0..<nr_vars cc]) [(a, b)])"
  sorry

lemma cc_explain_valid:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc"
  shows "cc_explain cc ([0..<nr_vars cc]) [(a, b)] \<subseteq> input cc"
  sorry

end