section \<open>Correctness proofs for congruence closure\<close>
theory Congruence_Closure_Proofs
  imports CC_Abstraction 
begin 

fun apply_merges :: "congruence_closure \<Rightarrow> equation list \<Rightarrow> congruence_closure"
  where
"apply_merges cc (eq # xs) = apply_merges (merge cc eq) xs"
| "apply_merges cc [] = cc"

subsection \<open>Correctness of merge\<close>

lemma "CC_union (cc_\<alpha> cc) (equation_\<alpha> eq) (equation_\<alpha> eq') = cc_\<alpha> (merge cc eq) eq'"
  sorry

lemma 
"valid_vars eq n \<Longrightarrow>
cc_\<alpha> (apply_merges (initial_cc n) xs) eq = Congruence_Closure (equation_\<alpha> ` set xs) (equation_\<alpha> eq)"
  sorry

subsection \<open>Correctness of are_congruent\<close>



subsection \<open>Correctness of explain\<close>


end 