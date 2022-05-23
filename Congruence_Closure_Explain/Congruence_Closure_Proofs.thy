section \<open>Correctness proofs for congruence closure\<close>
theory Congruence_Closure_Proofs
  imports CC_Abstraction 
begin 

fun apply_merges :: "congruence_closure \<Rightarrow> equation list \<Rightarrow> congruence_closure"
  where
"apply_merges cc (eq # xs) = apply_merges (merge cc eq) xs"
| "apply_merges cc [] = cc"



lemma cc_\<alpha>_eq_CC_representativeE: "cc_\<alpha> cc (s \<approx> t) = Congruence_Closure (representativeE cc) (s \<approx> t)"
  sorry

subsection \<open>Correctness of merge\<close>

lemma 
"valid_vars eq n \<Longrightarrow> cc_invar cc \<Longrightarrow> 
cc_\<alpha> (apply_merges (initial_cc n) xs) eq = Congruence_Closure (set xs) eq"
  sorry
lemma 
"valid_vars eq n \<Longrightarrow> cc_invar cc \<Longrightarrow> 
cc_\<alpha> cc eq = Congruence_Closure ((input cc)) eq"
  sorry

subsection \<open>Correctness of are_congruent\<close>
lemma "valid_vars eq (nr_vars cc) \<Longrightarrow> are_congruent cc eq = cc_\<alpha> cc eq"
  unfolding cc_\<alpha>_def by simp

subsection \<open>Correctness of explain\<close>

lemma "are_congruent cc (a \<approx> b) \<Longrightarrow> cc_invar cc \<Longrightarrow>
  Congruence_Closure (cc_explain cc ([0..<nr_vars cc]) [(a, b)]) (a \<approx> b)"
  sorry

end 