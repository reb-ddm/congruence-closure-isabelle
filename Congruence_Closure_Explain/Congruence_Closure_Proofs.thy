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

subsection \<open>Correctness of merge v2\<close>

lemma 
"valid_vars eq n \<Longrightarrow> cc_invar cc \<Longrightarrow> 
cc_\<alpha> (apply_merges (initial_cc n) xs) eq = Congruence_Closure_v2 (set xs) eq"
  sorry
lemma 
"valid_vars eq n \<Longrightarrow> cc_invar cc \<Longrightarrow> 
cc_\<alpha> cc eq = Congruence_Closure_v2 (set (input cc)) eq"
  sorry

subsection \<open>Correctness of are_congruent\<close>
lemma "valid_vars eq (nr_vars cc) \<Longrightarrow> are_congruent cc eq = cc_\<alpha> cc eq"
  unfolding cc_\<alpha>_def by simp

subsection \<open>Correctness of explain\<close>
lemma "are_congruent cc (a \<approx> b) \<Longrightarrow> cc_invar cc \<Longrightarrow>
  Congruence_Closure (equation_\<alpha> ` (cc_explain cc ([0..<nr_vars cc]) [(a,b)])) (Symb a, Symb b)"
  sorry

lemma "are_congruent cc (a \<approx> b) \<Longrightarrow> cc_invar cc \<Longrightarrow>
  Congruence_Closure_v2 (cc_explain cc ([0..<nr_vars cc]) [(a, b)]) (a \<approx> b)"
  sorry

end 