section \<open>Correctness proofs for congruence closure\<close>
theory CC_Explain
  imports CC_Invars 
begin 


subsection \<open>Correctness of explain\<close>

lemma "are_congruent cc (a \<approx> b) \<Longrightarrow> cc_invar cc \<Longrightarrow>
  Congruence_Closure (cc_explain cc ([0..<nr_vars cc]) [(a, b)]) (a \<approx> b)"
  sorry

end