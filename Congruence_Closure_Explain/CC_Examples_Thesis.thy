theory CC_Examples_Thesis
  imports Examples_Thesis CC_Explain
begin 

text \<open>In order to execute the functions, they need to terminate.\<close>

termination propagate sorry
termination add_label sorry
termination add_edge sorry
termination cc_explain_aux sorry
termination explain_along_path sorry

text \<open>Example 8\<close>

abbreviation "ex8 \<equiv> add_edge [0, 0, 2, 2] 3 1"
value ex8

text \<open>Example 9\<close>

abbreviation "ex9_1 \<equiv> merge (merge (initial_cc 4) (1 \<approx> 0)) (3 \<approx> 2)"
value "proof_forest ex9_1"
value "rep_of (cc_list ex9_1) 2"
abbreviation "ex9_2 \<equiv> merge ex9_1 (F 0 2 \<approx> 1)"
value "use_list ex9_2"
value "lookup ex9_2"
abbreviation "ex9_3 \<equiv> merge ex9_2 (F 1 3 \<approx> 3)"
value "rep_of (cc_list ex9_3) 2"
value "proof_forest ex9_3"
value "pf_labels ex9_3"
value "use_list ex9_3"
value "lookup ex9_3"

text \<open>Example 10\<close>

abbreviation "ex10 \<equiv> cc_explain ex9_3 3 1"
value ex10

abbreviation "ex10_1 \<equiv> explain_along_path ex9_3 [0..<4] 3 1"
value ex10_1

text \<open>Example 11\<close>

abbreviation "ex11 \<equiv> \<lparr>cc_list = [1, 1, 1, 3], use_list = [[], [], [], []],
    lookup = [[None, None, None, None], [None, None, None, None], [None, None, None, None], [None, None, None, None]], pending = [],
    proof_forest = [1, 1, 1, 3], pf_labels = [Some (Two (F 0 3 \<approx> 0) (F 1 3 \<approx> 1)), None, Some (One (2 \<approx> 1)), None], 
    input = {F 0 3 \<approx> 0, F 1 3 \<approx> 1, 2 \<approx> 1}\<rparr>"
value "cc_explain ex11 0 1"

end
