theory Examples_Thesis
  imports Helper_Functions
begin 

text \<open>In order to execute the functions, they need to terminate.\<close>

termination path_to_root sorry
termination rep_of sorry
termination find_newest_on_path sorry
termination explain sorry

text \<open>Example 1\<close>

abbreviation "ex1 \<equiv> initial_ufe 4"
value ex1

text \<open>Example 2\<close>

abbreviation "ex2 \<equiv> ufe_union ex1 3 2"
value ex2

text \<open>Example 3\<close>

abbreviation "ex3 \<equiv> apply_unions [(3,2), (3,0), (1,0)] ex1"
value ex3

abbreviation "l \<equiv> uf_list ex3"
value l

text \<open>Example 4\<close>

abbreviation "ex4 \<equiv> path_to_root l 3"
value ex4

text \<open>Example 5\<close>

abbreviation "ex5 \<equiv> lowest_common_ancestor l 3 1"
value ex5

text \<open>Example 6\<close>

abbreviation "ex6_1 \<equiv> find_newest_on_path l (au ex3) 3 0"
value ex6_1
abbreviation "ex6_2 \<equiv> find_newest_on_path l (au ex3) 1 0"
value ex6_2

text \<open>Example 7\<close>

abbreviation "ex7 \<equiv> explain ex3 3 1"
value ex7

end
