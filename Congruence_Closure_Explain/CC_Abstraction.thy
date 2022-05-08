theory CC_Abstraction
  imports Congruence_Closure
begin

section \<open>Abstract formalisation of congruence closure\<close>

datatype equation_term = Apply equation_term equation_term | Symb nat


text \<open>S is the set of input equations.
The Congruence Closure is the smallest relation that includes S and is closed under reflexivity,
symmetry, transitivity, and under function application.
Source: \<open>https://drops.dagstuhl.de/opus/volltexte/2021/14253/pdf/LIPIcs-FSCD-2021-15.pdf\<close>\<close>

inductive Congruence_Closure :: "(equation_term * equation_term) set \<Rightarrow> (equation_term * equation_term) \<Rightarrow> bool"
  where
base: "eqt \<in> S \<Longrightarrow> Congruence_Closure S eqt"
| reflexive: "Congruence_Closure S (a, a)"
| symmetric: "Congruence_Closure S (a, b) \<Longrightarrow> Congruence_Closure S (b, a)"
| transitive: "Congruence_Closure S (a, b) \<Longrightarrow> Congruence_Closure S (b, c) \<Longrightarrow> Congruence_Closure S (a, c)"
| monotonic: "Congruence_Closure S (a\<^sub>1, b\<^sub>1) \<Longrightarrow> Congruence_Closure S (a\<^sub>2, b\<^sub>2) \<Longrightarrow> Congruence_Closure S ((Apply a\<^sub>1 a\<^sub>2), (Apply b\<^sub>1 b\<^sub>2))"

fun equation_\<alpha> :: "equation \<Rightarrow> equation_term * equation_term"
  where
"equation_\<alpha> (a \<approx> b) = (Symb a, Symb b)"
| "equation_\<alpha> (F a b \<approx> c) = (Apply (Symb a) (Symb b), Symb c)"

fun CC_union :: "(equation \<Rightarrow> bool) \<Rightarrow> (equation_term * equation_term) \<Rightarrow> (equation_term * equation_term) \<Rightarrow> bool"
  where
"CC_union CC (a, b) (a', b') = Congruence_Closure ({equation_\<alpha> eq | eq. CC eq} \<union> {(a, b)}) (a', b')"

fun valid_vars :: "equation \<Rightarrow> nat \<Rightarrow> bool"
  where
"valid_vars (a \<approx> b) n = (a < n \<and> b < n)"
| "valid_vars (F a b \<approx> c) n = (a < n \<and> b < n \<and> c < n)"

abbreviation nr_vars :: "congruence_closure \<Rightarrow> nat"
  where
"nr_vars cc \<equiv> length (cc_list cc)"

definition cc_\<alpha> :: "congruence_closure \<Rightarrow> equation \<Rightarrow> bool"
  where
"cc_\<alpha> cc x \<equiv> valid_vars x (nr_vars cc) \<and> are_congruent cc x"

text \<open>TODO\<close>
abbreviation cc_invar :: "congruence_closure \<Rightarrow> bool"
  where
"cc_invar cc \<equiv> True"

text \<open>The length of all arrays of congruence_closure is always nr_vars cc\<close>
lemma length_initial_cc:
"nr_vars (initial_cc n) = n"
"nr_vars (initial_cc n) = length (use_list (initial_cc n))"
"nr_vars (initial_cc n) = length (lookup (initial_cc n))"
"nr_vars (initial_cc n) = length (proof_forest (initial_cc n))"
"nr_vars (initial_cc n) = length (pf_labels (initial_cc n))"
  by auto

lemma set_lookup_preserves_length:
"length t = n \<Longrightarrow> length (set_lookup t a b) = n"
  apply(induction t a b rule: set_lookup.induct)
  by auto

lemma add_edge_preserves_length:
"add_edge_dom (pf, a, b) \<Longrightarrow> length pf = n \<Longrightarrow> length (add_edge pf a b) = n"
  apply(induction pf a b rule: add_edge.pinduct)
  by (simp add: add_edge.psimps)

lemma add_label_preserves_length:
"add_label_dom (pfl, a, b, c) \<Longrightarrow> length pfl = n \<Longrightarrow> length (add_label pfl a b c) = n"
  apply(induction pfl a b c rule: add_label.pinduct)
  by (simp add: add_label.psimps)

lemma propagate_preserves_length_cc_list:
  assumes "propagate_dom (a, cc)" 
  shows "nr_vars cc = n \<Longrightarrow> nr_vars (propagate a cc) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  by auto

lemma propagate_preserves_length_use_list:
  assumes "propagate_dom (a, cc)" "length (use_list cc) = n "
  shows "length (use_list (propagate a cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def 
  by auto

lemma propagate_preserves_length_lookup:
  assumes "propagate_dom (a, cc)" "length (lookup cc) = n" 
(*"add_edge_dom(proof_forest cc, a, b)"*)
  shows "length (lookup (propagate a cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  sorry

lemma propagate_preserves_length_proof_forest:
  assumes "propagate_dom (a, cc)" "length (proof_forest cc) = n "
  shows "length (proof_forest (propagate a cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  sorry

lemma propagate_preserves_length_pf_labels:
  assumes "propagate_dom (a, cc)" "length (pf_labels cc) = n "
  shows "length (pf_labels (propagate a cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  sorry





end