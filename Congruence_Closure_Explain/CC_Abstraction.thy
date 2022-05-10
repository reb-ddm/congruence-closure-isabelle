theory CC_Abstraction
  imports Congruence_Closure
begin

section \<open>Abstract formalisation of congruence closure\<close>


text \<open>S is the set of input equations.
The Congruence Closure is the smallest relation that includes S and is closed under reflexivity,
symmetry, transitivity, and under function application.
Source: \<open>https://drops.dagstuhl.de/opus/volltexte/2021/14253/pdf/LIPIcs-FSCD-2021-15.pdf\<close>\<close>

inductive Congruence_Closure :: "equation set \<Rightarrow> equation \<Rightarrow> bool"
  where
base: "eqt \<in> S \<Longrightarrow> Congruence_Closure S eqt"
| reflexive: "Congruence_Closure S (a \<approx> a)"
| symmetric: "Congruence_Closure S (a \<approx> b) \<Longrightarrow> Congruence_Closure S (b \<approx> a)"
| transitive: "Congruence_Closure S (a \<approx> b) \<Longrightarrow> Congruence_Closure S (b \<approx> c) \<Longrightarrow> Congruence_Closure S (a \<approx> c)"
| monotonic: "Congruence_Closure S (F a\<^sub>1 a\<^sub>2 \<approx> a) \<Longrightarrow> Congruence_Closure S (F b\<^sub>1 b\<^sub>2 \<approx> b) 
\<Longrightarrow> Congruence_Closure S (a\<^sub>1 \<approx> b\<^sub>1) \<Longrightarrow> Congruence_Closure S (a\<^sub>2 \<approx> b\<^sub>2)
\<Longrightarrow> Congruence_Closure S (a \<approx> b)"

definition CC_union :: "(equation \<Rightarrow> bool) \<Rightarrow> equation \<Rightarrow> equation \<Rightarrow> bool"
  where
"CC_union CC eq' = Congruence_Closure ({eq | eq. CC eq} \<union> {eq'})"

lemma Congruence_Closure_union:
"Congruence_Closure S eqt \<Longrightarrow> Congruence_Closure (S \<union> S') eqt"
  apply(induction rule: Congruence_Closure.induct)
  using base apply blast
  using reflexive apply blast
  using symmetric apply blast
  using transitive apply blast
  using monotonic apply blast
  done

lemma CC_union_correct: 
"CC_union (Congruence_Closure S) eq' eq = Congruence_Closure (S \<union> {eq'}) eq"
proof
  show "CC_union (Congruence_Closure S) eq' eq \<Longrightarrow> Congruence_Closure (S \<union> {eq'}) eq"
    unfolding CC_union_def
    apply(induction "{eqa |eqa. Congruence_Closure S eqa} \<union> {eq'}" eq rule: Congruence_Closure.induct)
    using base Congruence_Closure_union apply blast
    using reflexive apply blast
    using symmetric apply blast
    using transitive apply blast
    using monotonic apply blast
    done
next
  show "Congruence_Closure (S \<union> {eq'}) eq \<Longrightarrow> CC_union (Congruence_Closure S) eq' eq"
    apply(induction "S \<union> {eq'}" eq rule: Congruence_Closure.induct)
    unfolding CC_union_def 
    using base apply auto[1]
    using reflexive apply auto[1]
    using symmetric apply auto[1]
    using transitive apply blast
    using monotonic apply blast
    done
qed


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


subsection \<open>Invariants\<close>
text \<open>As described in the paper\<close>

text \<open>For cc_list_invar we use ufa_invar\<close>

text \<open>for each representative i, UseList (i) is a list of input equations \<open>f(b\<^sub>1, b\<^sub>2)=b\<close>
such that i is the representative of \<open>b\<^sub>1\<close> or of \<open>b\<^sub>2\<close> (or of both).\<close>
definition use_list_invar :: "congruence_closure \<Rightarrow> bool"
  where
"use_list_invar cc = (\<forall> i < nr_vars cc . (\<forall> j < length ((use_list cc) ! i) . 
(cc_list cc) ! i = i \<longrightarrow> (\<exists> b\<^sub>1 b\<^sub>2 b .
use_list cc ! i ! j = (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and> 
(i = rep_of (cc_list cc) b\<^sub>1) \<or> i = rep_of (cc_list cc) b\<^sub>2)))"

text \<open>for all pairs of representatives (i, j), Lookup(i, j) is some input equation
\<open>f(a\<^sub>1, a\<^sub>2)=a\<close> such that i and j are the current respective representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close> whenever
such an equation exists. Otherwise, Lookup(i, j) is \<bottom>\<close>
definition lookup_invar :: "congruence_closure \<Rightarrow> bool"
  where
"lookup_invar cc = (\<forall> i < nr_vars cc . (\<forall> j < nr_vars cc . 
(cc_list cc) ! i = i \<and> (cc_list cc) ! j = j \<longrightarrow>
lookup cc ! i ! j = None \<or> (\<exists> a\<^sub>1 a\<^sub>2 a . lookup cc ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> a) \<and> 
rep_of (cc_list cc) a\<^sub>1 = i \<and> rep_of (cc_list cc) a\<^sub>2 = j)))"

definition representativeE :: "congruence_closure \<Rightarrow> equation set"
  where
"representativeE cc = {a \<approx> rep_of (cc_list cc) a |a.  a < nr_vars cc \<and> cc_list cc ! a \<noteq> a}
\<union> {F a' b' \<approx> rep_of (cc_list cc) c | a' b' c c\<^sub>1 c\<^sub>2 . a' < nr_vars cc \<and> b' < nr_vars cc \<and> c < nr_vars cc \<and>
                      cc_list cc ! a' = a' \<and> cc_list cc ! b' = b' \<and> lookup cc ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)}"

text \<open>TODO: 
Inv1: RepresentativeE is in standard form;
A set of equations E is in standard form if its equations are of the form a = b or
of the form f(a, b) = c whose (respective) left hand side terms a and f(a, b) only occur once
in E.\<close>
definition inv1 :: "congruence_closure \<Rightarrow> bool"
  where
"inv1 cc = True"

definition inv2 :: "congruence_closure \<Rightarrow> bool"
  where
"inv2 cc \<equiv> 
Congruence_Closure (representativeE cc) = Congruence_Closure (set (input cc))"

lemma cc_\<alpha>_eq_CC_representativeE: "cc_\<alpha> cc (s \<approx> t) = Congruence_Closure (representativeE cc) (s \<approx> t)"
  sorry

abbreviation cc_invar :: "congruence_closure \<Rightarrow> bool"
  where
"cc_invar cc \<equiv> use_list_invar cc \<and> lookup_invar cc \<and> inv1 cc \<and> inv2 cc"

lemma cc_invar_initial_cc: "cc_invar (initial_cc n)"
  sorry

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
  shows "length (lookup (propagate a cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  using set_lookup_preserves_length
  by auto

lemma propagate_preserves_length_proof_forest:
  assumes "propagate_dom (a, cc)" "length (proof_forest cc) = n "
  shows "length (proof_forest (propagate a cc)) = n"
  using assms proof(induction rule: propagate.pinduct)
  case (1 cc)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 pe xs l u t pf pfl ip)
  define a where "a = left pe"
  define b where "b = right pe"
  have "add_edge_dom (pf, a, b)"
    sorry
  with 2 add_edge_preserves_length a_def b_def show ?case 
    by (smt (verit) congruence_closure.select_convs(4) propagate.psimps(2))
qed

lemma propagate_preserves_length_pf_labels:
  assumes "propagate_dom (a, cc)" "length (pf_labels cc) = n"
  shows "length (pf_labels (propagate a cc)) = n"
  using assms proof(induction rule: propagate.pinduct)
  case (1 cc)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 pe xs l u t pf pfl ip)
  define a where "a = left pe"
  have "add_label_dom (pfl, pf, a, pe)"
    sorry
  with 2 add_label_preserves_length a_def propagate.psimps(2) show ?case 
    by (smt (verit) congruence_closure.select_convs(5) )
qed
thm "add_edge_rel.intros"
thm "rep_of_rel.intros"
lemma add_edge_rel: "rep_of_rel (l, x) (l, y) \<longleftrightarrow> add_edge_rel (l[y := y'], x, y) (l, y, y')" 
proof
  show "rep_of_rel (l, x) (l, y) \<Longrightarrow> add_edge_rel (l[y := y'], x, y) (l, y, y')"
    by (induction "(l, x)" "(l, y)" rule: rep_of_rel.induct)(auto simp add: add_edge_rel.intros)
next
  show "add_edge_rel (l[y := y'], x, y) (l, y, y') \<Longrightarrow> rep_of_rel (l, x) (l, y)"
    by (induction "(l[y := y'], x, y)" "(l, y, y')" rule: add_edge_rel.induct) (auto simp add: rep_of_rel.intros)
qed
thm add_edge.domintros

lemma "add_edge_dom (l, l ! i, x) \<Longrightarrow> add_edge_dom (l[i := y'], l ! i, x)"
proof(induction l "l!i" x arbitrary: x rule: add_edge.pinduct)
  case (1 pf e e')
  have "pf[i := y'] ! e = e \<Longrightarrow> add_edge_dom (pf[i := y'], e, x)" using add_edge.domintros by blast
  from 1 have *: "add_edge_dom (pf[pf ! i := e, i := y'], pf[pf ! i := e] ! i, e')" sorry
  have "pf[pf ! i := e] ! i = pf ! i" "pf[pf ! i := e, i := y'] = pf[i := y']" sorry
  with * show ?case 
    by argo
qed
lemma add_edge_dom: "ufa_invar l \<Longrightarrow> y < length l \<Longrightarrow> add_edge_dom (l, y, y')"
proof(induction arbitrary: y' rule: rep_of_induct)
  case (base i)
  then show ?case 
    using add_edge.domintros by blast
next
  case (step i)
  have "add_edge_dom (l[i := y'], l ! i, i)"
    sorry
  then show ?case 
    using add_edge.domintros by blast
qed
proof
lemma "ufa_invar pf \<Longrightarrow> a < length pf \<Longrightarrow> add_edge_dom (pf, a, b)"
proof(induction rule: rep_of_induct)
  case (base i)
  then show ?case using add_edge.psimps sorry
next
  case (step i)
  then show ?case sorry
qed



end