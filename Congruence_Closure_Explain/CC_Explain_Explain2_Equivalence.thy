theory CC_Explain_Explain2_Equivalence
  imports CC_Explain2_Correctness
begin

subsection \<open>Lemma about \<open>cc_explain2\<close> and append and subset\<close>

theorem cc_explain_aux2_app:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
    "\<forall> (a, b) \<in> set ys . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set ys . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
  shows "cc_explain_aux2 cc (xs @ ys) = cc_explain_aux2 cc xs \<union> cc_explain_aux2 cc ys"
  using assms proof(induction rule: cc_explain_aux2_induct)
  case (base cc)
  then show ?case using cc_explain_aux2.psimps by auto
next
  case (congruent cc a b xs c output1 pending1 output2 pending2)
  then have "\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc" 
"\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)" 
    by auto
  have vars_t: "nr_vars cc = length (cc_list cc_t)" 
    unfolding congruent(3) congruence_closure.truncate_def congruence_closure.select_convs 
    by simp
  then have " \<forall>(a, b)\<in>set (((a,b) # xs) @ ys). a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
" \<forall>(a, b)\<in>set (((a,b) # xs) @ ys). are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    using congruent unfolding congruent(3)[symmetric] by auto
  then have dom: "cc_explain_aux2_dom (cc, (((a,b) # xs) @ ys))"
    "cc_explain_aux2_dom (cc, ((a, b) # xs))"
    using cc_explain_aux2_domain congruent vars_t congruent(3) by blast+
  have in_bounds: "a < nr_vars cc" "b < nr_vars cc" 
    using congruent unfolding explain_list_invar_def same_length_invar_def by auto
  then have same_rep: "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    using congruent are_congruent_rep_of(2) by presburger
  then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" 
    "path (proof_forest cc) c p2 b"  
    using congruent in_bounds explain_along_path_lowest_common_ancestor
    by metis
  then have bounds1: "\<forall>(a, b)\<in>set pending1. a < nr_vars cc \<and> b < nr_vars cc"
    using explain_along_path2_pending_in_bounds congruent
    by metis
  have "\<forall>(a, b)\<in>set pending2. a < nr_vars cc \<and> b < nr_vars cc"
    using explain_along_path2_pending_in_bounds congruent 
    by (metis p(2))
  then have in_bounds2: "\<forall>a\<in>set (pending1 @ pending2 @ xs).
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall>a\<in>set ys.
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
    using bounds1 congruent congruent(3) vars_t by auto
  have "cc_explain_aux2 cc (((a, b) # xs) @ ys) = 
output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs @ ys)"
    using cc_explain_aux2_simp2 dom congruent
    by auto

  also have "... = output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs) 
\<union> cc_explain_aux2 cc ys"
    using congruent in_bounds2 by auto
  also have "... = cc_explain_aux2 cc ((a, b) # xs) \<union> cc_explain_aux2 cc ys"
    using cc_explain_aux2_simp2 dom(2) congruent
    by simp
  finally show ?case 
    by simp
qed

lemma cc_explain_aux2_union:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
  shows "cc_explain_aux2 cc xs = \<Union>{cc_explain_aux2 cc [x] |x. x \<in> set xs}"
using assms proof(induction xs)
  case Nil
  then show ?case 
    using cc_explain_aux2_simp1 by fastforce
next
  case (Cons a xs)
  then have "cc_explain_aux2 cc xs = \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set xs}" 
    by simp
  moreover have "cc_explain_aux2 cc (a # xs) = cc_explain_aux2 cc [a] \<union> cc_explain_aux2 cc xs"
"set (a # xs) = {a} \<union> set xs"
    using cc_explain_aux2_app[of cc_t "[a]" cc xs] Cons by auto
  moreover have "\<Union> {cc_explain_aux2 cc [x] |x. x \<in> set (a # xs)} = 
\<Union> {cc_explain_aux2 cc [x] |x. x \<in> {a}} \<union> \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set xs}"
    by fastforce
  moreover have "\<Union> {cc_explain_aux2 cc [x] |x. x \<in> {a}} = cc_explain_aux2 cc [a]"
    by blast
  ultimately show ?case using cc_explain_aux2_app 
    by auto
qed

theorem cc_explain_aux2_subset:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
    "\<forall> (a, b) \<in> set ys . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set ys . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "set xs \<subseteq> set ys"
  shows "cc_explain_aux2 cc xs \<subseteq> cc_explain_aux2 cc ys"
proof-
  have "cc_explain_aux2 cc xs = \<Union>{cc_explain_aux2 cc [x] |x. x \<in> set xs}"
    using cc_explain_aux2_union[OF assms(1-4)] by blast
  moreover have "cc_explain_aux2 cc ys = \<Union>{cc_explain_aux2 cc [y] |y. y \<in> set ys}"
    using cc_explain_aux2_union[OF assms(1,5,6,4)] assms by simp
  ultimately show ?thesis using assms(7) 
    by blast
qed

subsection \<open>Invariant of elements in the additional union find\<close>

text \<open>Invariant of \<open>explain_along_path\<close> that states that the recursive calls of explain are 
present in the total output\<close>

fun pending_equations_list :: "pending_equation option \<Rightarrow> (nat * nat) list"
  where
    "pending_equations_list None = []"
  | "pending_equations_list (Some (One a)) = []"
  | "pending_equations_list (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))) = [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)]"
  | "pending_equations_list (Some (Two a b)) = []"

text \<open>Invariant to show the equivalence of \<open>cc_explain\<close> and \<open>cc_explain2\<close>.\<close>

definition was_already_in_pending3 where
  "was_already_in_pending3 cc l a b xs \<equiv> 
    (((a, b) \<in> set xs) \<or> 
        (let c = lowest_common_ancestor (proof_forest cc) a b;
             (output1, pending1) = explain_along_path2 cc a c;
             (output2, pending2) = explain_along_path2 cc b c
         in ((output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
            \<and> set pending1 \<union> set pending2 \<subseteq> additional_uf_pairs_set l (pf_labels cc))
        ))"

definition equations_of_l_in_pending_invar3 where
  "equations_of_l_in_pending_invar3 cc l xs \<equiv>
  (\<forall> (a, b) \<in> additional_uf_pairs_set l (pf_labels cc).
      was_already_in_pending3 cc l a b xs
  )"

lemma equivalent_assumptions:
 assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
  shows "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
  using assms(1,4) apply simp
  using assms(2) 
  unfolding assms(4) congruence_closure.truncate_def congruence_closure.select_convs 
   apply blast
  using assms(3) congruence_closure.truncate_def by metis

lemma equivalent_assumptions2:
 assumes "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
      "cc = congruence_closure.truncate cc_t"
    shows
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
  using assms(1,2) 
  unfolding assms(3) congruence_closure.truncate_def congruence_closure.select_convs 
  by auto

lemma equations_of_l_in_pending_invar3_a_b:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output1, new_l, pending1)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
    "equations_of_l_in_pending_invar3 cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows 
    "was_already_in_pending3 cc new_new_l a b (pending1 @ pending2 @ xs)"
proof-
  obtain output12 pending12 output22 pending22 where
defs: "explain_along_path2 cc a c = (output12, pending12)"
         "explain_along_path2 cc b c = (output22, pending22)"
    by (metis old.prod.exhaust)
  have "output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
    using explain_along_path_explain_along_path2_output_subset' defs assms  
    by blast
  moreover have "set pending12 \<union> set pending22 \<subseteq>
additional_uf_pairs_set new_new_l (pf_labels cc)"
    using explain_along_path_explain_along_path2_pending_subset' defs assms 
    by blast
  ultimately show ?thesis unfolding was_already_in_pending3_def Let_def using defs 
    using assms(4) by force
qed

lemma changed_edge_in_pending:
assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
    "l ! n = n" "new_l ! n \<noteq> n" "n < nr_vars cc"
    "pf_labels cc ! n = (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b')))"
  shows  "(a\<^sub>1, b\<^sub>1) \<in> set pend \<and> (a\<^sub>2, b\<^sub>2) \<in> set pend" 
  using assms proof(induction rule: explain_along_path_induct)
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  then show ?case 
    by (metis nth_list_update_neq option.inject pending_equation.distinct(1))
next
  case (Two cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" new_l pend)
  then show ?case 
  proof(cases "l[rep_of l a := x] ! n = n")
    case True
    then have "(a\<^sub>1, b\<^sub>1) \<in> set pend \<and> (a\<^sub>2, b\<^sub>2) \<in> set pend" 
      using Two by blast
    then show ?thesis 
      by simp
  next
    case False
    then have "n = rep_of l a" using Two(21) 
      by (metis nth_list_update_neq)
    then have "a\<^sub>1 = x\<^sub>1" "a\<^sub>2 = x\<^sub>2" "b\<^sub>1 = y\<^sub>1" "b\<^sub>2 = y\<^sub>2" 
      using Two by auto
    then show ?thesis 
      using Two by simp
  qed
qed simp

lemma changed_edge_in_pending':
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output1, new_l, pend1)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pend2)"
    "a < nr_vars cc" "b < nr_vars cc"
    "are_congruent cc (a \<approx> b)"
    "l ! n = n" "new_new_l ! n \<noteq> n" "n < nr_vars cc"
    "pf_labels cc ! n = (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b')))"
  shows "(a\<^sub>1, b\<^sub>1) \<in> set (pend1 @ pend2) \<and> (a\<^sub>2, b\<^sub>2) \<in> set (pend1 @ pend2)" 
proof-
  obtain p1 p2 where paths: "path (proof_forest cc) c p1 a" 
"path (proof_forest cc) c p2 b" using assms lowest_common_ancestor_correct 
    unfolding proof_forest_invar_def same_length_invar_def  
    by (meson assms(1) explain_along_path_lowest_common_ancestor)
  then show ?thesis proof(cases "new_l ! n = n")
    case True
    have "explain_list_invar new_l (proof_forest cc)"
      using explain_list_invar_explain_along_path'' assms(1,2,3,4,6-8)
      by (metis length_explain_list_cc_list)
    with changed_edge_in_pending 
    have "(a\<^sub>1, b\<^sub>1) \<in> set pend2 \<and> (a\<^sub>2, b\<^sub>2) \<in> set pend2" 
      using paths True assms(1,10,11,12,5) by blast
    then show ?thesis by simp
  next
    case False
    with changed_edge_in_pending 
    have "(a\<^sub>1, b\<^sub>1) \<in> set pend1 \<and> (a\<^sub>2, b\<^sub>2) \<in> set pend1" 
      using paths assms(1,11,12,2,4,9) by blast
    then show ?thesis by auto
  qed
qed 

lemma equations_of_l_in_pending_invar3_invar:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output1, new_l, pending1)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
    "equations_of_l_in_pending_invar3 cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows 
    "equations_of_l_in_pending_invar3 cc new_new_l (pending1 @ pending2 @ xs)"
  unfolding equations_of_l_in_pending_invar3_def
proof(standard, standard)
  fix x x\<^sub>1 x\<^sub>2
  assume eq: "x \<in> additional_uf_pairs_set new_new_l (pf_labels cc)" "x = (x\<^sub>1, x\<^sub>2)" 
  then obtain n where n: "n < length new_new_l \<and> new_new_l ! n \<noteq> n"
    "x \<in> pending_pairs (pf_labels cc ! n)" unfolding additional_uf_pairs_set_def 
    by blast
  from n(2) obtain a\<^sub>1 a\<^sub>2  a' b\<^sub>1 b\<^sub>2 b' where 
pfl: "pf_labels cc ! n = (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b')))"
    "x = (a\<^sub>1, b\<^sub>1) \<or> x = (a\<^sub>2, b\<^sub>2)"
    using pending_pairs.cases 
    by (metis insert_iff memb_imp_not_empty pending_pairs.elims)
  have same_length: "length l = length new_new_l" 
    using assms explain_along_path_new_new_l_same_length 
    by (metis case_prodD list.set_intros(1) equivalent_assumptions(2))
  have valid_eqs: "a < nr_vars cc \<and> b < nr_vars cc"
    "are_congruent cc (a \<approx> b)" using equivalent_assumptions(2,3)[OF assms(1-4)] by auto
  show "was_already_in_pending3 cc new_new_l x\<^sub>1 x\<^sub>2 (pending1 @ pending2 @ xs)"
    unfolding was_already_in_pending3_def
  proof- 
    define c where "c = lowest_common_ancestor (proof_forest cc) x\<^sub>1 x\<^sub>2"
    obtain output12 pending12 output22 pending22 where 
      rec: "(output12, pending12) = explain_along_path2 cc x\<^sub>1 c"
      "(output22, pending22) = explain_along_path2 cc x\<^sub>2 c" 
      by (metis old.prod.exhaust)
    have "was_already_in_pending3 cc new_new_l a b (pending1 @ pending2 @ xs)"
      using equations_of_l_in_pending_invar3_a_b assms equivalent_assumptions[OF assms(1-4)] by simp
    have "(x\<^sub>1, x\<^sub>2) \<in> set (pending1 @ pending2 @ xs) \<or>
    (output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc) \<and>
        set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc))"
    proof(cases "l ! n = n")
      case True
      have "nr_vars cc = length new_new_l" 
        using same_length same_length_invar_def explain_list_invar_def 
        using assms(1,4,9) by presburger
      then have "(x\<^sub>1, x\<^sub>2) \<in> set (pending1 @ pending2)" 
        using changed_edge_in_pending'[OF _ assms(9,5)]
        using assms(1,6,7,5) True n pfl valid_eqs unfolding assms(4)[symmetric] 
        by (metis (no_types, lifting) eq(2) same_length valid_eqs(1) valid_eqs(2))
      then show ?thesis 
        by auto
    next
      case False
      then have a_b: "x \<in> additional_uf_pairs_set l (pf_labels cc)" using n same_length 
        unfolding additional_uf_pairs_set_def by auto
      then have 1: "was_already_in_pending3 cc l x\<^sub>1 x\<^sub>2 ((a, b) # xs)"
        using assms(2,3,7) n same_length eq equivalent_assumptions[OF assms(1-4)]
        unfolding equations_of_l_in_pending_invar3_def 
        by (metis assms(8) case_prodD equations_of_l_in_pending_invar3_def)
      then have 2: "((x\<^sub>1, x\<^sub>2) \<in> set ((a, b) # xs)) \<or> (output12 \<union> output22 \<subseteq> additional_uf_labels_set l (pf_labels cc) \<and>
      set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set l (pf_labels cc))"
        unfolding was_already_in_pending3_def Let_def using rec c_def by force
      have subset: "additional_uf_labels_set l (pf_labels cc) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
        "additional_uf_pairs_set l (pf_labels cc) \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
        using equivalent_assumptions[OF assms(1-4)] additional_uf_labels_set_explain_along_path' 
         apply (metis assms(5) assms(6) assms(7) assms(9) valid_eqs(1) valid_eqs(2))
        using equivalent_assumptions[OF assms(1-4)] additional_uf_pairs_set_explain_along_path'
        by (metis assms(5) assms(6) assms(7) assms(9) valid_eqs(1) valid_eqs(2))

      have append: "cc_explain_aux2 cc ((a, b) # xs) = cc_explain_aux2 cc [(a, b)] \<union> cc_explain_aux2 cc xs"
        using cc_explain_aux2_app[of cc_t "[(a, b)]" cc xs] assms(1,2,3,4)
        by auto
      have 0: "was_already_in_pending3 cc new_new_l a b (pending1 @ pending2 @ xs)"
        using equations_of_l_in_pending_invar3_a_b assms equivalent_assumptions[OF assms(1-4)] by blast
      consider "(x\<^sub>1, x\<^sub>2) = (a, b)" | "(x\<^sub>1, x\<^sub>2) \<in> set xs" | "output12 \<union> output22 \<subseteq> additional_uf_labels_set l (pf_labels cc) \<and>
      set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set l (pf_labels cc)"
        by (meson "2" set_ConsD)
      then show ?thesis proof(cases)
        case 1
        then show ?thesis using 0 unfolding was_already_in_pending3_def Let_def 
          using c_def local.rec(1) local.rec(2) by force
      next
        case 2
        then show ?thesis 
          by force
      next
        case 3
        then show ?thesis using subset 
          by (meson subset_trans)
      qed
    qed
    then show "(x\<^sub>1, x\<^sub>2) \<in> set (pending1 @ pending2 @ xs) \<or>
    (let c = lowest_common_ancestor (proof_forest cc) x\<^sub>1 x\<^sub>2; (output1, pending1) = explain_along_path2 cc x\<^sub>1 c;
         (output2, pending2) = explain_along_path2 cc x\<^sub>2 c
     in output1 \<union> output2 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc) \<and>
        set pending1 \<union> set pending2 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc))" 
      unfolding was_already_in_pending3_def Let_def 
      using c_def local.rec(1) local.rec(2) by force
  qed
qed

lemma equations_of_l_in_pending_invar3_initial:
"equations_of_l_in_pending_invar3 cc [0..<nr_vars cc] xs"
proof-
  have "additional_uf_pairs_set [0..<nr_vars cc] (pf_labels cc) = {}"
    unfolding additional_uf_pairs_set_def by auto
  then show ?thesis 
    unfolding equations_of_l_in_pending_invar3_def by blast
qed

subsection \<open>Equivalence proof of \<open>cc_explain2\<close> and \<open>cc_explain\<close>\<close>

lemma subseq_removeAll:
"subseq (removeAll x xs) xs"
  apply(induct xs)
  by auto

lemma subseq_notin_set:
  assumes "(a, b) \<notin> set xs"
    "subseq xs xs2"
  shows "subseq xs (removeAll (a, b) xs2)"
  using assms proof(induction xs2 arbitrary: xs)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs2)
  then show ?case proof(cases xs)
    case Nil
    then show ?thesis 
      by blast
  next
    case (Cons a list)
    then show ?thesis 
      by (metis Cons.prems removeAll_filter_not_eq removeAll_id subseq_filter)
  qed
qed

lemma cc_explain_aux2_removeAll:
   assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
  shows "cc_explain_aux2 cc ((a, b) # xs) = cc_explain_aux2 cc ((a, b) # removeAll (a, b) xs)"
proof-
  have same_set: "set ((a, b) # xs) = set ((a, b) # removeAll (a, b) xs)"
    by auto
  then have valid: "\<forall> (a, b) \<in> set ((a, b) # removeAll (a, b) xs) . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set ((a, b) # removeAll (a, b) xs) . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    using assms by auto
  have "cc_explain_aux2 cc ((a, b) # xs) =  \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set ((a, b) # xs)}"
    using cc_explain_aux2_union[OF assms] by blast
  also have "... = \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set ((a, b) # removeAll (a, b) xs)}"
    using same_set by blast
  also have "... = cc_explain_aux2 cc ((a, b) # removeAll (a, b) xs)"
    using cc_explain_aux2_union[OF assms(1) valid assms(4)] by argo 
  finally show ?thesis 
    by blast
qed

lemma cc_explain_aux_cc_explain_aux2_equivalence:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
    "\<forall> (a, b) \<in> set xs2 . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs2 . are_congruent cc (a \<approx> b)"
    "explain_list_invar l (proof_forest cc)" 
    "equations_of_l_in_pending_invar3 cc l xs" 
    "set xs2 \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)"
    "subseq xs xs2"
  shows "cc_explain_aux2 cc xs2 \<subseteq>
cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
  using assms proof (induction "timestamp_mset xs2 (proof_forest cc_t) (timestamps cc_t)" 
    arbitrary: xs xs2 l rule: less_induct)
  case 1: less
  then show ?case proof(cases xs2)
    case Nil
    then show ?thesis 
      using cc_explain_aux2_simp1 by blast
  next
    case (Cons ab xs2')
    obtain a b where ab: "ab = (a, b)" 
      by force
    define c where "c = lowest_common_ancestor (proof_forest cc) a b"
    obtain output12 output22 pending12 pending22 where 
      defs: "explain_along_path2 cc a c = (output12, pending12)"
      "explain_along_path2 cc b c = (output22, pending22)"
      by (metis old.prod.exhaust)
    have cc2: "\<lparr>cc_list = cc_list cc_t, use_list = use_list cc_t, lookup = lookup cc_t,
         pending = pending cc_t, proof_forest = proof_forest cc_t,
         pf_labels = pf_labels cc_t, input = input cc_t\<rparr> = cc"
      and cc3: "proof_forest cc_t = proof_forest cc"
      "cc_list cc_t = cc_list cc"
      unfolding 1(5) congruence_closure.truncate_def 
        congruence_closure.select_convs by auto
    note hyps = 1[unfolded congruence_closure.truncate_def 
        congruence_closure.select_convs cc2, unfolded cc3]
    have "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
      "ufa_invar (proof_forest cc)" 
      "a < length (proof_forest cc)" "b < length (proof_forest cc)"
      using  hyps(2,3,4,5,6,7) are_congruent_rep_of same_length_invar_def 
        ab Cons proof_forest_invar_def by auto
    then obtain p1 p2 where path: "path (proof_forest cc) c p1 a"
      "path (proof_forest cc) c p2 b"
      using c_def lowest_common_ancestor_correct  
      by presburger
    then have are_congruent: 
      "\<forall>a\<in>set (pending12 @ pending12 @ xs). case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)"
      using explain_along_path2_pending' hyps defs
      by fastforce
    have dom: "cc_explain_aux2_dom (cc, (a, b) # xs2')" using cc_explain_aux2_domain 
      using 1(2,5) hyps(6,7) Cons ab equivalent_assumptions2
      by blast 
    then have rec': "cc_explain_aux2 cc ((a, b) # xs2') =
output12 \<union> output22 \<union> cc_explain_aux2 cc (pending12 @ pending22 @ xs2')"
      using hyps c_def defs cc_explain_aux2_simp2 Cons ab 
      by auto
    then show ?thesis 
    proof(cases "xs = (a, b) # tl xs")
      case True
        (* The current pair that we consider is both in xs and in xs2 *)
      obtain output1 new_l pending1 output2 new_new_l pending2 where rec: 
        "explain_along_path cc l a c = (output1, new_l, pending1)"
        "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
        by (meson prod_cases3)
      have "cc_explain_aux_dom (cc, l, ((a, b) # tl xs))" 
        using cc_explain_aux_domain hyps True by simp
      then have cc_explain_aux: "cc_explain_aux cc l ((a, b) # tl xs) = output1 \<union> output2
\<union> cc_explain_aux cc new_new_l (pending1 @ pending2 @ tl xs)" 
        using cc_explain_aux_simp2 hyps rec c_def 
        by (metis \<open>a < length (proof_forest cc)\<close> \<open>b < length (proof_forest cc)\<close> \<open>rep_of (proof_forest cc) a = rep_of (proof_forest cc) b\<close> are_congruent_simp same_eq_classes_invar_not_divided)
      have eli: "explain_list_invar new_l (proof_forest cc)" using explain_list_invar_explain_along_path' 
        using hyps explain_along_path_domain local.rec(1) path(1) 
        by fast
      then have eli': "explain_list_invar new_new_l (proof_forest cc)" using explain_list_invar_explain_along_path' 
        using hyps explain_along_path_domain local.rec(2) path(2) 
        by fast
      have pend_in_bounds: "\<forall> (a, b) \<in> set pending12 . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set pending22 . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set pending12 . are_congruent cc (a \<approx> b)"
        "\<forall> (a, b) \<in> set pending22 . are_congruent cc (a \<approx> b)"
        "\<forall> (a, b) \<in> set pending1 . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set pending2 . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set pending1 . are_congruent cc (a \<approx> b)"
        "\<forall> (a, b) \<in> set pending2 . are_congruent cc (a \<approx> b)"
        using explain_along_path2_pending_in_bounds defs path explain_along_path2_pending_are_congruent
          explain_along_path_pending_in_bounds hyps 
               apply blast+
        using explain_along_path_pending_in_bounds path hyps 
           apply (simp add: local.rec eli)
        using explain_along_path_pending_in_bounds path hyps 
        using case_prodI2 eli local.rec(2) snd_conv apply simp
        using explain_along_path_pending_are_congruent  path hyps
        using local.rec(1) apply presburger
        using explain_along_path_pending_are_congruent  path hyps eli local.rec(2) by blast 
      then have in_bounds: "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2') . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2') . are_congruent cc (a \<approx> b)"
        "\<forall> (a, b) \<in> set (pending1 @ pending2 @ tl xs) . a < nr_vars cc \<and> b < nr_vars cc" 
        "\<forall> (a, b) \<in> set (pending1 @ pending2 @ tl xs) . are_congruent cc (a \<approx> b)" 
        "explain_list_invar new_new_l (proof_forest cc)" 
        using hyps Cons ab apply auto[2]
        using pend_in_bounds hyps apply (metis UnE in_set_tlD set_union_code)
        using pend_in_bounds hyps apply (metis UnE in_set_tlD set_union_code)
        using eli explain_list_invar_explain_along_path' 
        using hyps(2) explain_along_path_domain local.rec(2) path(2) by blast
      from eli have supset: "output12 \<supseteq> output1" "output22 \<supseteq> output2" 
        using explain_along_path_explain_along_path2_output_supset defs path hyps rec 
        by metis+
      have add_uf_new_l': "additional_uf_labels_set new_l (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> output1" 
        "additional_uf_labels_set new_new_l (pf_labels cc)
= additional_uf_labels_set new_l (pf_labels cc) \<union> output2"
        using additional_uf_labels_set_explain_along_path  
        using hyps local.rec path eli by auto
      then have add_uf_new_l: "additional_uf_labels_set new_new_l (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> output1 \<union> output2" 
        by simp
      have *: "output12 \<union> output22
    \<subseteq> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)" 
      proof-
        (* The output of explain2 is bigger than the output of explain, but
all the equations that are in explain2 are also present in new_new_l *)
        have "output12 \<subseteq> output1 \<union> additional_uf_labels_set l (pf_labels cc)" 
          "output22 \<subseteq> output2 \<union> additional_uf_labels_set new_l (pf_labels cc)" 
          "output1 \<union> additional_uf_labels_set l (pf_labels cc) = 
additional_uf_labels_set new_l (pf_labels cc)" 
          using add_uf_new_l' explain_along_path_explain_along_path2_output_subset hyps path(1) rec defs path 
            apply blast
          using add_uf_new_l' explain_along_path_explain_along_path2_output_subset path(2) hyps eli rec defs path 
           apply blast
          using add_uf_new_l' by blast
        then show ?thesis 
          using cc_explain_aux supset add_uf_new_l True by auto
      qed
      have "cc_explain_aux2 cc (pending12 @ pending22 @ xs2')
\<subseteq> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
        (* The pending list of explain2 is longer than the pending list of explain.
We can use the induction hypothesis to show the thesis. *)
      proof-
        have invar_eofip: "equations_of_l_in_pending_invar3 cc new_new_l (pending1 @ pending2 @ tl xs)"
          using equations_of_l_in_pending_invar3_invar[OF 1(2) _ _ 1(5) c_def rec _ 1(8), of "tl xs"] 1(9) True equivalent_assumptions2[OF 1(3,4,5)] 
          by force  
have pending_subset: "set pending12 \<subseteq> additional_uf_pairs_set new_l (pf_labels cc)"
            "set pending22 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
            using explain_along_path_explain_along_path2_pending_subset[OF _ path(1) defs(1)] 
            using hyps(2,8) local.rec(1) apply blast
            using explain_along_path_explain_along_path2_pending_subset[OF _ path(2) defs(2)] 
            using hyps(2) eli rec(2) by blast
          have pending_subseq: "subseq pending1 pending12" "subseq pending2 pending22" "subseq (tl xs) xs2'"
            using explain_along_path_explain_along_path2_pending_subseq hyps path(1) defs(1) rec(1) 
              apply blast
            using explain_along_path_explain_along_path2_pending_subseq hyps path(2) defs(2) eli rec(2) 
             apply blast 
            by (metis True ab hyps(11) local.Cons subseq_Cons2')
have aups_n_l: "additional_uf_pairs_set new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pending1" 
            using additional_uf_pairs_set_explain_along_path hyps local.rec(1) path(1) by blast
          then have aups_n_n_l: "additional_uf_pairs_set new_new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pending1 \<union> set pending2"
            using hyps additional_uf_pairs_set_explain_along_path eli rec(2) path(2) by presburger
        then show ?thesis
        proof(cases "(a, b) \<in> set (tl xs)")
          case True': True
          have "set xs = set (tl xs) \<union> {(a, b)}"
            "set ((a, b) # xs2) = set xs2 \<union> {(a, b)}" using hyps True 
             apply (metis Un_insert_right list.simps(15) sup_bot_right)
            by auto
          then have "set xs2 \<subseteq> set (tl xs) \<union> additional_uf_pairs_set l (pf_labels cc)" 
            using hyps(10) True True' by blast
          have "set xs2 \<subseteq> set (tl xs) \<union> additional_uf_pairs_set l (pf_labels cc)" 
            using True by (simp add: \<open>set xs2 \<subseteq> set (tl xs) \<union> additional_uf_pairs_set l (pf_labels cc)\<close>)
          then have subset: "set (pending12 @ pending22 @ xs2')
    \<subseteq> set (pending1 @ pending2 @ tl xs) \<union> additional_uf_pairs_set new_new_l (pf_labels cc)" 
            "subseq (pending1 @ pending2 @ tl xs) (pending12 @ pending22 @ xs2')" 
            using pending_subset aups_n_l aups_n_n_l Cons ab apply auto[1]
            using pending_subseq Cons ab by (metis list_emb_append_mono)
          have mset_less: "(timestamp_mset (pending12 @ pending22 @ xs2') (proof_forest cc) (timestamps cc_t))
     < (timestamp_mset xs2 (proof_forest cc) (timestamps cc_t))" 
            using recursive_calls_mset_less c_def 1(2,5) defs assms(4) cc3(1) unfolding 1(5) Cons ab
            by metis
          then have IH: "cc_explain_aux2 cc (pending12 @ pending22 @ xs2')
\<subseteq> cc_explain_aux cc new_new_l (pending1 @ pending2 @ tl xs) \<union> 
additional_uf_labels_set new_new_l (pf_labels cc)"
            using hyps(1)[OF mset_less hyps(2) in_bounds(3,4) _ in_bounds(1,2) eli' invar_eofip] 
              c_def subset defs in_bounds invar_eofip Cons ab mset_less by blast
          then show ?thesis 
            using IH True add_uf_new_l cc_explain_aux by auto
        next
          case False
          (* in this case "xs = (a, b) # tl xs" and "(a, b) \<notin> set (tl xs)" *)
          note True False
          define xs2_no_ab where "xs2_no_ab = removeAll (a, b) xs2'"
          have cc_explain_eq: "cc_explain_aux2 cc ((a, b) # xs2_no_ab) = cc_explain_aux2 cc ((a, b) # xs2')"
            using cc_explain_aux2_removeAll equivalent_assumptions2[OF hyps(6,7) 1(5)] 1(2,5)
            unfolding Cons ab xs2_no_ab_def by blast 
 have same_set: "set xs2 = set ((a, b) # xs2_no_ab)"
            unfolding xs2_no_ab_def Cons ab by auto
          then have in_bounds': "\<forall> (a, b) \<in> set ((a, b) # xs2_no_ab) . a < nr_vars cc \<and> b < nr_vars cc"
            "\<forall> (a, b) \<in> set ((a, b) # xs2_no_ab) . are_congruent cc (a \<approx> b)"
            "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2_no_ab) . a < nr_vars cc \<and> b < nr_vars cc"
            "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2_no_ab) . are_congruent cc (a \<approx> b)" 
            using hyps(6,7) pend_in_bounds by auto
have dom2: "cc_explain_aux2_dom (cc, ((a, b) # xs2_no_ab))" 
            using cc_explain_aux2_domain[OF 1(2) equivalent_assumptions2[OF in_bounds'(1,2) 1(5)]] 1(5) 
            by blast
          then have cc_explain_aux_no_ab: 
            "cc_explain_aux2 cc ((a, b) # xs2_no_ab) = output12 \<union> output22 \<union> 
cc_explain_aux2 cc (pending12 @ pending22 @ xs2_no_ab)"
            using cc_explain_aux2_simp2[OF dom2 c_def _ defs[symmetric]] hyps rec c_def 
              in_bounds'
              \<open>a < length (proof_forest cc)\<close> \<open>b < length (proof_forest cc)\<close> \<open>rep_of (proof_forest cc) a = rep_of (proof_forest cc) b\<close> are_congruent_simp same_eq_classes_invar_not_divided
            by presburger
          have cc_explain_eq2: "cc_explain_aux2 cc (pending12 @ pending22 @ xs2_no_ab) 
- output12 - output22
= cc_explain_aux2 cc (pending12 @ pending22 @ xs2') - output12 - output22" 
            using cc_explain_eq cc_explain_aux cc_explain_aux_no_ab rec' by auto
          have "subseq (tl xs) xs2_no_ab" 
            using False hyps(10,11) xs2_no_ab_def by (metis True ab local.Cons subseq_Cons2' subseq_notin_set)
          have "set xs2_no_ab = set xs2' - {(a, b)}" unfolding xs2_no_ab_def by simp
          have "(a, b) \<notin> set xs2_no_ab" unfolding xs2_no_ab_def by simp
           then have "set xs2_no_ab \<subseteq> set (tl xs) \<union> additional_uf_pairs_set l (pf_labels cc)" 
            using hyps(10) True 
            by (metis (no_types, lifting) Diff_insert2 Diff_insert_absorb Diff_subset_conv list.simps(15) same_set)
          then have subset: "set (pending12 @ pending22 @ xs2_no_ab)
    \<subseteq> set (pending1 @ pending2 @ tl xs) \<union> additional_uf_pairs_set new_new_l (pf_labels cc)" 
            "subseq (pending1 @ pending2 @ tl xs) (pending12 @ pending22 @ xs2')" 
            using pending_subset aups_n_l aups_n_n_l Cons ab apply auto[1]
            using pending_subseq Cons ab by (metis list_emb_append_mono)
          have mset_less: "(timestamp_mset (pending12 @ pending22 @ xs2') (proof_forest cc) (timestamps cc_t))
     < (timestamp_mset xs2 (proof_forest cc) (timestamps cc_t))" 
            using recursive_calls_mset_less c_def 1(2,5) defs unfolding 1(5) Cons ab 
            by (metis assms(4) cc3(1))
          then have "(timestamp_mset xs2_no_ab (proof_forest cc) (timestamps cc_t))
     < (timestamp_mset xs2' (proof_forest cc) (timestamps cc_t))
\<or> (timestamp_mset xs2_no_ab (proof_forest cc) (timestamps cc_t))
     = (timestamp_mset xs2' (proof_forest cc) (timestamps cc_t))" 
            using removeAll_timestamp_mset_less unfolding xs2_no_ab_def by simp
            then have "(timestamp_mset (pending12 @ pending22 @ xs2_no_ab) (proof_forest cc) (timestamps cc_t))
     < (timestamp_mset (pending12 @ pending22 @ xs2') (proof_forest cc) (timestamps cc_t))
\<or> (timestamp_mset (pending12 @ pending22 @ xs2_no_ab) (proof_forest cc) (timestamps cc_t))
     = (timestamp_mset (pending12 @ pending22 @ xs2') (proof_forest cc) (timestamps cc_t))"
              using append_timestamp_mset_less timestamp_mset_app by force
            then have **: "(timestamp_mset (pending12 @ pending22 @ xs2_no_ab) (proof_forest cc) (timestamps cc_t))
    < (timestamp_mset xs2 (proof_forest cc) (timestamps cc_t))" 
              using mset_less by fastforce
          have IH: "cc_explain_aux2 cc (pending12 @ pending22 @ xs2_no_ab)
\<subseteq> cc_explain_aux cc new_new_l (pending1 @ pending2 @ tl xs) \<union> 
additional_uf_labels_set new_new_l (pf_labels cc)"
            using hyps(1)[OF ** hyps(2) in_bounds(3,4) _ in_bounds'(3,4) eli' invar_eofip] c_def defs in_bounds(3-) invar_eofip in_bounds' 
              subset by (meson \<open>subseq (tl xs) xs2_no_ab\<close> list_emb_append_mono pending_subseq(1) pending_subseq(2))
          have "additional_uf_labels_set new_new_l (pf_labels cc) = 
additional_uf_labels_set l (pf_labels cc) \<union> output1 \<union> output2"
            using hyps c_def defs additional_uf_labels_set_explain_along_path' eli rec path add_uf_new_l by force
          then show ?thesis
            using IH True add_uf_new_l cc_explain_aux cc_explain_eq cc_explain_aux_no_ab 
             xs2_no_ab_def Cons ab cc_explain_eq2 * 
            by auto
        qed
      qed
      then show ?thesis using defs c_def rec' "*" 
        by (simp add: ab local.Cons)
    next
      case False
        (* The current pair that we consider is only in xs2, and not in xs.
We must prove that the added output and the added elements in pending 
are also present in explain xs.

The invariant equations_of_l_in_pending_invar states that all the edges
that are present in explain2 and not in explain were already in the pending list
sometime before this point.
*)
      then have subset: "set xs2' \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)"
        using hyps(10) Cons ab by auto
      then have union: "cc_explain_aux2 cc ((a, b) # xs2') =
cc_explain_aux2 cc [(a, b)] \<union> cc_explain_aux2 cc xs2'"
        using cc_explain_aux2_app[of cc_t "[(a, b)]" cc xs2', OF 1(2) _ _ 1(5)]
        using 1(5) equivalent_assumptions2[OF 1(6,7,5)] unfolding ab Cons by auto
      have subseq: "subseq xs xs2'" using hyps(11) Cons ab
        by (metis False list.collapse list_emb.simps subseq_Cons2_neq)
      have *: "cc_explain_aux2 cc ((a, b) # xs2') \<subseteq> 
      cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
      proof-
        show ?thesis
        proof(cases "(a, b) \<in> set xs")
          (* (a,b) is also present in the remaining list xs2 *)
          case True
          then have "(a, b) \<in> set xs2'" 
            by (meson subseq subseq_order.trans subseq_singleton_left)
          then have set_eq: "set ((a, b) # xs2') = set xs2'" 
            by auto
          have *: "(timestamp_mset xs2' (proof_forest cc) (timestamps cc_t))
     < (timestamp_mset xs2 (proof_forest cc) (timestamps cc_t))"
            using tl_list_mset_less[OF 1(2)] Cons ab equivalent_assumptions2[OF 1(6,7,5)] 
            using True assms(4) case_prodD cc3 hyps(3) by auto
          have "cc_explain_aux2 cc ((a, b) # xs2') = \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set ((a, b) # xs2')}"
            using cc_explain_aux2_union[of cc_t "((a, b) # xs2')" cc] 1(2,5)
              equivalent_assumptions2[OF 1(6,7,5)] unfolding Cons ab 
            by presburger
          also have "... = \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set xs2'}"
            using Cons ab False set_eq by auto
          also have "... = cc_explain_aux2 cc xs2'"
            using cc_explain_aux2_union[of cc_t "xs2'" cc] equivalent_assumptions2[OF _ _ 1(5)] 
              1(6,7) assms(1) assms(4) local.Cons by auto
          finally show ?thesis 
            using * hyps subseq subset unfolding Cons ab by auto
        next
          case False
            (* (a, b) is in the pairs set. We can use the invariant to prove that (a, b) \<in> explain2 xs*)
            (*or show that we can use here new_new_l instead of l, the one derived ba eap with the first element of
              xs. then use IH somehow idk or not*)
            (* make l bigger so i can show that its in there, like explain2 (pairs) \<union> l for the right hand side of equality \<subseteq>*)
          then have "(a, b) \<in> additional_uf_pairs_set l (pf_labels cc)"
            using hyps(10) ab Cons by force
          with hyps(9) have invariant: "output12 \<union> output22 \<subseteq> additional_uf_labels_set l (pf_labels cc) \<and>
         set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set l (pf_labels cc)" 
            unfolding equations_of_l_in_pending_invar3_def was_already_in_pending3_def Let_def
            using False defs c_def by force
          then have subset: "set (pending12 @ pending22 @ xs2') \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)" 
            using subset by auto
          have subseq_xs: "subseq xs (pending12 @ pending22 @ xs2')" 
            by (simp add: subseq subseq_drop_many)
          have *: "\<forall> (a, b) \<in> set pending12 . a < nr_vars cc \<and> b < nr_vars cc"
            "\<forall> (a, b) \<in> set pending22 . a < nr_vars cc \<and> b < nr_vars cc"
            "\<forall> (a, b) \<in> set pending12 . are_congruent cc (a \<approx> b)"
            "\<forall> (a, b) \<in> set pending22 . are_congruent cc (a \<approx> b)"
            using hyps(2) explain_along_path2_pending_in_bounds defs path explain_along_path2_pending_are_congruent
              explain_along_path_pending_in_bounds 
            by blast+
          then have in_bounds: "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2') . a < nr_vars cc \<and> b < nr_vars cc"
            "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2') . are_congruent cc (a \<approx> b)"
            using hyps(5,6,7,8) Cons by auto
          have mset_less: "(timestamp_mset (pending12 @ pending22 @ xs2') (proof_forest cc) (timestamps cc_t))
     < (timestamp_mset xs2 (proof_forest cc) (timestamps cc_t))" 
            using recursive_calls_mset_less c_def 1(2,5) defs unfolding 1(5) Cons ab 
            by (metis assms(4) cc3(1))
          then have IH: "cc_explain_aux2 cc (pending12 @ pending22 @ xs2') 
\<subseteq> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)" 
            using hyps(1) in_bounds defs hyps subseq_xs subset by blast
          then show ?thesis 
            using invariant rec' by auto
        qed
      qed
      then show ?thesis 
        using hyps Un_iff set_subset_Cons Cons ab by blast
    qed
  qed
qed

theorem cc_explain_cc_explain2_equivalence:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar_t cc_t" "valid_vars (a \<approx> b) (nr_vars cc)"
"cc = congruence_closure.truncate cc_t"
shows "cc_explain cc a b \<supseteq> cc_explain2 cc a b"
proof-
 have cc: "length (cc_list cc_t) = nr_vars cc" "cc_invar cc" using assms(2)
   unfolding congruence_closure.truncate_def congruence_closure.select_convs assms(4) by auto
  then have a_b: "\<forall>(a, b)\<in>set [(a, b)]. a < nr_vars cc \<and> b < nr_vars cc" 
"\<forall>(a, b)\<in>set [(a, b)]. are_congruent cc (a \<approx> b)"
    using assms valid_vars.simps by auto
  have *: "additional_uf_pairs_set [0..<nr_vars cc] (pf_labels cc) = {}"
"additional_uf_labels_set [0..<nr_vars cc] (pf_labels cc) = {}"
    unfolding additional_uf_pairs_set_def additional_uf_labels_set_def by auto
  have eli: "explain_list_invar [0..<nr_vars cc] (proof_forest cc)" 
    using cc explain_list_invar_initial unfolding same_length_invar_def 
    by metis
  with a_b show ?thesis 
    using cc_explain_aux_cc_explain_aux2_equivalence[OF assms(2) a_b assms(4) a_b eli equations_of_l_in_pending_invar3_initial] 
    * by blast
qed

subsection \<open>Correctness proof of \<open>cc_explain\<close>\<close>

theorem cc_explain_correctness:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar_t cc_t" "valid_vars (a \<approx> b) (nr_vars cc)"
"cc = congruence_closure.truncate cc_t"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain cc a b)"
proof- 
  have *: "(a \<approx> b) \<in> Congruence_Closure (cc_explain2 cc a b)"
    using cc_explain2_correctness cc_explain_cc_explain2_equivalence assms 
    by blast
  then have "cc_explain2 cc a b \<subseteq> cc_explain cc a b" 
    using cc_explain2_correctness cc_explain_cc_explain2_equivalence assms 
    by blast
  then show ?thesis using * 
    by (meson Congruence_Closure_monotonic in_mono)
qed

end