section \<open>Termination proof for congruence closure\<close>
theory CC_Termination
  imports CC_Invars
begin 

abbreviation root_set 
  where 
    "root_set l \<equiv> {i | i. i < length l \<and> l ! i = i}"

text \<open>To prove the termination of \<open>propagate\<close>, we show that the amount of equivalence classes 
decreases at each step of \<open>propagate\<close>.\<close>
definition nr_eq_classes :: "nat list \<Rightarrow> nat"
  where 
    "nr_eq_classes l = card (root_set l)"

lemma ufa_union_decreases_nr_eq_classes:
  assumes "ufa_invar l" "a < length l" 
    "rep_of l a \<noteq> rep_of l b"
  shows "nr_eq_classes (ufa_union l a b) = nr_eq_classes l - 1"
proof-
  have "rep_of l a \<in> root_set l"
    by (simp add: assms rep_of_less_length_l rep_of_root)
  have "root_set l = root_set (ufa_union l a b) \<union> {rep_of l a}"
    by (auto simp add: nth_list_update' assms rep_of_bound rep_of_min \<open>rep_of l a \<in> root_set l\<close>)
  moreover have "rep_of l a \<notin> root_set (ufa_union l a b)"
    using assms by auto
  ultimately show ?thesis unfolding nr_eq_classes_def
    by simp
qed

lemma nr_eq_classes_gt_0:
  assumes "ufa_invar l" "length l > 0"
  shows "nr_eq_classes l > 0"
proof(rule ccontr)
  assume "\<not> 0 < nr_eq_classes l"
  then have no_eq_classes: "nr_eq_classes l = 0"
    by blast
  then obtain i where i: "i < length l" 
    using assms by auto
  have "\<not> rep_of_dom (l, i)"
    using assms(1) i assms(2) proof(induction rule: rep_of_induct)
    case (base i)
    then have "l ! i \<noteq> i" 
      using no_eq_classes unfolding nr_eq_classes_def by simp
    then show ?case 
      using base by blast
  next
    case (step i)
    then show ?case 
      using rep_of_domain by auto
  qed
  then show "False" 
    using assms(1) i ufa_invarD(1) by auto
qed

lemma propagate_domain:
  assumes "cc_invar cc" "nr_vars cc > 0"
  shows "propagate_dom cc"
  using assms proof(induction "nr_eq_classes (cc_list cc)" arbitrary: cc)
  case 0
  then have "0 < nr_eq_classes (cc_list cc)" 
    using nr_eq_classes_gt_0 unfolding cc_list_invar_def by blast
  then show ?case
    using 0 by linarith
next
  case (Suc x)
  then show ?case 
  proof(cases "pending cc")
    case Nil
    then show ?thesis using propagate.domintros 
      by (metis congruence_closure.cases congruence_closure.select_convs(4))
  next
    case (Cons eq pe)
    define a b where a_b: "a = left eq" "b = right eq"
    obtain l u t pf pfl ip where 
      cc: "cc = \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      using Cons  by (metis congruence_closure.cases congruence_closure.select_convs(4))
    then show ?thesis proof(cases "rep_of l a = rep_of l b")
      case True
      let ?step = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      have "cc_invar ?step" 
        using Suc.prems(1) True a_b cc cc_invar_step2 by blast
      then have "propagate_dom ?step" using True Suc(1)
      proof (induction pe)
        case Nil
        then show ?case using propagate.domintros by blast
      next
        case (Cons eq2 pe2)
        then show ?case proof(cases "rep_of l (left eq2) = rep_of l (right eq2)")
          case True
          let ?step = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe2, proof_forest = pf, pf_labels = pfl,
        input = ip\<rparr>" 
          from True have *: "cc_invar ?step" using cc_invar_step2
            using Cons.prems(1) by blast
          with Cons have "propagate_dom ?step"
            by blast
          then show ?thesis using propagate.domintros Cons True by presburger
        next
          case False
          let ?step = "(propagate_step l u t pe2 pf pfl ip (left eq2) (right eq2) eq2)"
          have *: "cc_list ?step = ufa_union l (left eq2) (right eq2)" by (simp add: cc_list_loop)
          have "(left eq2) < length l" "ufa_invar l"  using Cons 
             apply (metis  pending_left_right_valid)
            using Suc unfolding cc_list_invar_def cc by simp
          then have "nr_eq_classes (ufa_union l (left eq2) (right eq2)) = nr_eq_classes l - 1" 
            using ufa_union_decreases_nr_eq_classes Suc * False by blast 
          then have "propagate_dom ?step"
            by (metis "*" Cons.prems(1) False Suc.hyps(1) Suc.hyps(2) Suc.prems(2) cc cc_invar_step congruence_closure.select_convs(1) diff_Suc_1 length_list_update)
          then show ?thesis using propagate.domintros 
            using False by presburger
        qed
      qed
      then show ?thesis using cc propagate.domintros True a_b by blast
    next
      case False
      let ?step = "(propagate_step l u t pe pf pfl ip a b eq)"
      have *: "cc_list ?step = ufa_union l a b" 
        by (simp add: cc_list_loop)
      have "a < length l" "ufa_invar l" using a_b Suc 
         apply (metis cc pending_left_right_valid)
        using Suc unfolding cc_list_invar_def cc by simp
      then have "nr_eq_classes (ufa_union l a b) = nr_eq_classes l - 1" 
        using ufa_union_decreases_nr_eq_classes Suc * False by blast 
      then have "propagate_dom ?step"
        using Suc False a_b cc cc_invar_step cc_list_loop by auto
      then show ?thesis using cc propagate.domintros False a_b by blast
    qed
  qed
qed

lemma valid_vars_imp_nr_vars_gt_0:
  assumes "valid_vars eq (nr_vars cc)"
  shows "nr_vars cc > 0"
proof(cases eq)
  case (Constants x11 x12)
  with assms have "x11 < nr_vars cc" 
    by simp
  then show ?thesis 
    by simp
next
  case (Function x21 x22 x23)
  with assms have "x21 < nr_vars cc" 
    by simp
  then show ?thesis 
    by simp
qed

corollary propagate_domain':
  assumes "cc_invar cc" "valid_vars eq (nr_vars cc)"
  shows "propagate_dom cc"
  using propagate_domain valid_vars_imp_nr_vars_gt_0 assms by blast

end