theory CC_Explain_Correctness_TODO
  imports CC_Explain_Correctness
begin 

section \<open>Lemmata about invariants\<close>

lemma cc_explain_correctness_invar':
  assumes "cc_explain_correctness_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "(\<forall> (a, b) \<in> set eqs . a < nr_vars cc \<and> b < nr_vars cc)"
    "(a, b) \<in> set eqs"
    "are_congruent cc (a \<approx> b)"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain_aux cc l eqs 
\<union> additional_uf_labels_set l (pf_labels cc))"
  using assms unfolding cc_explain_correctness_invar_def by blast

lemma length_explain_list_cc_list:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
  shows "length l = nr_vars cc"
  using assms unfolding explain_list_invar_def 
  by (simp add: same_length_invar_def)

lemma explain_list_rep_proof_forest:
  assumes "ufa_invar pf"
    "explain_list_invar l pf" 
    "a < length l" 
  shows "rep_of pf (rep_of l a) = rep_of pf a" 
proof-
  have "ufa_invar l" "a < length l" using assms unfolding explain_list_invar_def 
     apply blast using length_explain_list_cc_list assms 
    by presburger
  then show ?thesis 
    using assms proof(induction rule: rep_of_induct)
    case (base i)
    then show ?case 
      using rep_of_refl by presburger
  next
    case (step i)
    then have *: "rep_of pf (rep_of l (l ! i)) = rep_of pf (l ! i)"
      by (metis ufa_invarD(2))
    have "l ! i = pf ! i" using step.prems step(3) length_explain_list_cc_list
      unfolding explain_list_invar_def proof_forest_invar_def by simp
    then show ?case using step.prems * unfolding explain_list_invar_def proof_forest_invar_def
      by (metis rep_of_idx)
  qed
qed

section \<open>Lemmata about are_congruent\<close>

lemma are_congruent_step:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "are_congruent cc (a \<approx> b)" 
    "a < nr_vars cc" "b < nr_vars cc"
  shows "are_congruent cc (proof_forest cc ! rep_of l a \<approx> b)" 
proof-
  obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
  then have "rep_of cc_l a = rep_of cc_l b" using assms 
    by simp
  then have "rep_of pf a = rep_of pf b" 
    using assms unfolding cc same_eq_classes_invar_def same_length_invar_def
    by simp
  then have "rep_of pf (rep_of l a) = rep_of pf a" 
    using assms unfolding explain_list_invar_def 
    by (metis assms(2) cc congruence_closure.select_convs(5) explain_list_rep_proof_forest proof_forest_invar_def same_length_invar_def)
  then have "rep_of pf (pf ! rep_of l a) = rep_of pf a" 
    using cc by (metis assms(1) assms(2) assms(4) congruence_closure.select_convs(5) explain_list_invar_def proof_forest_invar_def rep_of_bound rep_of_idx same_length_invar_def)
  then have "rep_of cc_l (pf ! rep_of l a) = rep_of cc_l a" 
    using assms unfolding cc same_eq_classes_invar_def same_length_invar_def 
      congruence_closure.select_convs
    by (metis (mono_tags, lifting) congruence_closure.select_convs(5) explain_list_invar_def proof_forest_invar_def rep_of_less_length_l ufa_invarD(2))
  then show ?thesis 
    by (simp add: \<open>rep_of cc_l a = rep_of cc_l b\<close> cc)
qed

section \<open>Lemmata about lowest_common_ancestor\<close>

lemma lowest_common_ancestor_root:
  assumes "ufa_invar l" "i < length l" "l ! i = i" "k < length l"
    "rep_of l k = rep_of l i"
  shows "lowest_common_ancestor l i k = i"
proof-
  have "path_to_root l i = [i]" using assms 
    using path_to_root_correct path_to_root_has_length_1 by blast
  have "hd(path_to_root l k) = rep_of l k" 
    using assms(1) assms(4) hd_path path_to_root_correct by blast
  then obtain xs where "path_to_root l k = [rep_of l k] @ xs" using assms 
    by (metis append_Cons append_Nil list.sel(1) neq_Nil_conv path_not_empty path_to_root_correct)
  have "rep_of l k = i" 
    by (simp add: assms(3) assms(5) rep_of_refl)
  then show ?thesis 
    by (metis assms lowest_common_ancestor_correct path_no_root)
qed

lemma longest_common_prefix_delete_last:
  assumes "p = longest_common_prefix (xs @ [a]) ys"
    "last p \<noteq> a" "p \<noteq> []"
  shows "p = longest_common_prefix xs ys"
  using assms proof(induction "xs @ [a]" ys arbitrary: xs p rule: longest_common_prefix.induct)
  case (1 x xs' y ys)
  then show ?case 
  proof(cases "x = y")
    case True
    obtain short_xs where short_xs: "xs' = short_xs @ [a]" using 1 
      by (metis True append_butlast_last_id last_ConsR last_snoc longest_common_prefix.simps(1) longest_common_prefix.simps(2))
    let ?p = "longest_common_prefix (short_xs @ [a]) ys"
    show ?thesis 
    proof(cases "?p = []")
      case True
      then have "longest_common_prefix (xs @ [a]) (y # ys) = [x]"
        by (metis "1.hyps"(2) "1.prems"(1) "1.prems"(3) longest_common_prefix.simps(1) short_xs)
      then have "longest_common_prefix xs (y # ys) = x # longest_common_prefix short_xs ys" 
        using "1.hyps"(2) Cons_eq_appendI butlast_snoc list.discI longest_common_prefix.simps(1) short_xs by fastforce
      then show ?thesis 
      proof(cases "short_xs = []")
        case True
        then show ?thesis 
          by (simp add: "1.prems"(1) \<open>longest_common_prefix (xs @ [a]) (y # ys) = [x]\<close> \<open>longest_common_prefix xs (y # ys) = x # longest_common_prefix short_xs ys\<close>)
      next
        case False
        then have "ys = [] \<or> hd short_xs \<noteq> hd ys" 
          by (metis True append_is_Nil_conv hd_append2 list.sel(1) longest_common_prefix.simps(1) neq_Nil_conv)
        then show ?thesis 
          by (metis (no_types, lifting) "1.prems"(1) \<open>longest_common_prefix (xs @ [a]) (y # ys) = [x]\<close> \<open>longest_common_prefix xs (y # ys) = x # longest_common_prefix short_xs ys\<close> list.sel(1) longest_common_prefix.elims longest_common_prefix.simps(3))
      qed
    next
      case False
      have *: "last ?p \<noteq> a" 
      proof
        assume *: "last (longest_common_prefix (short_xs @ [a]) ys) = a"
        have "x # longest_common_prefix (short_xs @ [a]) ys = longest_common_prefix (xs @ [a]) (y # ys)" 
          using "1.hyps"(2) True short_xs by auto
        then have "last p = a" using * 1(3) False 
          by (metis last_ConsR)
        from short_xs have "?p = longest_common_prefix short_xs ys" using 1 True * False 
          using \<open>last p = a\<close> by force
        then show False 
          using "1.prems"(2) \<open>last p = a\<close> by blast
      qed
      then show ?thesis  using short_xs 1 False by force
    qed
  next
    case False
    then show ?thesis using 1 
      by (metis longest_common_prefix.simps(1))
  qed
qed auto

lemma lowest_common_ancestor_parent:
  assumes "ufa_invar l"
    "c = lowest_common_ancestor l a b"
    "a < length l" "b < length l"
    "c \<noteq> a" "rep_of l a = rep_of l b"
  shows "lowest_common_ancestor l a b =
lowest_common_ancestor l (l ! a) b"
proof-
  obtain p where "path l c p a" using lowest_common_ancestor_correct assms 
    by presburger
  then have "l ! a \<noteq> a"
    using assms(5) path_root by auto
  then have "path_to_root l a = path_to_root l (l ! a) @ [a]"
    by (metis assms(1) assms(3) path_snoc path_to_root_correct path_unique rep_of_idx ufa_invarD(2))
  have *: "hd (path_to_root l a) = hd (path_to_root l b)" 
    by (metis assms(1) assms(3) assms(4) assms(6) hd_path path_to_root_correct)
  have "last (longest_common_prefix (path_to_root l a) (path_to_root l b)) \<noteq> a"
    "longest_common_prefix (path_to_root l a) (path_to_root l b) \<noteq> []" 
    using assms apply simp
    using *
    by (metis Nil_is_append_conv \<open>path_to_root l a = path_to_root l (l ! a) @ [a]\<close> assms(1) assms(4) list.sel(1) longest_common_prefix.simps(1) neq_Nil_conv path_not_empty path_to_root_correct)
  then have "longest_common_prefix (path_to_root l a) (path_to_root l b)
= longest_common_prefix (path_to_root l (l ! a)) (path_to_root l b)"
    by (metis \<open>path_to_root l a = path_to_root l (l ! a) @ [a]\<close> longest_common_prefix_delete_last)
  then show ?thesis 
    by simp
qed

lemma lowest_common_ancestor_step:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "a < nr_vars cc" "b < nr_vars cc"
    "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    "rep_of l a \<noteq> rep_of l c"
  shows "c = lowest_common_ancestor (proof_forest cc)
     (proof_forest cc ! rep_of l a) b"
proof-
  have "ufa_invar (proof_forest cc)" "a < length (proof_forest cc)" 
    using assms unfolding proof_forest_invar_def explain_list_invar_def same_length_invar_def by auto
  then show ?thesis
    using assms proof(induction arbitrary: c rule: rep_of_induct)
    case (base i)
    have "b < length (proof_forest cc)" using length_explain_list_cc_list base 
      by (metis explain_list_invar_def)
    then have "c = i" using base lowest_common_ancestor_root unfolding explain_list_invar_def
      by presburger
    then show ?case 
      using base.prems(7) by auto
  next
    case (step i)
    let ?c = "lowest_common_ancestor (proof_forest cc) (proof_forest cc ! i) b"
    show ?case
    proof (cases "rep_of l (proof_forest cc ! i) = rep_of l ?c")
      case True
      then show ?thesis using step unfolding same_length_invar_def  
        by (metis (no_types, lifting) explain_list_invar_def lowest_common_ancestor_parent rep_of_refl rep_of_step)
    next
      case False
      have "proof_forest cc ! i < nr_vars cc" 
        "rep_of (proof_forest cc) (proof_forest cc ! i) = rep_of (proof_forest cc) b"
        using step unfolding proof_forest_invar_def ufa_invar_def same_length_invar_def 
         apply metis by (simp add: rep_of_idx step.hyps(1) step.hyps(2) step.prems(6))
      with step False have 1: "lowest_common_ancestor (proof_forest cc) (proof_forest cc ! i) b
 = lowest_common_ancestor (proof_forest cc)
     (proof_forest cc ! rep_of l (proof_forest cc ! i)) b" 
        by blast
      then have 2: "lowest_common_ancestor (proof_forest cc) (proof_forest cc ! rep_of l i) b
= lowest_common_ancestor (proof_forest cc)
     (proof_forest cc ! rep_of l (proof_forest cc ! i)) b" 
        using explain_list_invar_def rep_of_idx rep_of_refl step.hyps(2) step.prems(2) by fastforce
      have "ufa_invar (proof_forest cc)" "i < length (proof_forest cc)" "b < length (proof_forest cc)"
        using step unfolding proof_forest_invar_def 
          apply blast 
         apply (simp add: step.hyps(2)) using step unfolding same_length_invar_def 
        by presburger
      then have 3: "lowest_common_ancestor (proof_forest cc) (proof_forest cc ! i) b
= lowest_common_ancestor (proof_forest cc) i b" 
        by (metis lowest_common_ancestor_parent step.prems(3) step.prems(6) step.prems(7))
      with 1 2 step show ?thesis 
        by metis
    qed
  qed
qed

section \<open>Helper lemmata about \<open>explain_along_path\<close>\<close>

lemma are_congruent_implies_proof_forest_rep_of_eq:
  assumes  "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "are_congruent cc (a \<approx> b)"
    "a < length l" "b < length l"
  shows "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
  using assms unfolding same_eq_classes_invar_def explain_list_invar_def
  using are_congruent_rep_of(2) assms(1) same_length_invar_def by auto

theorem explain_list_invar_explain_along_path'':
  assumes 
    "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "a < length l" "b < length l"
    "are_congruent cc (a \<approx> b) \<or> rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "explain_list_invar new_l (proof_forest cc)"
proof-
  obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
  have a_b: "a < nr_vars cc" "b < nr_vars cc" using same_length_invar_def assms(1,2,3,4)
    by (metis (full_types) length_explain_list_cc_list)+
  obtain p where p: "path (proof_forest cc) c p a" 
    using lowest_common_ancestor_correct same_length_invar_def are_congruent_implies_proof_forest_rep_of_eq
      assms proof_forest_invar_def a_b by force
  then have "explain_along_path_dom (cc, l, a, c)"
    using explain_along_path_domain assms(1,2) by blast
  then show ?thesis using assms explain_list_invar_explain_along_path' p a_b
    by blast
qed

theorem explain_list_invar_explain_along_path''':
  assumes 
    "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "a < length l" "b < length l"
    "are_congruent cc (a \<approx> b) \<or> rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output, new_l, pend)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pend2)"
  shows "explain_list_invar new_new_l (proof_forest cc)"
proof-
  obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
  have a_b: "a < nr_vars cc" "b < nr_vars cc" using same_length_invar_def assms(1,2,3,4)
    by (metis (full_types) length_explain_list_cc_list)+
  obtain p where p: "path (proof_forest cc) c p b" 
    using lowest_common_ancestor_correct same_length_invar_def are_congruent_implies_proof_forest_rep_of_eq
      assms proof_forest_invar_def a_b by force
  have "explain_list_invar new_l (proof_forest cc)" 
    using explain_list_invar_explain_along_path'' a_b assms by blast
  then show ?thesis using assms explain_list_invar_explain_along_path' p a_b 
    using explain_along_path_domain by blast
qed

lemma explain_along_path_pending_in_bounds2:
  assumes "cc_invar cc" 
    "explain_list_invar l (proof_forest cc)"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "a < nr_vars cc" "b < nr_vars cc"
    "are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c" 
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
  shows "\<forall> (k, j) \<in> set (pending1 @ pending2 @ xs) . k < nr_vars cc \<and> j < nr_vars cc"
proof-
  have "ufa_invar (proof_forest cc)" "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    "a < length (proof_forest cc)" "b < length (proof_forest cc)"
    using assms unfolding proof_forest_invar_def apply blast
    using assms are_congruent_rep_of(2) apply presburger
    using assms unfolding same_length_invar_def apply argo
    using assms unfolding same_length_invar_def by argo
  then obtain p1 p2 where "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b"
    using lowest_common_ancestor_correct assms by presburger
  then have *: "\<forall> (k, j) \<in> set pending1 . k < nr_vars cc \<and> j < nr_vars cc"
    using assms explain_along_path_pending_in_bounds by (metis snd_conv)
  have "explain_list_invar new_l (proof_forest cc)" using explain_list_invar_explain_along_path' assms 
    by (metis \<open>path (proof_forest cc) c p1 a\<close> explain_along_path_domain)
  then have "\<forall> (k, j) \<in> set pending2 . k < nr_vars cc \<and> j < nr_vars cc" 
    using assms explain_along_path_pending_in_bounds 
    by (metis \<open>path (proof_forest cc) c p2 b\<close> snd_eqD)
  with * assms show ?thesis by fastforce
qed

lemma path_to_rep_of_l_a_explain_along_path_case_2:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "a < length l" "rep_of l a \<noteq> rep_of l c"
  obtains p where "path (proof_forest cc) c p (rep_of l a)"
proof-
  have "ufa_invar l" "ufa_invar (proof_forest cc)" "length l = length (proof_forest cc)"
    using assms(1,2) explain_list_invar_def proof_forest_invar_def by auto
  obtain p1 where "path l (rep_of l a) p1 a" 
    by (meson assms(2) assms(4) explain_list_invar_def path_to_rep_of)
  then have "path (proof_forest cc) (rep_of l a) p1 a" 
    using assms(2) explain_list_invar_paths by blast
  have "c \<notin> set p1" 
    by (metis \<open>path l (rep_of l a) p1 a\<close> \<open>ufa_invar l\<close> assms(5) in_set_conv_nth path_rep_of_neq_not_in_path)
  then show ?thesis using complement_of_subpath 
    using \<open>path (proof_forest cc) (rep_of l a) p1 a\<close> \<open>ufa_invar (proof_forest cc)\<close> assms(3) that by blast
qed

lemma path_to_parent_of_rep_of_l_a_explain_along_path_case_2:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "a < length l" "rep_of l a \<noteq> rep_of l c"
  obtains p where "path (proof_forest cc) c p (proof_forest cc ! rep_of l a)"
proof-
  obtain p1 where "path (proof_forest cc) c p1 (rep_of l a)"
    using assms path_to_rep_of_l_a_explain_along_path_case_2 by blast
  then have "c \<noteq> rep_of l a" using assms 
    using explain_list_invar_def rep_of_idem by force
  then show ?thesis using path_butlast 
    using \<open>path (proof_forest cc) c p1 (rep_of l a)\<close> that by blast
qed

lemma pf_labels_explain_along_path_case_2:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "a < length l" "rep_of l a \<noteq> rep_of l c"
  shows "(pf_labels cc) ! rep_of l a \<noteq> None"
proof-
  have "rep_of (proof_forest cc) a = rep_of (proof_forest cc) c"
    using assms by (simp add: path_rep_eq proof_forest_invar_def)
  obtain p1 where "path (proof_forest cc) c p1 (rep_of l a)" 
    using path_to_rep_of_l_a_explain_along_path_case_2 assms by blast
  then have "proof_forest cc ! rep_of l a \<noteq> rep_of l a" 
    by (metis assms(2) assms(4) assms(5) explain_list_invar_def path_root rep_of_idem)
  then show ?thesis using assms unfolding pf_labels_invar_def 
    by (metis \<open>path (proof_forest cc) c p1 (rep_of l a)\<close> option.discI path_nodes_lt_length_l)
qed

lemma rep_of_next_recursive_step_explain_along_path: 
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "a < length l"
  shows "rep_of (l[rep_of l a := proof_forest cc ! rep_of l a]) (proof_forest cc ! rep_of l a) =
    rep_of (l[rep_of l a := proof_forest cc ! rep_of l a]) a"
  using assms 
  by (smt (verit) explain_list_invar_def list_update_id path_to_root_correct proof_forest_invar_def rep_of_a_and_parent_rep_neq rep_of_bound rep_of_fun_upd' rep_of_fun_upd_aux2 rep_of_idem ufa_invarD(2))

lemma pf_labels_Two_valid:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p x"
    "rep_of l x \<noteq> rep_of l c"
    "the (pf_labels cc ! rep_of l x) = Two a' b'"
  obtains a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b where "pf_labels cc ! rep_of l x = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "a < length l" "b\<^sub>1 < length l" "b\<^sub>2 < length l" "b < length l"
proof-
  have "(proof_forest cc) ! rep_of l x \<noteq> rep_of l x" using assms unfolding explain_list_invar_def using path_to_rep_of_l_a_explain_along_path_case_2 
    by (metis (no_types, lifting) assms(2) list_update_id path_nodes_lt_length_l path_root rep_of_next_recursive_step_explain_along_path)
  then have "(pf_labels cc) ! rep_of l x \<noteq> None" using assms pf_labels_explain_along_path_case_2 
    using explain_list_invar_def path_nodes_lt_length_l by auto
  then obtain a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b where "pf_labels cc ! rep_of l x = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))"
    using assms
      valid_vars_pending_iff
    unfolding pf_labels_invar_def explain_list_invar_def 
    by (metis option.collapse path_nodes_lt_length_l pending_equation.distinct(1) rep_of_less_length_l)
  then have "valid_vars_pending (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)) (cc_list cc)" 
    using assms pf_labels_invar_def 
    by (metis \<open>proof_forest cc ! rep_of l x \<noteq> rep_of l x\<close> explain_list_invar_def option.sel path_nodes_lt_length_l rep_of_bound)
  then have "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (nr_vars cc)" "valid_vars (F b\<^sub>1 b\<^sub>2 \<approx> b) (nr_vars cc)" "nr_vars cc = length l"
    using assms explain_list_invar_def same_length_invar_def 
    by auto
  then have "a\<^sub>1 < length l"
    "b\<^sub>1 < length l"
    "a\<^sub>2 < length l"
    "b\<^sub>2 < length l"
    "b < length l"
    "a < length l"
    by auto
  then show ?thesis using assms
    using \<open>pf_labels cc ! rep_of l x = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))\<close> that by blast
qed

section \<open>Induction rule for \<open>explain_along_path\<close>.\<close>

thm explain_along_path.pinduct

lemma explain_along_path_induct[consumes 4, case_names base One Two]:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
    "(\<And>cc l a c p.
    explain_along_path_dom (cc, l, a, c) \<Longrightarrow>
    cc_invar cc \<Longrightarrow>
      explain_list_invar l (proof_forest cc) \<Longrightarrow>
      path (proof_forest cc) c p a \<Longrightarrow>
        rep_of l a = rep_of l c \<Longrightarrow>
        P cc l a c {} l [] p)" 
    "(\<And>cc l a c p1 p2 x x1 x11 x12 output new_l pend.
    explain_along_path_dom (cc, l, a, c) \<Longrightarrow>
    cc_invar cc \<Longrightarrow>
      explain_list_invar l (proof_forest cc) \<Longrightarrow>
      path (proof_forest cc) c p1 a \<Longrightarrow>
      path (proof_forest cc) c p2 x \<Longrightarrow>
      explain_list_invar (l[rep_of l a := x]) (proof_forest cc) \<Longrightarrow>
      explain_along_path cc (l[rep_of l a := x]) x c = (output, new_l, pend) \<Longrightarrow>
      rep_of l a \<noteq> rep_of l c \<Longrightarrow>
      x = proof_forest cc ! rep_of l a \<Longrightarrow> 
      pf_labels cc ! rep_of l a = Some (One x1) \<Longrightarrow>
      x11 < length l \<Longrightarrow> x12 < length l \<Longrightarrow> x1 = (x11 \<approx> x12) \<Longrightarrow>
      x < length l \<Longrightarrow>
      P cc (l[rep_of l a := x]) x c output new_l pend p2 \<Longrightarrow>
         P cc l a c ({x1} \<union> output) new_l pend p1)" 
    "(\<And>cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y output new_l pend.
      explain_along_path_dom (cc, l, a, c) \<Longrightarrow>
      cc_invar cc \<Longrightarrow>
      explain_list_invar l (proof_forest cc) \<Longrightarrow>
      path (proof_forest cc) c p1 a \<Longrightarrow>
      path (proof_forest cc) c p2 x \<Longrightarrow>
      explain_list_invar (l[rep_of l a := x]) (proof_forest cc) \<Longrightarrow>
       explain_along_path cc (l[rep_of l a := x]) x c = (output, new_l, pend) \<Longrightarrow>
        rep_of l a \<noteq> rep_of l c \<Longrightarrow>
        x = proof_forest cc ! rep_of l a \<Longrightarrow>
        pf_labels cc ! rep_of l a = Some (Two x21 x22) 
      \<Longrightarrow> x21 = (F x\<^sub>1 x\<^sub>2 \<approx> x') \<Longrightarrow> x22 = (F y\<^sub>1 y\<^sub>2 \<approx> y) \<Longrightarrow>
      x < length l \<Longrightarrow> x\<^sub>1 < length l \<Longrightarrow> x\<^sub>2 < length l 
      \<Longrightarrow> x < length l \<Longrightarrow> y\<^sub>1 < length l \<Longrightarrow> y\<^sub>2 < length l \<Longrightarrow> y < length l 
      \<Longrightarrow> P cc (l[rep_of l a := x]) x c output new_l pend p2 \<Longrightarrow>
      P cc l a c ({(F x\<^sub>1 x\<^sub>2 \<approx> x'), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> output) new_l ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pend) p1)"
  shows "P cc l a c output new_l pend p"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path_domain by fast
  then show ?thesis
    using assms proof(induction 
      arbitrary: "output" new_l pend p
      rule: explain_along_path.pinduct)
    case (1 cc l a c)
    then show ?case 
    proof(cases "rep_of l a = rep_of l c")
      case True
      with 1(7) have "output = {}" "new_l = l" "pend = []" using explain_along_path_simp1
        by simp+
      then show ?thesis 
        using 1(1,4,5,6,7,8) True by blast
    next
      case False
      define x where "x = (proof_forest cc) ! rep_of l a"
      have invar: "explain_list_invar (l[rep_of l a := x]) (proof_forest cc)" 
        "rep_of l a < length l"
        "explain_list_invar new_l (proof_forest cc)" 
        using explain_list_invar_step proof_forest_invar_def "1.prems" 
          apply (metis x_def explain_list_invar_def path_nodes_lt_length_l)
        using "1.prems" apply (metis  explain_list_invar_def path_nodes_lt_length_l rep_of_bound)
        using "1.prems" explain_list_invar_explain_along_path'' 
        by (smt (verit, del_insts) "1.hyps" explain_list_invar_def explain_list_invar_explain_along_path' length_explain_list_cc_list path_nodes_lt_length_l)
      obtain p2' where path_to_rep: "path (proof_forest cc) c p2' x" 
        using path_to_parent_of_rep_of_l_a_explain_along_path_case_2 "1.prems" x_def 
        by (metis (no_types, lifting) False explain_list_invar_def path_nodes_lt_length_l)
      then obtain p3' p4' where path_to_lca: "path (proof_forest cc) c p3' a"
        "path (proof_forest cc) c p4' x"
        using "1.prems" lowest_common_ancestor_correct explain_list_invar_def 
        using proof_forest_invar_def by blast
      have not_none: "(pf_labels cc) ! rep_of l a \<noteq> None" using pf_labels_explain_along_path_case_2 
        using "1.prems" False explain_list_invar_def path_nodes_lt_length_l by auto
      then obtain output_rec' new_l_rec' pending_rec' 
        where 
          rec': "explain_along_path cc (l[rep_of l a := x]) x c = (output_rec', new_l_rec', pending_rec')"
        by (metis prod_cases3)
      then have "x < length l" 
        using "1.prems"(2) explain_list_invar_def path_nodes_lt_length_l path_to_rep by auto
      show ?thesis
      proof(cases "the ((pf_labels cc) ! rep_of l a)")
        case (One x1)
        then have Some: "(pf_labels cc) ! rep_of l a = Some (One x1)"
          using not_none by auto
        then obtain x11 x12 where "x1 = (x11 \<approx> x12)" "x11 < length l" "x12 < length l" 
          using "1.prems" invar One not_none unfolding pf_labels_invar_def explain_list_invar_def 
          by (metis equation.exhaust same_length_invar_def valid_vars.simps(1) valid_vars_pending.simps(1) valid_vars_pending.simps(3))
        then have rec: "(output, new_l, pend) = ({x1} \<union> output_rec', new_l_rec', pending_rec')"
          using "1.hyps" "1.prems" False Some x_def explain_along_path_simp2 
          by (metis rec')
        have IH: "P cc (l[rep_of l a := x]) x c output_rec' new_l_rec' pending_rec' p4'" using 1(2) 
          using "1.prems"(1) False One assms(5-7) invar(1) path_to_lca(2) rec' x_def by blast
        then show ?thesis using 1(9) 
          using "1.hyps" "1.prems"(1,2,3) False Some \<open>x < length l\<close> \<open>x1 = (x11 \<approx> x12)\<close> \<open>x11 < length l\<close> \<open>x12 < length l\<close> invar(1) local.rec path_to_lca(2) rec' x_def by blast
      next
        case (Two x21 x22)
        then obtain x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y where Some: "(pf_labels cc) ! rep_of l a = 
Some (Two (F x\<^sub>1 x\<^sub>2 \<approx> x') (F y\<^sub>1 y\<^sub>2 \<approx> y))" "x\<^sub>1 < length l" "x\<^sub>2 < length l" "x' < length l"
          "y\<^sub>1 < length l" "y\<^sub>2 < length l"  "y < length l"
          using pf_labels_Two_valid "1.prems" False by metis
        then have x21x22: "x21 = (F x\<^sub>1 x\<^sub>2 \<approx> x')" "x22 = (F y\<^sub>1 y\<^sub>2 \<approx> y)" using Two by auto
        have rec: "(output, new_l, pend) 
= ({(F x\<^sub>1 x\<^sub>2 \<approx> x'), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> output_rec', new_l_rec', [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pending_rec')"
          using explain_along_path_simp3 False Some(1) rec' x_def 1(1,7) by auto
        have IH: "P cc (l[rep_of l a := x]) x c output_rec' new_l_rec' pending_rec' p2'" 
          using 1(3)[OF False x_def Two x21x22 "1.prems"(1) invar(1) path_to_rep rec' ]
          using assms(5-7) by blast
        then show ?thesis  
          using 1(1,4,5,6,10) Some path_to_rep invar(1) rec' False x_def \<open>x < length l\<close> rec by fastforce
      qed
    qed
  qed
qed

lemma explain_along_path_induct2[consumes 4, case_names base One Two]:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"

"rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
"c = lowest_common_ancestor (proof_forest cc) a b"
"a < length l" "b < length l"

"explain_along_path cc l a c = (output, new_l, pend)"
"(\<And>cc l a c p.
    explain_along_path_dom (cc, l, a, c) \<Longrightarrow>
    cc_invar cc \<Longrightarrow>
      explain_list_invar l (proof_forest cc) \<Longrightarrow>
      path (proof_forest cc) c p a \<Longrightarrow>
        rep_of l a = rep_of l c \<Longrightarrow>
        P cc l a c {} l [])" 
"(\<And>cc l a c p1 p2 x x1 x11 x12 output new_l pend.
    explain_along_path_dom (cc, l, a, c) \<Longrightarrow>
    cc_invar cc \<Longrightarrow>
      explain_list_invar l (proof_forest cc) \<Longrightarrow>
      path (proof_forest cc) c p1 a \<Longrightarrow>
      path (proof_forest cc) c p2 x \<Longrightarrow>
      explain_list_invar (l[rep_of l a := x]) (proof_forest cc) \<Longrightarrow>
      explain_along_path cc (l[rep_of l a := x]) x c = (output, new_l, pend) \<Longrightarrow>
      rep_of l a \<noteq> rep_of l c \<Longrightarrow>
      x = proof_forest cc ! rep_of l a \<Longrightarrow> 
      pf_labels cc ! rep_of l a = Some (One x1) \<Longrightarrow>
      x11 < length l \<Longrightarrow> x12 < length l \<Longrightarrow> x1 = (x11 \<approx> x12) \<Longrightarrow>
      x < length l \<Longrightarrow>
      P cc (l[rep_of l a := x]) x c output new_l pend \<Longrightarrow>
         P cc l a c ({x1} \<union> output) new_l pend)" 
"(\<And>cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y output new_l pend.
      explain_along_path_dom (cc, l, a, c) \<Longrightarrow>
      cc_invar cc \<Longrightarrow>
      explain_list_invar l (proof_forest cc) \<Longrightarrow>
      path (proof_forest cc) c p1 a \<Longrightarrow>
      path (proof_forest cc) c p2 x \<Longrightarrow>
      explain_list_invar (l[rep_of l a := x]) (proof_forest cc) \<Longrightarrow>
       explain_along_path cc (l[rep_of l a := x]) x c = (output, new_l, pend) \<Longrightarrow>
        rep_of l a \<noteq> rep_of l c \<Longrightarrow>
        x = proof_forest cc ! rep_of l a \<Longrightarrow>
        pf_labels cc ! rep_of l a = Some (Two x21 x22) 
      \<Longrightarrow> x21 = (F x\<^sub>1 x\<^sub>2 \<approx> x') \<Longrightarrow> x22 = (F y\<^sub>1 y\<^sub>2 \<approx> y) \<Longrightarrow>
      x < length l \<Longrightarrow> x\<^sub>1 < length l \<Longrightarrow> x\<^sub>2 < length l 
      \<Longrightarrow> x < length l \<Longrightarrow> y\<^sub>1 < length l \<Longrightarrow> y\<^sub>2 < length l \<Longrightarrow> y < length l 
      \<Longrightarrow> P cc (l[rep_of l a := x]) x c output new_l pend \<Longrightarrow>
      P cc l a c ({(F x\<^sub>1 x\<^sub>2 \<approx> x'), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> output) new_l ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pend))"
shows "P cc l a c output new_l pend"
proof-
  obtain p where p: "path (proof_forest cc) c p a" using assms(1-6) length_explain_list_cc_list lowest_common_ancestor_correct 
    unfolding proof_forest_invar_def same_length_invar_def
    by (metis explain_list_invar_def)
  show ?thesis 
    using explain_along_path_induct
      [OF assms(1,2) p assms(7), of "\<lambda> cc l a c output new_l pend p . P cc l a c output new_l pend"] 
    using assms(8-) by simp
qed

section \<open>Induction rule for \<open>cc_explain_aux\<close>.\<close>

thm cc_explain_aux.pinduct
thm cc_explain_aux_domain

lemma cc_explain_aux_induct[consumes 3, case_names base congruent not_congruent]:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "(\<And>cc l. cc_explain_aux_dom (cc, l, []) \<Longrightarrow>
cc_invar cc \<Longrightarrow> explain_list_invar l (proof_forest cc)
 \<Longrightarrow> P cc l [])" 
    "\<And>cc l a b xs c output1 new_l pending1 output2 new_new_l pending2.
    cc_explain_aux_dom (cc, l, (a, b) # xs) \<Longrightarrow>
 cc_invar cc \<Longrightarrow> explain_list_invar l (proof_forest cc) \<Longrightarrow>
(\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc) \<Longrightarrow>
 a < nr_vars cc \<Longrightarrow> b < nr_vars cc \<Longrightarrow>
        are_congruent cc (a \<approx> b) \<Longrightarrow>
       c = lowest_common_ancestor (proof_forest cc) a b \<Longrightarrow>
    (output1, new_l, pending1) = explain_along_path cc l a c \<Longrightarrow>
    (output2, new_new_l, pending2) = explain_along_path cc new_l b c
\<Longrightarrow> P cc new_new_l (pending1 @ pending2 @ xs)
\<Longrightarrow> P cc l ((a, b) # xs)" 
    "\<And>cc l a b xs.
    cc_explain_aux_dom (cc, l, (a, b) # xs) \<Longrightarrow>
cc_invar cc \<Longrightarrow> explain_list_invar l (proof_forest cc) \<Longrightarrow>
(\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc) \<Longrightarrow>
 a < nr_vars cc \<Longrightarrow> b < nr_vars cc \<Longrightarrow>
(\<not> are_congruent cc (a \<approx> b) \<Longrightarrow> P cc l xs
\<Longrightarrow> P cc l ((a, b) # xs))"
  shows "P cc l xs"
proof-
  have "cc_explain_aux_dom (cc, l, xs)" using assms(1-3) cc_explain_aux_domain 
    by blast
  then show ?thesis using assms proof(induction rule: cc_explain_aux.pinduct)
    case (2 cc l a b xs)
    have in_bounds: "a < nr_vars cc" "b < nr_vars cc" using 2(6) by auto 
    show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"
      obtain output1 new_l pending1 output2 new_new_l pending2
        where eap: "(output1, new_l, pending1) = explain_along_path cc l a c" 
          "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
        by (metis prod_cases3)
      have invar: "explain_list_invar new_new_l (proof_forest cc)"
        using explain_list_invar_explain_along_path''' 
        by (metis (mono_tags, lifting) "2.prems"(1) "2.prems"(2) True c_def eap(1) eap(2) in_bounds(1) in_bounds(2) length_explain_list_cc_list)
      have " \<forall>(k, j)\<in>set (pending1 @ pending2 @ xs). k < nr_vars cc \<and> j < nr_vars cc" 
        using explain_along_path_pending_in_bounds2[OF 2(4,5) _ _ _ True c_def] 
        by (metis "2.prems"(3) eap(1) eap(2) in_bounds(1) in_bounds(2) list.set_intros(2))
      then have "P cc new_new_l (pending1 @ pending2 @ xs)"
        using 2(2)[OF True c_def _ _ _ _ _ _ 2(4) invar] eap 2(4,5,6,7,8,9) 
        by blast
      then show ?thesis using "2.prems"(5)[OF 2(1,4,5)] 2(6) 
        using True c_def eap(1) eap(2) in_bounds(1) in_bounds(2) list.set_intros(2) by auto
    next
      case False
      have "P cc l xs" using 2(3)[OF False 2(4,5)] 2(6,7,8,9) 
        by fastforce
      then show ?thesis using "2.prems"(6)[OF 2(1,4,5)] using 2(6) False 
        by auto
    qed
  qed blast
qed

subsection \<open>Alternative definition for add_label.\<close>

function (domintros) add_label2 :: "pending_equation option list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> pending_equation \<Rightarrow> nat \<Rightarrow> pending_equation option list"
  where
    "add_label2 pfl pf e lbl e' = (if pf ! e = e then (pfl[e := Some lbl]) else add_label2 (pfl[e := Some lbl]) (pf[e := e']) (pf ! e) (the (pfl ! e)) e)"
  by pat_completeness auto

thm add_label_domain

lemma add_edge_dom_add_label2_dom:
  "add_edge_dom (l, y, y') \<Longrightarrow> add_label2_dom (pfl, l , y, lbl, y')"
  apply(induction arbitrary: pfl lbl rule: add_edge.pinduct)
  using add_label2.domintros by blast

lemma add_label2_dom_add_edge_dom:
  "add_label2_dom (pfl, l , y, lbl, y') \<Longrightarrow> add_edge_dom (l, y, y')"
  apply(induction rule: add_label2.pinduct)
  using add_edge.domintros by blast

lemma add_label2_domain: 
  assumes "ufa_invar l" "y < length l" "y' < length l" "rep_of l y \<noteq> rep_of l y'"
  shows "add_label2_dom (pfl, l, y, lbl, y')"
  using add_edge_dom_add_label2_dom add_label2_dom_add_edge_dom add_edge_domain assms 
  by blast

lemma add_label_add_label2_eq:
  assumes "ufa_invar pf" "e < length pf" "e' < length pf" "rep_of pf e \<noteq> rep_of pf e'"
  shows "add_label pfl pf e lbl = add_label2 pfl pf e lbl e'"
proof-
  have "add_edge_dom (pf, e, e')"
    using add_edge_domain assms by blast
  then show ?thesis
    using assms proof(induction arbitrary: pfl lbl rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case proof(cases "pf ! e = e")
      case True
      then show ?thesis using add_label.domintros add_label2.domintros
          add_label.psimps add_label2.psimps 
        by metis
    next
      case False
      have p: "path pf (pf ! e) [pf ! e, e] e" 
        by (simp add: "1.prems"(1) "1.prems"(2) False path.step single ufa_invarD(2))
      then have 
        "ufa_invar (pf[e := e'])"
        "pf ! e < length (pf[e := e'])"
        "e < length (pf[e := e'])"
        "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e"
        using "1.prems" apply (simp add: ufa_invar_fun_upd')
        using "1.prems" ufa_invar_def apply force
         apply (simp add: "1.prems"(2))
        using "1.prems" False rep_of_fun_upd_aux1 p 
        by (metis rep_of_fun_upd_aux2 rep_of_step single)
      with 1 False have IH: "add_label (pfl[e := Some lbl]) (pf[e := e']) (pf ! e) (the (pfl ! e)) =
    add_label2 (pfl[e := Some lbl]) (pf[e := e']) (pf ! e) (the (pfl ! e)) e"
        by blast
      have 2: "add_label pfl pf e lbl = add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e))"
        using False "1.prems" add_label_domain 
        by (simp add: add_label.psimps)
      have 3: "add_label2 pfl pf e lbl e' = add_label (pfl[e := Some lbl]) (pf[e := e']) (pf ! e) (the (pfl ! e))"
        by (simp add: "1.prems"(1) "1.prems"(2) "1.prems"(3) "1.prems"(4) False \<open>add_label (pfl[e := Some lbl]) (pf[e := e']) (pf ! e) (the (pfl ! e)) = add_label2 (pfl[e := Some lbl]) (pf[e := e']) (pf ! e) (the (pfl ! e)) e\<close> add_label2.psimps add_label2_domain)
      obtain pER where "path pf (rep_of pf e) pER e" 
        using "1.prems" path_to_root_correct by metis
      then have pER:  "path pf (rep_of pf e) (butlast pER) (pf ! e)" 
        by (metis "1.prems"(1) False path_butlast path_nodes_lt_length_l rep_of_min)
      have e_e': "e < length pf" "e' < length pf" using "1.prems"
        by metis+
      have "e \<notin> set (butlast pER)" 
        using "1.prems"(1) \<open>path pf (rep_of pf e) pER e\<close> path_remove_right by auto
      with pER have "add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)) = 
add_label (pfl[e := Some lbl]) (pf[e := e']) (pf ! e) (the (pfl ! e))"
        using "1.prems" \<open>path pf (rep_of pf e) pER e\<close> add_label_fun_upd e_e'
        by (simp add: rep_of_idx ufa_invarD(2))
      then show ?thesis using 2 3 IH by presburger
    qed
  qed
qed

lemma add_label_case_2_rep_of_neq:
  assumes "ufa_invar pf" "e < length pf" "e' < length pf" "rep_of pf e \<noteq> rep_of pf e'"
    "pf ! e \<noteq> e"
  shows "rep_of (pf[e := e']) e \<noteq> rep_of (pf[e := e']) (pf ! e)"
proof-
  obtain pER where "path pf (rep_of pf e) pER e" 
    using assms path_to_root_correct by metis
  with assms have pER:  "path pf (rep_of pf e) (butlast pER) (pf ! e)" 
    by (metis path_butlast rep_of_min)
  have e_e': "e < length pf" "e' < length pf" using assms
    by metis+
  have "e \<notin> set (butlast pER)" 
    using assms \<open>path pf (rep_of pf e) pER e\<close> path_remove_right by auto
  with assms have "path pf (pf ! e) [pf ! e, e] e" 
    by (simp add: path.step single ufa_invarD(2) e_e')
  have "rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)" 
    using rep_of_fun_upd_aux1 
    using assms \<open>path pf (pf ! e) [pf ! e, e] e\<close> by auto
  with assms have 5: "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
    by (metis \<open>e < length pf\<close> \<open>e' < length pf\<close> length_list_update nth_list_update_eq rep_of_fun_upd' rep_of_idx ufa_invar_fun_upd')
  from assms have 6: "ufa_invar (pf[e := e'])" 
    by (simp add: \<open>e' < length pf\<close> ufa_invar_fun_upd')
  then show ?thesis 
    by (metis "5")
qed


lemma add_label_simp2:
  assumes "ufa_invar pf" "e < length pf" "e' < length pf" "rep_of pf e \<noteq> rep_of pf e'"
    "pf ! e \<noteq> e"
  shows "add_label pfl pf e eq = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e))"
proof-
  have *: "ufa_invar (pf[e := e'])" "rep_of (pf[e := e']) e \<noteq> rep_of (pf[e := e']) (pf ! e)"
     apply (simp add: assms(1) assms(3) assms(4) ufa_invar_fun_upd')
    using assms add_label_case_2_rep_of_neq by blast
  have "add_label pfl pf e eq = add_label2 pfl pf e eq e'"
    using assms add_label_add_label2_eq by blast
  also have "... = add_label2 (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e)) e"
    using add_label2.psimps add_label2_domain assms by presburger
  also have "... = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e))"
    using assms add_label_add_label2_eq * by (metis length_list_update ufa_invarD(2))
  finally show ?thesis .
qed

section \<open>Abstraction of \<open>cc_explain_aux\<close>\<close>

text \<open>These definitions describe the set of all labels on a certain path \<open>p\<close>
of the proof forest, or on a certain subgraph \<open>l\<close> of the proof forest. \<close>

definition labels_on_path where
  "labels_on_path p pfl = \<Union>{pe_to_set (pfl ! x) | x. x \<in> set p}"

definition labels_in_uf where
  "labels_in_uf l pfl = \<Union>{pe_to_set (pfl ! x) | x. l ! x \<noteq> x}"

lemma labels_in_uf_same_rep:
  assumes "path l a p b"
  shows "labels_on_path (tl p) pfl \<subseteq> labels_in_uf l pfl"
proof
  fix eq 
  assume "eq \<in> labels_on_path (tl p) pfl"
  then obtain x where x: "x \<in> set (tl p)" "eq \<in> pe_to_set (pfl ! x)"
    unfolding labels_on_path_def by fast
  then have "l ! x \<noteq> x" using assms path_not_first_no_root 
    by (metis (no_types, lifting) in_set_conv_nth length_0_conv length_pos_if_in_set list.sel(3) not_gr_zero nth_Cons_0 path.cases)
  then show "eq \<in> labels_in_uf l pfl"
    using x unfolding labels_in_uf_def by blast
qed

subsection \<open>\<open>explain_along_path\<close> abstraction\<close>

text \<open>\<open>explain_along_path cc l a c\<close> returns the set of labels on the path 
from \<open>a\<close> to \<open>c\<close>, without the labels of edges that are present in the 
additional union-find \<open>l\<close>.\<close>

subsubsection \<open>Helper lemmata\<close>

lemma path_pf_same_rep:
  assumes "path pf a p b"
    "explain_list_invar l pf"
    "rep_of l a = rep_of l b"
    "ufa_invar pf"
  shows "path l a p b"
proof(cases "\<exists> pL . path l a pL b")
  case True
  then obtain pL where "path l a pL b" 
    by blast
  then have "path pf a pL b" 
    using explain_list_invar_paths assms by blast
  then show ?thesis 
    using \<open>path l a pL b\<close> assms(1) assms(4) path_unique by blast
next
  case False
  define lca where "lca = lowest_common_ancestor l a b"
  then obtain p1 p2 where "path l lca p1 a" "path l lca p2 b"
    using lca_def lowest_common_ancestor_correct assms 
    using explain_list_invar_def path_nodes_lt_length_l by fastforce
  then have "path pf lca p1 a" "path pf lca p2 b" 
    using assms(2) explain_list_invar_paths by blast+
  then have "path pf lca (p1 @ tl p) b" 
    using assms(1) path_concat1 by auto
  then show ?thesis 
    by (metis \<open>path l lca p2 b\<close> \<open>path pf lca p1 a\<close> \<open>path pf lca p2 b\<close> assms(1) assms(4) path_unique paths_iff)
qed

lemma labels_in_uf_fun_upd:
  assumes "x \<noteq> y" "y < length l"
  shows "labels_in_uf (l[y := x]) pfl = pe_to_set (pfl ! y) \<union> 
labels_in_uf l pfl"
proof
  show "labels_in_uf (l[y := x]) pfl \<subseteq> pe_to_set (pfl ! y) \<union> labels_in_uf l pfl"
  proof
    fix xa
    assume 1: "xa \<in> labels_in_uf (l[y := x]) pfl"
    then obtain ixa where 2: "xa \<in> pe_to_set (pfl ! ixa)" "l[y := x] ! ixa \<noteq> ixa"
      unfolding labels_in_uf_def by auto
    have "l[y := x] ! y \<noteq> y" using assms 
      by auto
    then show "xa \<in> pe_to_set (pfl ! y) \<union> labels_in_uf l pfl" 
      unfolding labels_in_uf_def using assms 1 2 
      by (smt (verit) UnI1 UnI2 Union_iff mem_Collect_eq nth_list_update)
  qed
next show "pe_to_set (pfl ! y) \<union> labels_in_uf l pfl \<subseteq> labels_in_uf (l[y := x]) pfl"
  proof
    fix xa
    assume "xa \<in> pe_to_set (pfl ! y) \<union> labels_in_uf l pfl"
    then show "xa \<in> labels_in_uf (l[y := x]) pfl"
    proof
      assume "xa \<in> pe_to_set (pfl ! y)"
      then show ?thesis unfolding labels_in_uf_def 
        by (smt (verit) Union_iff assms(1) assms(2) mem_Collect_eq nth_list_update_eq)
    next
      assume "xa \<in> labels_in_uf l pfl"
      then show "xa \<in> labels_in_uf (l[y := x]) pfl"
        unfolding labels_in_uf_def  
        by (smt (verit) Union_iff assms(1) assms(2) mem_Collect_eq nth_list_update_eq nth_list_update_neq)
    qed
  qed
qed

lemma labels_in_uf_fun_upd1:
  assumes "x \<noteq> y" "y < length l"
  shows "labels_in_uf (l[y := x]) pfl - pe_to_set (pfl ! y) \<subseteq> 
labels_in_uf l pfl"
proof
  fix xa
  assume 1: "xa \<in> labels_in_uf (l[y := x]) pfl - pe_to_set (pfl ! y)"
  then obtain ixa where 2: "xa \<in> pe_to_set (pfl ! ixa)" "l[y := x] ! ixa \<noteq> ixa"
    unfolding labels_in_uf_def by auto
  then have 3: "ixa \<noteq> y" 
    using "1" by blast
  have "l[y := x] ! y \<noteq> y" using assms 
    by auto
  then show "xa \<in> labels_in_uf l pfl" 
    unfolding labels_in_uf_def using assms 1 2 3 by auto
qed

lemma labels_in_uf_fun_upd2:
  assumes "x \<noteq> y" "y < length l"
  shows "labels_in_uf (l[y := x]) pfl \<supseteq> 
labels_in_uf l pfl"
proof
  fix xa
  assume "xa \<in> labels_in_uf l pfl"
  then obtain ixa where  "l ! ixa \<noteq> ixa" 
    "xa \<in> pe_to_set (pfl ! ixa)" 
    unfolding labels_in_uf_def 
    by blast
  then have "l[y := x] ! ixa \<noteq> ixa" 
    by (metis assms(1) assms(2) nth_list_update_eq nth_list_update_neq)
  then show "xa \<in> labels_in_uf (l[y := x]) pfl" unfolding labels_in_uf_def 
    using \<open>xa \<in> pe_to_set (pfl ! ixa)\<close> by blast
qed

lemma path_from_rep_of_l_a_to_a_eap_case2:
  assumes "path pf c p1 a"
    "path pf c p2 x"
    "x = pf ! rep_of l a"
    "explain_list_invar l pf"
    "ufa_invar pf"
    "x \<noteq> rep_of l a"
  shows "path l (rep_of l a) (drop (length p2) p1) a"
    "take (length p2) p1 = p2"
proof-
  have "path l (rep_of l a) (path_to_root l a) a"
    using assms path_to_root_correct explain_list_invar_def path_nodes_lt_length_l by auto
  then have p1: "path pf (rep_of l a) (path_to_root l a) a" 
    using assms explain_list_invar_paths by blast
  have "rep_of l a < length pf" 
    by (metis \<open>path l (rep_of l a) (path_to_root l a) a\<close> assms(4) explain_list_invar_def path_nodes_lt_length_l)
  then have p2: "path pf x [x, rep_of l a] (rep_of l a)"
    using assms explain_list_invar_def path_nodes_lt_length_l path.intros by force
  then have p3: "path pf x (x # path_to_root l a) a"
    using \<open>rep_of l a < length pf\<close> assms(3) assms(5) assms(6) p1 path.step ufa_invarD(2) by blast
  then have p4: "path pf c (p2 @ path_to_root l a) a" 
    using assms path_concat1 by (metis list.sel(3))
  then have "p1 = p2 @ path_to_root l a" 
    using assms(1) assms(5) path_unique by auto
  then show "path l (rep_of l a) (drop (length p2) p1) a"
    "take (length p2) p1 = p2" 
     apply (simp add: \<open>path l (rep_of l a) (path_to_root l a) a\<close>)
    by (simp add: \<open>p1 = p2 @ path_to_root l a\<close>)
qed

lemma labels_on_path_eap_case2:
  assumes "path pf c p1 a"
    "path pf c p2 x"
    "a < length l"
    "x = pf ! rep_of l a"
    "explain_list_invar l pf"
    "rep_of l a \<noteq> rep_of l c"
    "ufa_invar pf"
  shows "labels_on_path (tl p1) pfl - labels_on_path (tl p2) pfl
\<subseteq> labels_in_uf (l[rep_of l a := x]) pfl \<union> pe_to_set (pfl ! rep_of l a)"
proof
  fix xa 
  assume xa: "xa \<in> labels_on_path (tl p1) pfl - labels_on_path (tl p2) pfl"
  then obtain ixa where ixa: "ixa \<in> set (tl p1)" "xa \<in> pe_to_set (pfl ! ixa)"
    unfolding labels_on_path_def by blast
  with xa have "ixa \<notin> set (tl p2)" unfolding labels_on_path_def 
    by blast
  then show "xa \<in> labels_in_uf (l[rep_of l a := x]) pfl \<union>
                pe_to_set (pfl ! rep_of l a)"
  proof(cases "ixa = rep_of l a")
    case True
    then show ?thesis 
      using ixa unfolding labels_on_path_def by simp
  next
    case False
    define p3 where "p3 = drop (length p2) p1"
    have x_neq_rep_a: "x \<noteq> rep_of l a" using assms unfolding proof_forest_invar_def assms(4) 
      by (metis explain_list_invar_def path_root rep_of_idem)
    then have "p2 @ p3 = p1" "path l (rep_of l a) p3 a" 
      using path_from_rep_of_l_a_to_a_eap_case2 assms p3_def 
       apply (metis append_take_drop_id)
      using path_from_rep_of_l_a_to_a_eap_case2 assms p3_def x_neq_rep_a by metis
    have "ixa \<in> set p3" 
      by (metis Un_iff \<open>ixa \<notin> set (tl p2)\<close> \<open>p2 @ p3 = p1\<close> in_set_tlD ixa(1) self_append_conv2 set_union_code tl_append2)
    have "l ! ixa \<noteq> ixa" using assms ixa 
      by (metis (no_types, lifting) False \<open>ixa \<in> set p3\<close> \<open>path l (rep_of l a) p3 a\<close> explain_list_invar_def in_set_conv_nth path_rep_of_neq_not_in_path rep_of_refl)
    have "l[rep_of l a := x] ! ixa \<noteq> ixa"
      using False \<open>l ! ixa \<noteq> ixa\<close> by auto
    then show ?thesis 
      using ixa xa labels_in_uf_def by auto
  qed
qed

subsubsection \<open>Abstraction\<close>

lemma explain_along_path_is_labels_on_path:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "output \<supseteq> labels_on_path (tl p) (pf_labels cc) - labels_in_uf l (pf_labels cc)"
  using assms proof(induction rule: explain_along_path_induct)
  case (base cc l a c p)
  have "path l c p a" 
    using path_pf_same_rep base unfolding proof_forest_invar_def by metis
  then have "x \<in> set (tl p) \<Longrightarrow> l ! x \<noteq> x" for x 
    using base.hyps(3) explain_list_invar_def path_contains_no_root by auto
  then have "\<Union> {pe_to_set (pf_labels cc ! x) |x. x \<in> set (tl p)} \<subseteq>
    \<Union> {pe_to_set (pf_labels cc ! x) |x. l ! x \<noteq> x}" 
    by auto
  then show ?case unfolding labels_on_path_def labels_in_uf_def 
    by auto
next
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  have *: "labels_in_uf (l[rep_of l a := x]) (pf_labels cc) = 
pe_to_set (pf_labels cc ! rep_of l a) \<union> labels_in_uf l (pf_labels cc)"
    using labels_in_uf_fun_upd One.hyps
    by (metis (no_types, lifting) explain_list_invar_def path_nodes_lt_length_l path_root rep_of_bound rep_of_iff)
  have ***: "labels_on_path (tl p1) (pf_labels cc) - labels_on_path (tl p2) (pf_labels cc)
\<subseteq> labels_in_uf (l[rep_of l a := x]) (pf_labels cc) \<union> {x1}" 
    using labels_on_path_eap_case2 "*" One.hyps proof_forest_invar_def 
    by (smt (verit) explain_list_invar_def path_nodes_lt_length_l pe_to_set.simps(2))
  show ?case using One *  ***
    by auto
next
  case (Two cc l a c p1 p2 x x21 x22 x21a x22a x23 x21b x22b x23a "output" new_l pend)
  have *: "labels_in_uf (l[rep_of l a := x]) (pf_labels cc) = 
pe_to_set (pf_labels cc ! rep_of l a) \<union> labels_in_uf l (pf_labels cc)"
    using labels_in_uf_fun_upd Two.hyps
    by (metis (no_types, lifting) explain_list_invar_def path_nodes_lt_length_l path_root rep_of_bound rep_of_iff)
  have ***: "labels_on_path (tl p1) (pf_labels cc) - labels_on_path (tl p2) (pf_labels cc)
\<subseteq> labels_in_uf (l[rep_of l a := x]) (pf_labels cc) \<union> {x21, x22}" 
    using labels_on_path_eap_case2 "*" Two.hyps proof_forest_invar_def 
    by (smt (verit, del_insts) explain_list_invar_def path_nodes_lt_length_l pe_to_set.simps(3))
  show ?case using Two *  ***
    by auto
qed

section \<open>New invariant that describes a well-formed proof forest.\<close>

lemma additional_uf_labels_set_fun_upd:
  assumes "e < length pf" "length pf = length pfl" "e \<noteq> e'"
    "pf ! e \<noteq> e \<or> pfl ! e = None"
  shows "additional_uf_labels_set pf pfl \<union> pe_to_set eq
= additional_uf_labels_set (pf[e := e']) (pfl[e := eq]) \<union> pe_to_set (pfl ! e)"
proof
  show "additional_uf_labels_set pf pfl \<union> pe_to_set eq
    \<subseteq> additional_uf_labels_set (pf[e := e']) (pfl[e := eq]) \<union> pe_to_set (pfl ! e)"
  proof
    fix x assume "x \<in> additional_uf_labels_set pf pfl \<union> pe_to_set eq"
    then show "x \<in> additional_uf_labels_set (pf[e := e']) (pfl[e := eq]) \<union> pe_to_set (pfl ! e)"
    proof
      assume "x \<in> additional_uf_labels_set pf pfl"
      then obtain i where i: "x \<in> pe_to_set (pfl ! i)" "i < length pf \<and> pf ! i \<noteq> i"
        unfolding additional_uf_labels_set_def by blast
      then show ?thesis
      proof(cases "i = e")
        case True
        then show ?thesis 
          using i(1) by auto
      next
        case False
        then show ?thesis unfolding additional_uf_labels_set_def using i 
          using Union_iff length_list_update by fastforce
      qed
    next
      assume "x \<in> pe_to_set eq"
      show ?thesis 
        unfolding additional_uf_labels_set_def using assms 
        using Un_def Union_iff \<open>x \<in> pe_to_set eq\<close> length_list_update mem_Collect_eq nth_list_update  
        by fastforce
    qed
  qed
next
  show "additional_uf_labels_set (pf[e := e']) (pfl[e := eq]) \<union> pe_to_set (pfl ! e)
    \<subseteq> additional_uf_labels_set pf pfl \<union> pe_to_set eq"
  proof
    fix x assume "x \<in> additional_uf_labels_set (pf[e := e']) (pfl[e := eq]) \<union> pe_to_set (pfl ! e)"
    then show "x \<in> additional_uf_labels_set pf pfl \<union> pe_to_set eq"
    proof
      assume "x \<in> additional_uf_labels_set (pf[e := e']) (pfl[e := eq])"
      then obtain i where i: "x \<in> pe_to_set (pfl[e := eq] ! i)" "i < length (pf[e := e']) \<and> pf[e := e'] ! i \<noteq> i"
        unfolding additional_uf_labels_set_def by blast
      then show ?thesis 
      proof(cases "i = e")
        case True
        then show ?thesis using additional_uf_labels_set_def assms i(1) by fastforce
      next
        case False
        then show ?thesis 
          unfolding additional_uf_labels_set_def using i by auto
      qed
    next
      assume "x \<in> pe_to_set (pfl ! e)"
      then show ?thesis unfolding additional_uf_labels_set_def
        using \<open>x \<in> pe_to_set (pfl ! e)\<close> assms by auto
    qed
  qed
qed

lemma additional_uf_labels_set_add_label:
  assumes "ufa_invar pf" "e < length pf" "e' < length pf" 
    "rep_of pf e \<noteq> rep_of pf e'"
    "valid_labels_invar pfl pf cc_l"
    "length pf = length pfl"
    "length cc_l = length pf"
    "(\<exists> c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d . (eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)))
\<and> ((e' = c \<and> e = d) \<or> (e = c \<and> e' = d))
\<and> c < length cc_l \<and> d < length cc_l
\<and> valid_vars_pending eq cc_l
)"
  shows "additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq)
= additional_uf_labels_set (add_edge pf e e') (add_label pfl pf e eq)"
proof-
  have "add_edge_dom (pf, e, e')" 
    using add_edge_domain assms proof_forest_invar_def by auto
  then show ?thesis 
    using assms proof(induction 
      arbitrary: pfl eq rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case proof(cases "pf ! e = e")
      case True
      then have 2: "pfl ! e = None" using "1.prems"(1,2,5)
        unfolding pf_labels_invar_def by simp
      have add_edge: "add_edge pf e e' = pf[e := e']" 
        using True 1 add_edge.psimps add_edge_domain by presburger
      have add_label: "add_label pfl pf e eq = pfl[e:= Some eq]"
        using True 1 add_label.psimps by (metis add_label.domintros)
      then show ?thesis 
        using additional_uf_labels_set_fun_upd[OF "1.prems"(2)] "1.prems"(3,6) 2
        by (metis "1.prems"(4) add_edge add_label pe_to_set.simps(1) sup_bot_right)
    next
      case False
      have add_edge: "add_edge pf e e' = add_edge (pf[e := e']) (pf ! e) e" 
        using False 1 add_edge.psimps add_edge_domain by presburger
      have add_label: "add_label pfl pf e eq = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e))"
        using False 1(1-6) add_label.psimps add_label_add_label2_eq 
        by (metis add_label_simp2)
      from add_label_case_2_rep_of_neq have rep_rec: "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e"
        using "1.prems"(1-7) False  
        by metis
      have invar_pfl_e: "\<exists>c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d.
       (the (pfl ! e) = One (c \<approx> d) \<or>
        the (pfl ! e) = Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)) \<and>
       (e = c \<and> pf ! e = d \<or> pf ! e = c \<and> e = d) \<and>
       c < length cc_l \<and>
       d < length cc_l \<and>
       valid_vars_pending (the (pfl ! e)) cc_l"
        using "1.prems"(1,2,5,7) False option.sel by auto
      have "ufa_invar (pf[e := e'])"
        "pf ! e < length (pf[e := e'])"
        "valid_labels_invar (pfl[e := Some eq]) (pf[e := e']) cc_l"
          apply (simp add: "1.prems"(1,3,4) ufa_invar_fun_upd')
        using "1.prems"(1,2) ufa_invar_def apply auto[1]
        using valid_labels_invar_fun_upd "1.prems" by presburger
      with 1(2)[OF False this(1-2) _ rep_rec this(3) _ _ invar_pfl_e] have IH: "additional_uf_labels_set (pf[e := e']) (pfl[e := Some eq]) \<union>
    pe_to_set (Some (the (pfl ! e))) =
    additional_uf_labels_set (add_edge (pf[e := e']) (pf ! e) e)
     (add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e)
       (the (pfl ! e)))" 
        by (metis "1.prems"(2) "1.prems"(6) "1.prems"(7) length_list_update)
      then show ?thesis using "1.prems"(2) "1.prems"(5) "1.prems"(6) False \<open>valid_labels_invar (pfl[e := Some eq]) (pf[e := e']) cc_l\<close> add_edge add_label additional_uf_labels_set_fun_upd length_list_update nth_list_update_eq option.collapse option.distinct(1)
        by metis
    qed
  qed
qed

abbreviation well_formed_pf :: "nat list \<Rightarrow> pending_equation option list \<Rightarrow> equation set \<Rightarrow> bool"
  where
    "well_formed_pf pf pfl other_set \<equiv>
  (\<forall> a b . a < length pf \<longrightarrow> b < length pf \<longrightarrow>
    rep_of pf a = rep_of pf b \<longrightarrow> 
(a \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> other_set))"

text \<open>Invariant for the proof forest in the congruence closure data structure.\<close>
definition well_formed_pf_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "well_formed_pf_invar cc \<equiv>
well_formed_pf (proof_forest cc) (pf_labels cc) {}"

subsection \<open>Proof that \<open>well_formed_pf_invar\<close> is an invariant of \<open>merge\<close>.\<close>

theorem well_formed_pf_invar_initial_cc: "well_formed_pf_invar (initial_cc n)"
  unfolding well_formed_pf_invar_def
proof(standard, standard, standard, standard, standard)
  fix a b
  assume *: "a < length (proof_forest (initial_cc n))"
    "b < length (proof_forest (initial_cc n))"
    "rep_of (proof_forest (initial_cc n)) a = rep_of (proof_forest (initial_cc n)) b"
  then have "[0..<n] ! a = a" "[0..<n] ! b = b" 
    by auto
  then have "a = b" unfolding congruence_closure.select_convs using * 
    using rep_of_refl by fastforce
  then show "(a \<approx> b)
           \<in> Congruence_Closure
               (additional_uf_labels_set (proof_forest (initial_cc n)) (pf_labels (initial_cc n)) \<union>
                {})" by blast
qed

lemma a_eq_b_in_CC_of_eq:
  assumes "well_formed_pf pf pfl {}"
    "(\<exists> c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d . (eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)))
\<and> ((b = c \<and> a = d) \<or> (a = c \<and> b = d))
\<and> c < length cc_l \<and> d < length cc_l
\<and> c\<^sub>1 < length cc_l \<and> c\<^sub>2 < length cc_l
\<and> d\<^sub>1 < length cc_l \<and> d\<^sub>2 < length cc_l
\<and> valid_vars_pending eq cc_l
\<and> rep_of pf c\<^sub>1 = rep_of pf d\<^sub>1
\<and> rep_of pf c\<^sub>2 = rep_of pf d\<^sub>2
)"
    "length cc_l = length pf"
  shows "(a \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
proof-
  obtain c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d where 
    eq: "eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d))"
    "(b = c \<and> a = d) \<or> (a = c \<and> b = d)"
    "c < length cc_l" "d < length cc_l"
    "valid_vars_pending eq cc_l" 
    "rep_of pf c\<^sub>1 = rep_of pf d\<^sub>1"
    "rep_of pf c\<^sub>2 = rep_of pf d\<^sub>2"
    using assms by blast
  from eq(1) show ?thesis 
  proof
    assume "eq = (One (c \<approx> d))"
    then show ?thesis
      using assms by auto
  next
    assume *: "eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d))"
    then have **: "(c\<^sub>1 \<approx> d\<^sub>1) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
      "(c\<^sub>2 \<approx> d\<^sub>2) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
      using assms eq 
      by (metis Congruence_Closure_split_rule equation.inject(2) pending_equation.distinct(1) pending_equation.inject(2) sup_bot.right_neutral)+
    then have ***: "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
      "(F d\<^sub>1 d\<^sub>2 \<approx> d) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
      using * by auto
    then have "(F d\<^sub>1 d\<^sub>2 \<approx> c) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
      using ** by blast
    then show ?thesis 
      using "***"(2) eq(2) by blast
  qed
qed

lemma well_formed_pf_add_edge:
  assumes 
    "well_formed_pf pf pfl {}"
    "ufa_invar pf" "a < length pf" "b < length pf"
    "rep_of pf a \<noteq> rep_of pf b"
    "valid_labels_invar pfl pf cc_l"
    "length pf = length pfl"
    "length cc_l = length pf"
    "(\<exists> c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d . (eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)))
\<and> ((b = c \<and> a = d) \<or> (a = c \<and> b = d))
\<and> c < length cc_l \<and> d < length cc_l
\<and> c\<^sub>1 < length cc_l \<and> c\<^sub>2 < length cc_l
\<and> d\<^sub>1 < length cc_l \<and> d\<^sub>2 < length cc_l
\<and> valid_vars_pending eq cc_l
\<and> rep_of pf c\<^sub>1 = rep_of pf d\<^sub>1
\<and> rep_of pf c\<^sub>2 = rep_of pf d\<^sub>2
)"
  shows "well_formed_pf (add_edge pf a b) (add_label pfl pf a eq) {}"
proof(standard, standard, standard, standard, standard)
  fix a' b'
  assume prems: "a' < length (add_edge pf a b)"
    "b' < length (add_edge pf a b)"
    "rep_of (add_edge pf a b) a' = rep_of (add_edge pf a b) b'"
  from additional_uf_labels_set_add_label[OF assms(2-8)]
  have *: "additional_uf_labels_set (add_edge pf a b) (add_label pfl pf a eq) 
= additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq)" 
    using assms(9) by blast
  have **: "(a \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
    using a_eq_b_in_CC_of_eq assms by simp
  then show "(a' \<approx> b')
       \<in> Congruence_Closure
           (additional_uf_labels_set (add_edge pf a b) (add_label pfl pf a eq) \<union> {})"
  proof(cases "rep_of pf a' = rep_of pf b'")
    case True
    then show ?thesis using assms(1-5) * prems 
      by (simp add: Congruence_Closure_split_rule add_edge_preserves_length')
  next
    case False
    then have "(rep_of pf a' = rep_of pf a \<and> rep_of pf b' = rep_of pf b) 
        \<or> 
      (rep_of pf b' = rep_of pf a \<and> rep_of pf a' = rep_of pf b)"
      by (metis add_edge_preserves_length' assms(2-5) prems rep_of_add_edge_aux)
    then show ?thesis 
    proof
      assume "rep_of pf a' = rep_of pf a \<and> rep_of pf b' = rep_of pf b"
      then have "(a' \<approx> a) \<in> Congruence_Closure (additional_uf_labels_set pf pfl)"
        "(b' \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set pf pfl)"
        using add_edge_preserves_length' assms(1-5) prems by force+
      then have "(a' \<approx> a) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
        "(b' \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
        by (auto simp add: Congruence_Closure_split_rule)
      then show ?thesis using * ** 
        by (metis Congruence_Closure.symmetric Congruence_Closure.transitive1 boolean_algebra.disj_zero_right)
    next 
      assume "rep_of pf b' = rep_of pf a \<and> rep_of pf a' = rep_of pf b"
      then have "(a' \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set pf pfl)"
        "(b' \<approx> a) \<in> Congruence_Closure (additional_uf_labels_set pf pfl)"
        using add_edge_preserves_length' assms(1-5) prems by force+
      then have "(a' \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
        "(b' \<approx> a) \<in> Congruence_Closure (additional_uf_labels_set pf pfl \<union> pe_to_set (Some eq))"
        by (auto simp add: Congruence_Closure_split_rule)
      then show ?thesis using * ** 
        by (metis Congruence_Closure.symmetric Congruence_Closure.transitive1 boolean_algebra.disj_zero_right)
    qed
  qed
qed

lemma well_formed_pf_invar_loop: 
  assumes 
    "well_formed_pf_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "well_formed_pf_invar ?base") 
  shows "well_formed_pf_invar (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)" 
  using assms apply(induction rep_b u_a 
      "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
  unfolding well_formed_pf_invar_def by auto

lemma well_formed_pf_invar_step:
  assumes "ufa_invar pf" "a < length l" "b < length l" 
    "a = left eq" "b = right eq"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pf_labels_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "well_formed_pf_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "length l = length pf" "length l = length pfl"
    "rep_of pf a \<noteq> rep_of pf b"
    "ufa_invar l"  
    "same_eq_classes_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "well_formed_pf_invar (propagate_step l u t pe pf pfl ip a b eq)"
proof-
  have "(\<exists> c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d . (eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)))
\<and> ((b = c \<and> a = d) \<or> (a = c \<and> b = d))
\<and> c < length l \<and> d < length l
\<and> c\<^sub>1 < length l \<and> c\<^sub>2 < length l
\<and> d\<^sub>1 < length l \<and> d\<^sub>2 < length l
\<and> valid_vars_pending eq l
\<and> rep_of l c\<^sub>1 = rep_of l d\<^sub>1
\<and> rep_of l c\<^sub>2 = rep_of l d\<^sub>2
)"
    using assms(6,13) valid_vars_pending_iff 
    using assms(4,5) left.simps pending_invar_Cons right.simps(1) right.simps(2) by fastforce
  then have *: "(\<exists> c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d . (eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)))
\<and> ((b = c \<and> a = d) \<or> (a = c \<and> b = d))
\<and> c < length l \<and> d < length l
\<and> c\<^sub>1 < length l \<and> c\<^sub>2 < length l
\<and> d\<^sub>1 < length l \<and> d\<^sub>2 < length l
\<and> valid_vars_pending eq l
\<and> rep_of pf c\<^sub>1 = rep_of pf d\<^sub>1
\<and> rep_of pf c\<^sub>2 = rep_of pf d\<^sub>2
)"    
    using assms(13) same_eq_classes_invar_divided assms(9) 
    by (smt (verit, del_insts))
  have "well_formed_pf (add_edge pf a b) (add_label pfl pf a eq) {}"
    using well_formed_pf_add_edge[OF _ _ _ _ _ _ _ _ *] using assms(1-12)
    unfolding well_formed_pf_invar_def pf_labels_invar_def congruence_closure.select_convs 
    by simp
  then show ?thesis using well_formed_pf_invar_def 
    using pf_labels_invar_loop proof_forest_loop by auto
qed

lemma well_formed_pf_invar_propagate: 
  assumes "propagate_dom cc" "well_formed_pf_invar cc" "cc_invar cc"
  shows "well_formed_pf_invar (propagate cc)"
  using assms proof(induction cc rule: propagate.pinduct)
  case (2 l u t eq pe pf pfl ip)
  then show ?case 
  proof(cases "rep_of l (left eq) = rep_of l (right eq)")
    case True
    let ?step = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    have cc_invar: "cc_invar ?step"
      using "2.prems" cc_invar_step2 True by blast
    have "well_formed_pf_invar ?step"
      using 2(4) unfolding well_formed_pf_invar_def by simp
    then show ?thesis 
      using 2(2) "2.hyps" True cc_invar propagate.psimps(2) by presburger
  next
    case False
    let ?step = "(propagate_step l u t pe pf pfl ip (left eq) (right eq) eq)"
    have invar: "ufa_invar l" using "2.prems" unfolding cc_list_invar_def by simp
    have left_right: "left eq < length l" "right eq < length l" 
      using "2.prems" pending_left_right_valid by auto
    have cc_invar: "cc_invar ?step"
      using "2.prems" cc_invar_step invar left_right False by blast
    have "ufa_invar pf" 
      "length l = length pf" "length l = length pfl"  
      "rep_of pf (left eq) \<noteq> rep_of pf (right eq)"
      "ufa_invar l" 
      using 2(5) unfolding proof_forest_invar_def congruence_closure.select_convs apply simp 
      using 2(5) unfolding same_length_invar_def apply auto[2]
      using 2(5) False left_right unfolding same_eq_classes_invar_def 
      using propagate_loop.simps(2) same_length_invar_def apply auto[1]
      using 2(5) unfolding cc_list_invar_def by simp
    with left_right 2(4,5) have "well_formed_pf_invar (propagate_step l u t pe pf pfl ip (left eq) (right eq) eq)"
      using well_formed_pf_invar_step by simp
    then show ?thesis 
      using 2(3) cc_invar "2.hyps" False by auto
  qed
qed simp

theorem well_formed_pf_invar_merge: 
  assumes "cc_invar cc" "well_formed_pf_invar cc" "valid_vars eq (nr_vars cc)"
  shows "well_formed_pf_invar (merge cc eq)"
  using assms proof(induction cc eq rule: merge.induct)
  case (1 l u t pe pf pfl ip a b)
  have *: "merge \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (a \<approx> b)
= propagate 
    \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"
    using CC_Definition.merge.simps(1) by blast
  have "well_formed_pf_invar
\<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"
    using 1 unfolding well_formed_pf_invar_def by auto
  with propagate_domain' show ?case using well_formed_pf_invar_propagate 
    by (metis "1.prems"(1,3) * cc_invar_merge1 congruence_closure.select_convs(1))
next
  case (2 l u t pe pf pfl ip a\<^sub>1 a\<^sub>2 a)
  then show ?case proof(cases "(lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a))")
    case True
    then have *: "merge \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
(F a\<^sub>1 a\<^sub>2 \<approx> a)
= 
propagate \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      by simp
    then have "well_formed_pf_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      using 2(2) unfolding well_formed_pf_invar_def by auto
    with propagate_domain' show ?thesis using well_formed_pf_invar_propagate 
      by (metis "2.prems"(1,3) True * cc_invar_merge2 congruence_closure.select_convs(1))
  next
    case False
    then have "merge \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
(F a\<^sub>1 a\<^sub>2 \<approx> a)
= \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      by auto
    then show ?thesis using 2(2) unfolding well_formed_pf_invar_def by auto
  qed
qed

section \<open>Invariant for the well-formedness of the additional union find of the explain operation.\<close>

text \<open>Invariant for the additional union find in the explain function.\<close>
definition well_formed_uf_invar
  where
    "well_formed_uf_invar l pfl other_set \<equiv>
well_formed_pf l pfl other_set"

subsection \<open>Proof that \<open>well_formed_uf_invar\<close> is an invariant of \<open>explain_along_path\<close>\<close>

lemma well_formed_uf_invar_initial:
  "well_formed_uf_invar [0..<length pf] pfl {}"
  unfolding well_formed_uf_invar_def 
  by (simp add: Congruence_Closure.reflexive rep_of_refl)

lemma additional_uf_labels_set_fun_upd_l:
  assumes "k \<noteq> pf ! k" "k < length l"
  shows "additional_uf_labels_set (l[k := pf ! k]) pfl =
additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
proof
  show "additional_uf_labels_set (l[k := pf ! k]) pfl
    \<subseteq> additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
  proof
    fix x assume "x \<in> additional_uf_labels_set (l[k := pf ! k]) pfl"
    then obtain i where i: "x \<in> pe_to_set (pfl ! i)" 
      "i < length (l[k := pf ! k])" "l[k := pf ! k] ! i \<noteq> i" 
      unfolding additional_uf_labels_set_def by auto
    then show "x \<in> additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
    proof(cases "l ! i = i")
      case True
      with i show ?thesis unfolding additional_uf_labels_set_def 
        by (metis (no_types, lifting) Un_iff nth_list_update_neq)
    next
      case False
      then show ?thesis unfolding additional_uf_labels_set_def 
        using i by auto
    qed
  qed
next
  show "additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)
    \<subseteq> additional_uf_labels_set (l[k := pf ! k]) pfl"
  proof
    fix x assume "x \<in> additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
    then show "x \<in> additional_uf_labels_set (l[k := pf ! k]) pfl"
    proof
      assume "x \<in> additional_uf_labels_set l pfl"
      then obtain i where i: "x \<in> pe_to_set (pfl ! i)" "i < length l \<and> l ! i \<noteq> i"
        unfolding additional_uf_labels_set_def by blast
      then have "l[k := pf ! k] ! i \<noteq> i" using assms 
        by (metis nth_list_update_eq nth_list_update_neq)
      then show ?thesis unfolding additional_uf_labels_set_def 
        using i(1) i(2) by auto
    next
      assume "x \<in> pe_to_set (pfl ! k)"
      have "l[k := pf ! k] ! k \<noteq> k" 
        using assms by simp
      then show ?thesis unfolding additional_uf_labels_set_def
        using \<open>x \<in> pe_to_set (pfl ! k)\<close> assms(2) length_list_update mem_Collect_eq by fastforce
    qed
  qed
qed

text \<open>This represents the equations that are added to pending after considering a certain
label of the proof forest during the explain operation.\<close>
fun pending_equations :: "pending_equation option \<Rightarrow> equation set"
  where
    "pending_equations None = {}"
  | "pending_equations (Some (One a)) = {}"
  | "pending_equations (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))) = {(a\<^sub>1 \<approx> b\<^sub>1), (a\<^sub>2 \<approx> b\<^sub>2)}"
  | "pending_equations (Some (Two a b)) = {}"

lemma well_formed_uf_invar_union:
  assumes "well_formed_pf pf pfl {}" "well_formed_uf_invar l pfl xs" 
    "rep_of l k \<noteq> rep_of l (pf ! k)" "k < length l" "ufa_invar l" "pfl ! k \<noteq> None"
    "valid_labels_invar pfl pf cc_l" "length l = length pf" "pf ! k < length l"
    "l ! k = k" 
  shows "well_formed_uf_invar (l[k := pf ! k]) pfl (xs \<union> pending_equations (pfl ! k))"
  unfolding well_formed_uf_invar_def 
proof(standard, standard, standard, standard, standard)
  fix a b
  assume *: "a < length (l[k := pf ! k])"
    "b < length (l[k := pf ! k])"
    "rep_of (l[k := pf ! k]) a = rep_of (l[k := pf ! k]) b"
  show "(a \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))" 
  proof(cases "rep_of l a = rep_of l b")
    case True
    then have ab: "(a \<approx> b) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
      using assms * unfolding well_formed_uf_invar_def by force
    then have "additional_uf_labels_set l pfl \<subseteq> additional_uf_labels_set (l[k := pf ! k]) pfl"
      by (metis UnCI additional_uf_labels_set_fun_upd_l assms(3) assms(4) subsetI)
    then show ?thesis 
      by (metis (no_types, opaque_lifting) Congruence_Closure_monotonic ab subset_iff sup.coboundedI2 sup_commute sup_mono)
  next
    case False
    then have reps: "rep_of l a = rep_of l k \<or> rep_of l b = rep_of l k" 
      using * assms rep_of_fun_upd' by (metis length_list_update)
    have p: "path l k [k] k" 
      by (simp add: assms(4) path_length_1)
    then have reps2: "rep_of (l[k := pf ! k]) k = rep_of l (pf ! k)" "rep_of (l[k := pf ! k]) (pf ! k) = rep_of l (pf ! k)" 
      using rep_of_fun_upd_aux2 assms apply blast 
      using assms(3) assms(5) assms(9) rep_of_fun_upd' by auto
    from reps have reps_cases: "rep_of l a = rep_of l k \<and> rep_of l b = rep_of l (pf ! k) 
\<or> rep_of l b = rep_of l k \<and> rep_of l a = rep_of l (pf ! k)" 
    proof
      assume r1: "rep_of l a = rep_of l k"
      then have r2: "rep_of l b \<noteq> rep_of l k" 
        using False by presburger
      have r3: "rep_of (l[k := pf ! k]) a = rep_of (l[k := pf ! k]) k" using assms 
        by (metis "*"(1) length_list_update r1 rep_of_fun_upd_rep_of rep_of_refl)
      then have r1: "rep_of (l[k := pf ! k]) a = rep_of (l[k := pf ! k]) (pf ! k)"
        using reps2 False by (simp add: r3)
      have r4: "rep_of (l[k := pf ! k]) b = rep_of (l[k := pf ! k]) (pf ! k)" 
        using "*"(3) r1 by auto
      then show ?thesis 
        by (metis "*"(2) assms(5) length_list_update r2 rep_of_fun_upd' reps reps2(2))
    next
      assume r1: "rep_of l b = rep_of l k"
      then have r2: "rep_of l a \<noteq> rep_of l k" 
        using False by presburger
      have r3: "rep_of (l[k := pf ! k]) b = rep_of (l[k := pf ! k]) k" using assms 
        by (metis "*"(2) length_list_update r1 rep_of_fun_upd_rep_of rep_of_refl)
      then have r1: "rep_of (l[k := pf ! k]) b = rep_of (l[k := pf ! k]) (pf ! k)"
        using reps2 False by (simp add: r3)
      have r4: "rep_of (l[k := pf ! k]) b = rep_of (l[k := pf ! k]) (pf ! k)" 
        using "*"(3) r1 by auto
      then show ?thesis 
        by (metis "*"(1) "*"(3) assms(5) length_list_update r2 rep_of_fun_upd' reps reps2(2))
    qed
    have eq_in_aus: "pe_to_set (pfl ! k) \<subseteq> additional_uf_labels_set (l[k := pf ! k]) pfl"
      by (metis UnCI additional_uf_labels_set_fun_upd_l assms(3) assms(4) subsetI)
    then have auf_l_subset: "additional_uf_labels_set l pfl \<subseteq> additional_uf_labels_set (l[k := pf ! k]) pfl"
      by (metis UnCI additional_uf_labels_set_fun_upd_l assms(3) assms(4) subsetI)
    obtain a' a\<^sub>1 a\<^sub>2 b' b\<^sub>1 b\<^sub>2 where "((pfl ! k = Some (One (a' \<approx> b')) \<and> 
          (a' = pf ! k \<and> b' = k \<or> a' = k \<and> b' = pf ! k)
          \<and> valid_vars_pending (the (pfl ! k)) l)
        \<or> 
          (pfl ! k = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b')))
          \<and> (a' = pf ! k \<and> b' = k \<or> a' = k \<and> b' = pf ! k)
          \<and> valid_vars_pending (the (pfl ! k)) cc_l)" 
      using assms valid_vars_pending_iff by (metis (no_types, lifting) option.sel)
    then show ?thesis 
    proof
      assume eq: "pfl ! k = Some (One (a' \<approx> b')) \<and> (a' = pf ! k \<and> b' = k \<or> a' = k \<and> b' = pf ! k)
          \<and> valid_vars_pending (the (pfl ! k)) l"
      then have "pe_to_set (pfl ! k) = {a' \<approx> b'}" 
        by simp
      then have pf_k_eq_k: "(pf ! k \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
        apply(cases "a' = pf ! k \<and> b' = k")
        using eq_in_aus eq by auto
      from reps_cases show ?thesis
      proof
        assume rep_a_k: "rep_of l a = rep_of l k \<and> rep_of l b = rep_of l (pf ! k)"
        then have "(a \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          "(b \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          using assms "*" unfolding well_formed_uf_invar_def by force+
        then have eqs: "(a \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
          "(b \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
          by (metis Congruence_Closure_union auf_l_subset inf_sup_aci(5) inf_sup_aci(6) le_iff_sup subset_iff)+
        have "pending_equations (pfl ! k) = {}" using eq by simp
        with pf_k_eq_k eqs show ?thesis
          using Congruence_Closure.transitive1 by (metis Congruence_Closure.symmetric sup_bot_right)
      next
        assume "rep_of l b = rep_of l k \<and> rep_of l a = rep_of l (pf ! k)"
        then have "(a \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          "(b \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          using assms "*" unfolding well_formed_uf_invar_def by force+
        then have eqs: "(a \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
          "(b \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
          by (metis Congruence_Closure_union auf_l_subset inf_sup_aci(5) inf_sup_aci(6) le_iff_sup subset_iff)+
        have "pending_equations (pfl ! k) = {}" using eq by simp
        with pf_k_eq_k eqs show ?thesis
          using Congruence_Closure.transitive1 by (metis Congruence_Closure.symmetric sup_bot_right)
      qed
    next
      assume eq: "pfl ! k = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b')) \<and> 
(a' = pf ! k \<and> b' = k \<or> a' = k \<and> b' = pf ! k) \<and> 
valid_vars_pending (the (pfl ! k)) cc_l"
      then have eq': "pe_to_set (pfl ! k) = {F a\<^sub>1 a\<^sub>2 \<approx> a', F b\<^sub>1 b\<^sub>2 \<approx> b'}" 
        by simp
      then have pf_k_eq_k: "(pf ! k \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
      proof-
        have "pending_equations (pfl ! k) = {(a\<^sub>1 \<approx> b\<^sub>1), (a\<^sub>2 \<approx> b\<^sub>2)}" 
          using eq by simp
        then have "(a\<^sub>1 \<approx> b\<^sub>1) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          "(a\<^sub>2 \<approx> b\<^sub>2) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          using assms(2) unfolding well_formed_uf_invar_def by blast+
        then have in_CC: "(a\<^sub>1 \<approx> b\<^sub>1) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          "(a\<^sub>2 \<approx> b\<^sub>2) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          using auf_l_subset Congruence_Closure_union
          by (meson Congruence_Closure_monotonic equalityE in_mono sup_mono)+
        then have "(F a\<^sub>1 a\<^sub>2 \<approx> a') \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          "(F b\<^sub>1 b\<^sub>2 \<approx> b') \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          using eq_in_aus eq' by blast+
        then have "(a' \<approx> b') \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          using eq_in_aus eq' in_CC by blast
        then show ?thesis 
          using eq by fast
      qed
      from reps_cases show ?thesis
      proof
        assume rep_a_k: "rep_of l a = rep_of l k \<and> rep_of l b = rep_of l (pf ! k)"
        then have "(a \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          "(b \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          using assms "*" unfolding well_formed_uf_invar_def by force+
        then have "(a \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
          "(b \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)" 
          using Congruence_Closure_union 
          by (meson Congruence_Closure_monotonic Un_mono auf_l_subset equalityE in_mono)+
        then have "(a \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          "(b \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          using Congruence_Closure_union by (metis Un_assoc in_mono)+
        with pf_k_eq_k show ?thesis
          using Congruence_Closure.transitive1 by blast
      next
        assume "rep_of l b = rep_of l k \<and> rep_of l a = rep_of l (pf ! k)"
        then have "(a \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          "(b \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set l pfl \<union> xs)"
          using assms "*" unfolding well_formed_uf_invar_def by force+
        then have "(a \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
          "(b \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> xs)"
          by (metis Congruence_Closure_union auf_l_subset inf_sup_aci(5) inf_sup_aci(6) le_iff_sup subset_iff)+
        then have "(a \<approx> pf ! k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          "(b \<approx> k) \<in> Congruence_Closure (additional_uf_labels_set (l[k := pf ! k]) pfl \<union> (xs \<union> pending_equations (pfl ! k)))"
          using Congruence_Closure_union by (metis Un_assoc in_mono)+
        with pf_k_eq_k show ?thesis
          using Congruence_Closure.transitive1 by blast
      qed
    qed
  qed
qed

lemma well_formed_uf_invar_union':
  assumes "cc_invar cc"
    "well_formed_pf_invar cc" "well_formed_uf_invar l (pf_labels cc) xs" 
    "a < length (proof_forest cc)"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p2 x"
    "rep_of l a \<noteq> rep_of l c"
    "x = proof_forest cc ! rep_of l a" 
    "x < length l"
    "pf_labels cc ! rep_of l a \<noteq> None"
  shows "well_formed_uf_invar (l[rep_of l a := x]) (pf_labels cc) 
(xs \<union> pending_equations ((pf_labels cc) ! rep_of l a))"
proof-
  from assms have invars: "ufa_invar (proof_forest cc)" 
    "(proof_forest cc) ! rep_of l a \<noteq> rep_of l a"
    unfolding proof_forest_invar_def apply blast
    using assms 
    by (metis explain_list_invar_def path_root rep_of_idem)
  obtain pRAC where "path (proof_forest cc) c pRAC (rep_of l a)"
    by (metis (no_types, lifting) assms(4) assms(5) assms(6) assms(8) explain_list_invar_def path_nodes_lt_length_l path_snoc rep_of_bound)
  then have *: "rep_of l (rep_of l a) \<noteq> rep_of l (proof_forest cc ! rep_of l a)" 
    "rep_of l a < length l" "ufa_invar l" "pf_labels cc ! rep_of l a \<noteq> None"
    "valid_labels_invar (pf_labels cc) (proof_forest cc) (cc_list cc)" 
    "length l = length (proof_forest cc)" "(proof_forest cc) ! rep_of l a < length l"
    "l ! rep_of l a = rep_of l a"
    using rep_of_a_and_parent_rep_neq invars assms explain_list_invar_def path_nodes_lt_length_l rep_of_idem apply force
          apply (metis assms(4,5) explain_list_invar_def rep_of_bound)
    using cc_list_invar_def assms explain_list_invar_def apply auto[1]
        apply (simp add: assms(10))
    using pf_labels_invar_def assms apply presburger
    using assms explain_list_invar_def apply blast
    using assms apply auto[1]
    using assms explain_list_invar_def path_nodes_lt_length_l rep_of_root by auto
  show ?thesis 
    using well_formed_uf_invar_union[OF _ assms(3) *] assms(8) assms(2) well_formed_pf_invar_def 
    by blast
qed

fun e_pend_to_set :: "(nat * nat) list \<Rightarrow> equation set"
  where
    "e_pend_to_set [] = {}"
  | "e_pend_to_set ((a,b) # xs) = {(a \<approx> b)} \<union> e_pend_to_set xs"

lemma e_pend_to_set_append:
  "e_pend_to_set (xs @ ys) = e_pend_to_set xs \<union> e_pend_to_set ys"
  apply(induction arbitrary: ys rule: e_pend_to_set.induct)
   apply simp
  by force

lemma well_formed_uf_invar_explain_along_path:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
    "well_formed_pf_invar cc"
    "well_formed_uf_invar l (pf_labels cc) xs"
  shows "well_formed_uf_invar new_l (pf_labels cc) (xs \<union> e_pend_to_set pend)"
  using assms proof(induction arbitrary: xs rule: explain_along_path_induct)
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  from One.hyps have "pending_equations (pf_labels cc ! rep_of l a) = {}" 
    using pending_equations.simps(2) by presburger
  then have "well_formed_uf_invar (l[rep_of l a := x]) (pf_labels cc) xs"
    using well_formed_uf_invar_union' One 
    by (metis Un_empty_right not_None_eq path_nodes_lt_length_l) 
  then show ?case 
    by (simp add: One.IH One.prems(1))
next
  case (Two cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" new_l pend)
  from Two.hyps have  "pending_equations (pf_labels cc ! rep_of l a) = {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)}" 
    using pending_equations.simps(3) by presburger
  then have *: "well_formed_uf_invar (l[rep_of l a := x]) (pf_labels cc) (xs \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)})"
    using well_formed_uf_invar_union' Two 
    by (metis option.distinct(1) path_nodes_lt_length_l)
  have "e_pend_to_set ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pend) = e_pend_to_set pend \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)}"
    by auto
  then show ?case using *  Two.IH 
    using Two.prems(1) by fastforce
qed simp

subsection \<open>Correctness of \<open>explain_along_path\<close>\<close>

lemma additional_uf_labels_set_explain_along_path:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "additional_uf_labels_set new_l (pf_labels cc) = 
additional_uf_labels_set l (pf_labels cc) \<union> output"
  using assms proof(induction rule: explain_along_path_induct)
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  have "additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> pe_to_set (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) One.hyps(3,4,5,8,9) additional_uf_labels_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_iff rep_of_less_length_l)
  moreover have "pe_to_set (pf_labels cc ! rep_of l a) = {x1}" 
    by (simp add: One.hyps(10))
  ultimately show ?case 
    by (simp add: One.IH)
next
  case (Two cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" new_l pend)
  have "additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> pe_to_set (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) Two.hyps(3,4,5,8,9) additional_uf_labels_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_iff rep_of_less_length_l)
  moreover have "pe_to_set (pf_labels cc ! rep_of l a) = {F x\<^sub>1 x\<^sub>2 \<approx> x', F y\<^sub>1 y\<^sub>2 \<approx> y}" 
    by (simp add: Two.hyps(10-12))
  ultimately show ?case 
    by (simp add: Two.IH)
qed simp

lemma explain_along_path_correctness2:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
    "well_formed_pf_invar cc"
    "well_formed_uf_invar l (pf_labels cc) xs"
  shows "(a \<approx> c) \<in> Congruence_Closure 
(output \<union> additional_uf_labels_set l (pf_labels cc) \<union> e_pend_to_set pend \<union> xs)"
  using assms proof(induction arbitrary: xs rule: explain_along_path_induct)
  case (base cc l a c p)
  then show ?case unfolding well_formed_uf_invar_def 
    by (simp add: explain_list_invar_def path_nodes_lt_length_l)
next
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  let ?final_set = 
    "{x1} \<union> output \<union> additional_uf_labels_set l (pf_labels cc) \<union> e_pend_to_set pend \<union> xs"
  from One.hyps have "pending_equations (pf_labels cc ! rep_of l a) = {}" 
    using pending_equations.simps(2) by presburger
  then have "well_formed_uf_invar (l[rep_of l a := x]) (pf_labels cc) xs"
    using well_formed_uf_invar_union' One 
    by (metis Un_empty_right not_None_eq path_nodes_lt_length_l) 
  then have IH: "(x \<approx> c) \<in> Congruence_Closure 
(output \<union> additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc) \<union> e_pend_to_set pend \<union> xs)"
    by (simp add: One.IH One.prems(1))
  have auls_fun_upd: "additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> pe_to_set (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) One.hyps(3,4,5,8,9) additional_uf_labels_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_bound rep_of_iff)
  have pe_to_set: "pe_to_set (pf_labels cc ! rep_of l a) = {x1}" 
    by (simp add: One.hyps(10))
  then have IH': "(x \<approx> c) \<in> Congruence_Closure ?final_set"
    using IH auls_fun_upd by auto
  have rep_x: "(rep_of l a \<approx> x) \<in> Congruence_Closure ({x1})" 
  proof-
    have "rep_of l a < length (proof_forest cc)"
      "proof_forest cc ! rep_of l a \<noteq> rep_of l a" 
       apply (metis One.hyps(3) One.hyps(4) explain_list_invar_def path_nodes_lt_length_l rep_of_bound)
      by (metis One.hyps(3) One.hyps(4) One.hyps(5) One.hyps(8) One.hyps(9) explain_list_invar_def path_nodes_lt_length_l path_root rep_of_idem)
    with One(2) obtain a' b' where *: "(x1 = (a' \<approx> b'))
          \<and> (a' = x \<and> b' = rep_of l a \<or> a' = rep_of l a \<and> b' = x)"
      unfolding pf_labels_invar_def using One.hyps 
      by (metis emptyE insert_iff option.sel pe_to_set.simps(2) pending_equation.distinct(1))
    show ?thesis
      using Congruence_Closure.base * by blast
  qed
  have a_rep: "(a \<approx> rep_of l a) \<in> 
Congruence_Closure (additional_uf_labels_set l (pf_labels cc) \<union> xs)" 
    by (metis (no_types, lifting) One.hyps(3) One.hyps(4) One.prems(2) explain_list_invar_def path_nodes_lt_length_l rep_of_less_length_l rep_of_refl rep_of_root well_formed_uf_invar_def)
  have "(rep_of l a \<approx> x) \<in> Congruence_Closure ?final_set"
    "(a \<approx> rep_of l a) \<in> Congruence_Closure ?final_set"
    using rep_x Congruence_Closure_union apply (meson in_mono)
    using a_rep Congruence_Closure_union by (metis Un_assoc Un_commute subsetD)
  then show ?case using IH' by blast
next
  case (Two cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" new_l pend)
  let ?label = "{F x\<^sub>1 x\<^sub>2 \<approx> x', F y\<^sub>1 y\<^sub>2 \<approx> y}"
  let ?final_set = "?label \<union> output \<union> additional_uf_labels_set l (pf_labels cc) \<union>
            e_pend_to_set ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pend) \<union> xs"
  from Two.hyps have "pending_equations (pf_labels cc ! rep_of l a) = {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)}" 
    using pending_equations.simps(3) by presburger
  then have "well_formed_uf_invar (l[rep_of l a := x]) (pf_labels cc) (xs \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)})"
    using well_formed_uf_invar_union' Two
    by (metis not_None_eq path_nodes_lt_length_l) 
  then have IH: "(x \<approx> c) \<in> Congruence_Closure 
(output \<union> additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc) \<union> e_pend_to_set pend \<union> (xs \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)}))"
    using Two.IH Two.prems(1) by blast
  have auls_fun_upd: "additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> pe_to_set (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) Two.hyps(3,4,5,8,9) additional_uf_labels_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_bound rep_of_iff)
  have pe_to_set: "pe_to_set (pf_labels cc ! rep_of l a) = ?label" 
    by (simp add: Two.hyps(10-12))
  then have IH': "(x \<approx> c) \<in> Congruence_Closure ?final_set"
    using IH auls_fun_upd 
    by (metis (no_types, opaque_lifting) Cons_eq_appendI Un_commute Un_empty_left Un_insert_right e_pend_to_set.simps(2) empty_append_eq_id)
  have rep_x: "(rep_of l a \<approx> x) \<in> Congruence_Closure ({F x\<^sub>1 x\<^sub>2 \<approx> x', F y\<^sub>1 y\<^sub>2 \<approx> y} \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)})" 
  proof-
    have "rep_of l a < length (proof_forest cc)"
      "proof_forest cc ! rep_of l a \<noteq> rep_of l a" 
       apply (metis Two.hyps(3,4) explain_list_invar_def path_nodes_lt_length_l rep_of_bound)
      by (metis Two.hyps(3,4,5,8,9) explain_list_invar_def path_nodes_lt_length_l path_root rep_of_idem)
    with Two(2) have *: "(x' = x \<and> y = rep_of l a \<or> x' = rep_of l a \<and> y = x)"
      unfolding pf_labels_invar_def using Two.hyps(9-12) by auto
    have "(F y\<^sub>1 y\<^sub>2 \<approx> x') \<in> Congruence_Closure ({F x\<^sub>1 x\<^sub>2 \<approx> x', F y\<^sub>1 y\<^sub>2 \<approx> y} \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)})"
      using Congruence_Closure_split_rule by auto
    then have "(y \<approx> x') \<in> Congruence_Closure ({F x\<^sub>1 x\<^sub>2 \<approx> x', F y\<^sub>1 y\<^sub>2 \<approx> y} \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)})"
      using Congruence_Closure.base Congruence_Closure.monotonic Un_insert_left insertCI insert_absorb by auto
    then show ?thesis 
      using "*" by blast
  qed
  have a_rep: "(a \<approx> rep_of l a) \<in> 
Congruence_Closure (additional_uf_labels_set l (pf_labels cc) \<union> xs)" 
    by (metis (no_types, lifting) Two.hyps(3,4) Two.prems(2) explain_list_invar_def path_nodes_lt_length_l rep_of_less_length_l rep_of_refl rep_of_root well_formed_uf_invar_def)
  have "{F x\<^sub>1 x\<^sub>2 \<approx> x', F y\<^sub>1 y\<^sub>2 \<approx> y} \<union> {(x\<^sub>1 \<approx> y\<^sub>1), (x\<^sub>2 \<approx> y\<^sub>2)} \<subseteq> ?final_set" 
    by auto
  then have "(rep_of l a \<approx> x) \<in> Congruence_Closure ?final_set"
    "(a \<approx> rep_of l a) \<in> Congruence_Closure ?final_set"
    using rep_x Congruence_Closure_union apply (meson Congruence_Closure_monotonic in_mono)
    using a_rep Congruence_Closure_union by (metis Un_assoc Un_commute subsetD)
  then show ?case using IH' by blast
qed

(*
lemma cc_explain_aux_correctness:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "\<forall>(a, b)\<in>set xs. a < nr_vars cc \<and> b < nr_vars cc"
    "well_formed_pf_invar cc"
    "well_formed_uf_invar l (pf_labels cc) (e_pend_to_set xs)"
    "(x, y) \<in> set xs" "are_congruent cc (x \<approx> y)"
  shows "(x \<approx> y) \<in> Congruence_Closure (cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc))"
  using assms proof(induction arbitrary: x y rule: cc_explain_aux_induct)
  case (congruent cc l a b xs c output1 new_l pending1 output2 new_new_l pending2)
  then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b" 
    by (meson explain_along_path_lowest_common_ancestor)
  have wf_invar: "well_formed_uf_invar new_l (pf_labels cc) (e_pend_to_set (pending1 @ (a, b) # xs))" 
    using e_pend_to_set_append well_formed_uf_invar_explain_along_path[OF congruent(2,3) p(1) ]
      (*TODO change well_formed_uf_invar_explain_along_path to delete (a,b) but only after eap ac and eap ab*)
    by (metis congruent.hyps(9) congruent.prems(1) congruent.prems(2) sup_commute)
  have el_invar: "explain_list_invar new_l (proof_forest cc)" using explain_list_invar_explain_along_path' 
    by (metis congruent.hyps(2) congruent.hyps(3) congruent.hyps(5) congruent.hyps(9) explain_along_path_domain p(1))
  have "e_pend_to_set (pending1 @ pending2 @ (a, b) # xs) = 
e_pend_to_set (pending1 @ (a, b) # xs) \<union> e_pend_to_set pending2" 
    using e_pend_to_set_append by auto
  then have "well_formed_uf_invar new_new_l (pf_labels cc) (e_pend_to_set (pending1 @ pending2 @ (a, b) # xs))"
    using well_formed_uf_invar_explain_along_path[OF congruent(2) el_invar p(2) _ _ wf_invar] e_pend_to_set_append
    by (metis congruent.hyps(10) congruent.prems(1))
  have *: "e_pend_to_set (pending1 @ pending2 @ (a, b) # xs)
= e_pend_to_set ([(a, b)] @ pending1 @ pending2 @ xs)"
    using e_pend_to_set_append by force
  then show ?case proof(cases "(a, b) = (x, y)")
    case True
    then show ?thesis sorry
  next
    case False
    from congruent have IH: "(x \<approx> y) \<in> Congruence_Closure (cc_explain_aux cc new_new_l ([(a, b)] @ pending1 @ pending2 @ xs) 
\<union> additional_uf_labels_set new_new_l (pf_labels cc))" using * congruent.IH sorry
    then show ?thesis sorry
  qed
next
  case (not_congruent cc l a b xs)
  have "(a, b) \<noteq> (x, y)" 
    using not_congruent.hyps(7) not_congruent.prems(4) by auto
  then have "rep_of (proof_forest cc) a \<noteq> rep_of (proof_forest cc) b" 
    using are_congruent_rep_of_neq not_congruent(2,5,6,7) by blast
  then have "well_formed_uf_invar l (pf_labels cc) (e_pend_to_set xs)"
    using well_formed_uf_invar_remove_if_rep_neq not_congruent.prems(2) by blast
  then show ?case 
    using cc_explain_aux_simp3 not_congruent by auto
qed simp
*)


end
