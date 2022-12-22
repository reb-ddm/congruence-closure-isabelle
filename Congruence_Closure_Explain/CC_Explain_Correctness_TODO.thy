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
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain_aux cc l eqs \<union> cc_list_set l)"
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
          by (smt (verit, ccfv_SIG) True hd_append2 list.discI list.sel(1) longest_common_prefix.elims snoc_eq_iff_butlast')
        then show ?thesis 
          by (smt (verit, del_insts) "1.prems"(1) \<open>longest_common_prefix (xs @ [a]) (y # ys) = [x]\<close> \<open>longest_common_prefix xs (y # ys) = x # longest_common_prefix short_xs ys\<close> list.sel(1) longest_common_prefix.elims longest_common_prefix.simps(3))
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
next
  case ("2_1" uv)
  then show ?case by blast
next
  case ("2_2" )
  then show ?case by simp
qed

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

section \<open>Helper lemmata about explain_along_path\<close>

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
    "(\<And>cc l a c p1 p2 x x21 x22 x21a x22a x23 x21b x22b x23a output new_l pend.
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
      \<Longrightarrow> x21 = (F x21a x22a \<approx> x23) \<Longrightarrow> x22 = (F x21b x22b \<approx> x23a) \<Longrightarrow>
      x < length l \<Longrightarrow> x21a < length l \<Longrightarrow> x22a < length l 
      \<Longrightarrow> x23 < length l \<Longrightarrow> x21b < length l \<Longrightarrow> x22b < length l \<Longrightarrow> x23a < length l 
      \<Longrightarrow> P cc (l[rep_of l a := x]) x c output new_l pend p2 \<Longrightarrow>
      P cc l a c ({(F x21a x22a \<approx> x23), (F x21b x22b \<approx> x23a)} \<union> output) new_l ([(x21a, x21b), (x22a, x22b)] @ pend) p1)"
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
         apply (metis "1.prems" explain_list_invar_def path_nodes_lt_length_l rep_of_bound)
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
        then show ?thesis  using 1(10)[OF 1(1,4,5,6) path_to_rep invar(1) rec' False x_def 
              Some(1) _ _ \<open>x < length l\<close> Some(2-)]
          using rec by fastforce
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
"(\<And>cc l a c p1 p2 x x21 x22 x21a x22a x23 x21b x22b x23a output new_l pend.
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
      \<Longrightarrow> x21 = (F x21a x22a \<approx> x23) \<Longrightarrow> x22 = (F x21b x22b \<approx> x23a) \<Longrightarrow>
      x < length l \<Longrightarrow> x21a < length l \<Longrightarrow> x22a < length l 
      \<Longrightarrow> x23 < length l \<Longrightarrow> x21b < length l \<Longrightarrow> x22b < length l \<Longrightarrow> x23a < length l 
      \<Longrightarrow> P cc (l[rep_of l a := x]) x c output new_l pend \<Longrightarrow>
      P cc l a c ({(F x21a x22a \<approx> x23), (F x21b x22b \<approx> x23a)} \<union> output) new_l ([(x21a, x21b), (x22a, x22b)] @ pend))"
shows "P cc l a c output new_l pend"
proof-
  obtain p where p: "path (proof_forest cc) c p a" using assms(1-6) length_explain_list_cc_list lowest_common_ancestor_correct 
    unfolding proof_forest_invar_def same_length_invar_def
    by (metis explain_list_invar_def)
  show ?thesis 
    using explain_along_path_induct[OF assms(1,2) p assms(7), of "\<lambda> cc l a c output new_l pend p . P cc l a c output new_l pend"] 
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
    "(\<And>cc l a b xs.
    cc_explain_aux_dom (cc, l, (a, b) # xs) \<Longrightarrow>
 cc_invar cc \<Longrightarrow> explain_list_invar l (proof_forest cc) \<Longrightarrow>
(\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc) \<Longrightarrow>
 a < nr_vars cc \<Longrightarrow> b < nr_vars cc \<Longrightarrow>
    (\<And>c output1 new_l pending1 output2 new_new_l pending2.
        are_congruent cc (a \<approx> b) \<Longrightarrow>
       c = lowest_common_ancestor (proof_forest cc) a b \<Longrightarrow>
    (output1, new_l, pending1) = explain_along_path cc l a c \<Longrightarrow>
    (output2, new_new_l, pending2) = explain_along_path cc new_l b c
\<Longrightarrow> P cc new_new_l (pending1 @ pending2 @ xs))
\<Longrightarrow> P cc l ((a, b) # xs))" 
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
    then have in_bounds: "a < nr_vars cc" "b < nr_vars cc" 
      by fastforce+
    then show ?case proof(cases "are_congruent cc (a \<approx> b)")
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
        by (metis Pair_inject c_def eap(1) eap(2) in_bounds(1) in_bounds(2) list.set_intros(2))
    next
      case False
      have "P cc l xs" using 2(3)[OF False 2(4,5)] 2(6,7,8,9) 
        by fastforce
      then show ?thesis using "2.prems"(6)[OF 2(1,4,5)] using 2(6) False 
        by auto
    qed
  qed blast
qed

section \<open>Proofs about how \<open>cc_explain\<close> changes with a function update or with many function updates. \<close>

lemma rep_of_fun_upd4:
  assumes "ufa_invar l"
    "k \<in> set (path_to_root l c)"
    "u < length l"
    "c < length l"
    "rep_of l k \<noteq> rep_of l u" 
  shows "rep_of (l[k := u]) c = rep_of l u"
proof-
  obtain p1 p2 where "path_to_root l c = p1 @ [k] @ p2" 
    by (metis Cons_eq_appendI assms(2) empty_append_eq_id in_set_conv_decomp_first)
  then have "path l (rep_of l c) (p1 @ [k] @ p2) c"
    using path_to_root_correct
    by (metis assms(1) assms(4))
  then have "path l k ([k] @ p2) c" 
    by (metis append_is_Nil_conv hd_append2 length_Cons less_numeral_extra(3) list.sel(1) list.size(3) nat_in_between_eq(1) path_divide2)
  then show ?thesis 
    using assms rep_of_fun_upd_aux2 by force
qed

lemma fun_upd_somewhere_else_does_not_join_a_and_c:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "k < length l" "a < length l" "rep_of l a \<noteq> rep_of l c" "k \<noteq> rep_of l a"
  shows "rep_of (l[k := (proof_forest cc) ! k]) a \<noteq> rep_of (l[k := (proof_forest cc) ! k]) c"
    (is "rep_of ?l_upd a \<noteq> rep_of ?l_upd c")
proof
  assume "rep_of ?l_upd a = rep_of ?l_upd c"
  have invars: "ufa_invar l""ufa_invar (proof_forest cc)"
    "length (proof_forest cc) = length l" "length ?l_upd = length l"
    "a < length l" "c < length l" "rep_of l a < length l" 
    "proof_forest cc ! k < length l"   
    using assms explain_list_invar_def proof_forest_invar_def 
           apply auto[5]
    using assms(2) assms(3) explain_list_invar_def path_nodes_lt_length_l apply auto[1]
    using assms(2) assms(5) explain_list_invar_def rep_of_less_length_l apply blast
    using proof_forest_invar_def explain_list_invar_def assms 
    by (simp add: ufa_invarD(2))
  have "explain_list_invar ?l_upd (proof_forest cc)" 
    by (simp add: assms explain_list_invar_fun_upd invars(2))
  then have "?l_upd ! rep_of l a = proof_forest cc ! rep_of l a \<or> ?l_upd ! rep_of l a = rep_of l a"
    using explain_list_invar_def invars by auto
  then show False
  proof
    assume "?l_upd ! rep_of l a = proof_forest cc ! rep_of l a"
    then show False 
      by (metis assms(2,3,5,6,7) explain_list_invar_imp_valid_rep invars(1,2) nth_list_update' rep_of_root)
  next
    assume "?l_upd ! rep_of l a = rep_of l a"
    then have 1: "rep_of ?l_upd a = rep_of l a"
      by (metis assms(2,4,5,7) explain_list_invar_def list_update_id rep_of_fun_upd' rep_of_refl)
    have path_root_c: "path l (rep_of l c) (path_to_root l c) c"
      by (simp add: invars path_to_root_correct)
    have 2: "rep_of ?l_upd c = rep_of l c \<or> rep_of ?l_upd c = rep_of l (proof_forest cc ! k)"
      using rep_of_fun_upd' 
    proof(cases "k \<in> set (path_to_root l c)")
      case True
      then show ?thesis using rep_of_fun_upd4 
        by (metis (no_types, lifting) assms(2) assms(4) explain_list_invar_def invars(2) invars(6) list_update_id rep_of_l_a_is_root_in_pf_if_parent_has_same_rep rep_of_refl ufa_invarD(2))
    next
      case False
      then show ?thesis using rep_of_fun_upd 
        using \<open>path l (rep_of l c) (path_to_root l c) c\<close> invars(1) by auto
    qed
    have 3: "rep_of l (proof_forest cc ! rep_of l a) \<noteq> rep_of l (rep_of l a)"
      using rep_of_a_and_parent_rep_neq assms unfolding proof_forest_invar_def 
      by (smt (verit) assms(1) explain_list_invar_def path_root path_to_rep_of_l_a_explain_along_path_case_2 rep_of_idem) 
    have "rep_of l a = rep_of l (proof_forest cc ! k) \<Longrightarrow> rep_of ?l_upd c = rep_of l c"
    proof-
      assume a_pf_k_same_rep: "rep_of l a = rep_of l (proof_forest cc ! k)"
      then have "rep_of l (proof_forest cc ! k) \<noteq> rep_of l c" 
        using assms(6) by presburger
      then have "rep_of l k = rep_of l (proof_forest cc ! k)" 
      proof-
        have k_root: "l ! k = k" 
          using assms(2) assms(4) explain_list_invar_def 
          by (metis \<open>rep_of (l[k := proof_forest cc ! k]) a = rep_of (l[k := proof_forest cc ! k]) c\<close> assms(6) list_update_id)
        then have "k \<notin> set (path_to_root l c)" 
        proof-
          have "k \<notin> set (tl (path_to_root l c))"
            using \<open>path l (rep_of l c) (path_to_root l c) c\<close> invars(1) path_contains_no_root k_root 
            by blast
          moreover have "hd (path_to_root l c) = (rep_of l c)" 
            using \<open>path l (rep_of l c) (path_to_root l c) c\<close> hd_path by auto
          moreover have "rep_of l c \<noteq> k" 
            (* If they were equal, we could construct a path from rep_of l c to c to a in the proof forest
and then from the lca of a and rep_of l c, because rep_of l a = rep_of l (pf ! k)
and then we have two different paths from rep_of l c to a 
One of them exists in l and the other doesn't, therefore they are different *)
          proof
            assume "rep_of l c = k"
            have "path (proof_forest cc) (rep_of l c) (path_to_root l c) c"
              using assms(2) explain_list_invar_paths path_root_c by blast
            define lcaAK where "lcaAK = lowest_common_ancestor l a (proof_forest cc ! k)"
            then have "common_ancestor l a (proof_forest cc ! k) lcaAK" 
              using lowest_common_ancestor_correct a_pf_k_same_rep invars 
              by blast
            then obtain pLcaA pLcaPfK where "path l lcaAK pLcaA a" 
              "path l lcaAK pLcaPfK (proof_forest cc ! k)"
              by auto
            then have p1: "path (proof_forest cc) lcaAK pLcaA a" 
              "path (proof_forest cc) lcaAK pLcaPfK (proof_forest cc ! k)"
              using assms(2) explain_list_invar_paths by blast+
            then have p2: "path (proof_forest cc) (proof_forest cc ! k) [(proof_forest cc ! k), k] k"
              by (metis \<open>rep_of ?l_upd a = rep_of ?l_upd c\<close> \<open>rep_of l c = k\<close> assms(4) assms(7) invars(3) invars(8) k_root list_update_id path.step path_length_1)
            then have p3: "path (proof_forest cc) k (path_to_root l c) c" 
              using \<open>path (proof_forest cc) (rep_of l c) (path_to_root l c) c\<close> \<open>rep_of l c = k\<close> by auto
            then have p4: "path (proof_forest cc) lcaAK (pLcaPfK @ [k]) k" 
              by (metis \<open>rep_of l (proof_forest cc ! k) \<noteq> rep_of l c\<close> \<open>rep_of l c = k\<close> assms(4) invars(1) invars(3) invars(6) invars(8) p1(2) path_snoc rep_of_idem)
            then have p5: "path (proof_forest cc) lcaAK (pLcaPfK @ path_to_root l c) c" 
              using p3 path_concat2 by fastforce 
            then have p6: "path (proof_forest cc) lcaAK (pLcaPfK @ path_to_root l c @ tl p) a" 
              using assms(3) path_concat1 by fastforce
            have "last (path_to_root l c) = c" 
              using last_path p3 by auto
            then have "c \<in> set (pLcaPfK @ path_to_root l c @ tl p)" 
              by (smt (verit, ccfv_threshold) \<open>path (proof_forest cc) (rep_of l c) (path_to_root l c) c\<close> \<open>path l lcaAK pLcaA a\<close> \<open>rep_of l c = k\<close> append_self_conv2 assms(3) invars(1) invars(2) k_root p1(1) p1(2) p2 p6 path_divide2 path_to_root_has_length_1 path_unique paths_iff)
            have "c \<notin> set pLcaA" 
              by (metis \<open>path l lcaAK pLcaA a\<close> assms(6) in_set_conv_nth invars(1) path_rep_of_neq_not_in_path)
            then have "pLcaA \<noteq> pLcaPfK @ path_to_root l c @ tl p"
              using \<open>c \<in> set (pLcaPfK @ path_to_root l c @ tl p)\<close> by blast
            then show False using path_unique 
              using invars(2) p1(1) p6 by auto
          qed
          ultimately show "k \<notin> set (path_to_root l c)"
            by (metis not_hd_in_tl)
        qed
        then show ?thesis 
          using "1" \<open>path l (rep_of l c) (path_to_root l c) c\<close> \<open>rep_of (l[k := proof_forest cc ! k]) a = rep_of (l[k := proof_forest cc ! k]) c\<close> assms(6) invars(1) rep_of_fun_upd by auto
      qed
      then show ?thesis using rep_of_fun_upd4
        using \<open>path l (rep_of l c) (path_to_root l c) c\<close> invars(1) rep_of_fun_upd 
        using \<open>rep_of l (proof_forest cc ! k) \<noteq> rep_of l c\<close> invars(6) rep_of_fun_upd' by presburger
    qed
    then show ?thesis using 1 2 
      by (simp add: \<open>rep_of ?l_upd a = rep_of ?l_upd c\<close> assms(6))
  qed
qed

fun pending_equation_to_set :: "pending_equation option \<Rightarrow> equation set"
  where
    "pending_equation_to_set None = {}"
  | "pending_equation_to_set (Some (One a')) = {a'}"
  | "pending_equation_to_set (Some (Two a' b')) = {a', b'}"

lemma explain_along_path_output_fun_upd:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output1, new_l1, pend1)"
    "explain_along_path cc (l[k := (proof_forest cc) ! k]) a c = (output2, new_l2, pend2)"
    "k < length l"
  shows "output2 \<supseteq> output1 - pending_equation_to_set (pf_labels cc ! k) \<and>
output2 \<subseteq> output1"
proof-
  have "explain_along_path_dom (cc, l, a, c)" using assms explain_along_path_domain 
    by blast
  then show ?thesis using assms proof(induction 
      arbitrary: output1 new_l1 pend1 output2 new_l2 pend2 p rule: explain_along_path.pinduct)
    case (1 cc l a c)
    have a_in_bounds: "a < length l" 
      using "1.prems" unfolding explain_list_invar_def 
      using path_nodes_lt_length_l by presburger
    then show ?case proof(cases "rep_of l a = rep_of l c")
      case True
        (*BASE CASE: the output is {} in both cases*)
      have invar: "ufa_invar l" using "1.prems" unfolding explain_list_invar_def by simp
      then have "rep_of (l[k := (proof_forest cc) ! k]) a = rep_of (l[k := (proof_forest cc) ! k]) c" 
        using explain_list_invar_def "1.prems" 
        by (smt (verit, ccfv_SIG) True list_update_same_conv path_nodes_lt_length_l rep_of_fun_upd' rep_of_iff rep_of_next_recursive_step_explain_along_path single)
      then have "output2 = {}" "output1 = {}"
        using "1.prems" explain_along_path_simp1 True by auto
      then show ?thesis by simp
    next
      case repa_neq_repb: False
        (*INDUCTIVE CASE:*)
      have not_None: "(pf_labels cc) ! rep_of l a \<noteq> None"  using "1.prems" 
        using pf_labels_explain_along_path_case_2 repa_neq_repb a_in_bounds by blast
      define x where "x = proof_forest cc ! rep_of l a"
      obtain output1' new_l1' pend1' output2' new_l2' pend2'
        where recursive_calls:
          "explain_along_path cc (l[rep_of l a := x]) x c = (output1', new_l1', pend1')"
          "explain_along_path cc (l[rep_of l a := x, k := (proof_forest cc) ! k]) x c = (output2', new_l2', pend2')"
        by (meson prod_cases3)    
      obtain p1 where "path (proof_forest cc) c p1 x" using path_to_parent_of_rep_of_l_a_explain_along_path_case_2 
          "1.prems"(1,2,3) repa_neq_repb x_def a_in_bounds by blast
      define l_upd where "l_upd = l[rep_of l a := x]"
      have l_upd_invar: "explain_list_invar l_upd (proof_forest cc)"
        using "1.prems" explain_list_invar_step proof_forest_invar_def repa_neq_repb a_in_bounds
        unfolding l_upd_def x_def by blast
      have "proof_forest cc ! rep_of l a \<noteq> rep_of l a" "rep_of l a < length (proof_forest cc)"
         apply (metis "1.prems"(2) a_in_bounds \<open>path (proof_forest cc) c p1 x\<close> explain_list_invar_def path_root rep_of_idem repa_neq_repb x_def)
        using "1.prems"(2) a_in_bounds explain_list_invar_def rep_of_bound by fastforce
      then have pf_labels_invar_property: "\<exists> k\<^sub>1 k\<^sub>2 k\<^sub>3 k\<^sub>4 k\<^sub>5 k\<^sub>6 . (pf_labels cc ! rep_of l a = Some (One (k\<^sub>1 \<approx> k\<^sub>2))
\<or>  pf_labels cc ! rep_of l a = Some (Two (F k\<^sub>3 k\<^sub>4 \<approx> k\<^sub>1) (F k\<^sub>5 k\<^sub>6 \<approx> k\<^sub>2)))
          \<and> (k\<^sub>1 = proof_forest cc ! rep_of l a \<and> k\<^sub>2 = rep_of l a \<or> k\<^sub>1 = rep_of l a \<and> k\<^sub>2 = proof_forest cc ! rep_of l a)
          \<and> valid_vars_pending (the (pf_labels cc ! rep_of l a)) (cc_list cc)" 
        using pf_labels_invar_def "1.prems"(1,2) explain_list_invar_def 
        by meson
      then show ?thesis proof(cases "k = rep_of l a")
        case True
          (* CASE when the edge we add to output is not added in the updated list case *)
          (* the updated list case is equal to the next recursive call of the normal list case *)

        from True x_def have same_l: "l[rep_of l a := x] = l[k := proof_forest cc ! k]"
          "l[rep_of l a := x] = (l[rep_of l a := x, k := (proof_forest cc) ! k])"
          by auto
        then have *: "output2' = output1'" 
          using recursive_calls x_def by auto
        have same_rep: "rep_of l x = rep_of (l[rep_of l a := x]) a" 
          using "1.prems" a_in_bounds unfolding x_def explain_list_invar_def 
          by (metis "1.prems"(2) \<open>path (proof_forest cc) c p1 x\<close> list_update_same_conv path_nodes_lt_length_l path_to_root_correct proof_forest_invar_def rep_of_a_and_parent_rep_neq rep_of_fun_upd_aux2 rep_of_idem x_def)
        have "output2 = output2'" 
        proof(cases "rep_of l_upd x = rep_of l_upd c")
          (*Case one of the recursive call: base case*)
          case True
          then have 1: "output2' = {}" using recursive_calls same_l explain_along_path_simp1 l_upd_def
            by force
          have "rep_of l_upd x = rep_of l_upd a" using same_rep unfolding x_def l_upd_def 
            by (metis (no_types, lifting) "1.prems"(2) a_in_bounds \<open>path (proof_forest cc) c p1 x\<close> explain_list_invar_def l_upd_def l_upd_invar nth_list_update_eq path_nodes_lt_length_l rep_of_bound rep_of_fun_upd' rep_of_idem rep_of_min x_def)
          then have "output2 = {}" using same_l explain_along_path_simp1 same_rep True "1.prems"(5) l_upd_def by force
          with 1 show ?thesis 
            by simp
        next
          case False
            (* Case two of the recursive call *)
          define b where "b = (proof_forest cc) ! rep_of l_upd x"
          have pfl_not_None: "((pf_labels cc) ! rep_of l_upd x) \<noteq> None" using pf_labels_explain_along_path_case_2 
            by (metis "1.prems"(1) "1.prems"(2) "1.prems"(3) a_in_bounds False l_upd_def l_upd_invar length_explain_list_cc_list rep_of_next_recursive_step_explain_along_path x_def)

          have recursive_calls':  
            "explain_along_path cc l_upd x c = (output2', new_l2', pend2')" 
            using recursive_calls(2) same_l(2) l_upd_def by auto
          obtain output12 new_l12 pend12
            where recursive_calls2:
              "(output12, new_l12, pend12) = 
                explain_along_path cc (l_upd[rep_of l_upd x := (proof_forest cc) ! rep_of l_upd x]) b c"
            by (metis prod_cases3)
          have domain: "explain_along_path_dom (cc, l_upd, x, c)" using l_upd_invar explain_along_path_domain "1.prems"
            using explain_along_path_domain 
            using \<open>path (proof_forest cc) c p1 x\<close> by blast
          have *: "rep_of l_upd x = rep_of l_upd a"
            unfolding l_upd_def x_def using rep_of_next_recursive_step_explain_along_path "1.prems"  a_in_bounds
            by blast
          have two_recursive_calls_same: "explain_along_path cc (l_upd[rep_of l_upd x := (proof_forest cc) ! rep_of l_upd x]) b c
= explain_along_path cc (l_upd[rep_of l_upd a := (proof_forest cc) ! rep_of l_upd a]) ((proof_forest cc) ! rep_of l_upd a) c"
            unfolding b_def * same_l by simp
          have recursive_calls'': "explain_along_path cc l_upd a c = (output2, new_l2, pend2)" 
            using "1.prems"(5) l_upd_def True x_def by fastforce
          have prems: "rep_of l_upd a \<noteq> rep_of l_upd c"
            "(output12, new_l12, pend12) =
    explain_along_path cc (l_upd[rep_of l_upd a := proof_forest cc ! rep_of l_upd a]) (proof_forest cc ! rep_of l_upd a) c"
            "explain_along_path_dom (cc, l_upd, a, c)"
            using "*" False apply auto[1]
             apply (simp add: two_recursive_calls_same recursive_calls2)
            using explain_along_path_domain l_upd_invar "1.prems" by blast
          show ?thesis proof(cases "the ((pf_labels cc) ! rep_of l_upd x)")
            case (One a'2)
              (* Case two of the recursive call: the edge has one label *)
            have "pf_labels cc ! rep_of l_upd x = Some (One a'2)" 
              using pfl_not_None One by force
            then have 1: "output2' = {a'2} \<union> output12" using explain_along_path_simp2 same_l False 
                recursive_calls2 recursive_calls' domain b_def False by auto
            have "pf_labels cc ! rep_of l_upd a = Some (One a'2)" by (metis "*" \<open>pf_labels cc ! rep_of l_upd x = Some (One a'2)\<close>)
            then have "output2 = {a'2} \<union> output12" using explain_along_path_simp2 prems
                "1.prems"(5) recursive_calls2 recursive_calls'' by force
            then show ?thesis using 1 by simp
          next
            case (Two a'2 b'2)
              (* Case two of the recursive call: the edge has two labels *)
            have Two': "pf_labels cc ! rep_of l_upd x = Some (Two a'2 b'2)" 
              using pfl_not_None Two by force
            then obtain aa bb a1a a2a b1b b2b where "a'2 = (F a1a a2a \<approx> aa)" "b'2 = (F b1b b2b \<approx> bb)"
              and pf_labels_two: "pf_labels cc ! rep_of l_upd x = Some (Two (F a1a a2a \<approx> aa) (F b1b b2b \<approx> bb))"
              using pf_labels_Two_valid 
              by (metis "1.prems"(1) False Two \<open>path (proof_forest cc) c p1 x\<close> l_upd_invar pending_equation.inject(2) the_state.simps)
            then have 1: "output2' = {(F a1a a2a \<approx> aa), (F b1b b2b \<approx> bb)} \<union> output12" 
              using explain_along_path_simp3[OF False pf_labels_two] same_l False 
                recursive_calls2 recursive_calls' domain b_def False Two' 
              by (metis prod.inject)
            have "pf_labels cc ! rep_of l_upd a = Some (Two (F a1a a2a \<approx> aa) (F b1b b2b \<approx> bb))" 
              using "*" pf_labels_two by auto
            then have "output2 = {(F a1a a2a \<approx> aa), (F b1b b2b \<approx> bb)} \<union> output12" 
              by (metis "1.prems"(5) Pair_inject True explain_along_path_simp3 l_upd_def prems(1) prems(2) prems(3) x_def)
            then show ?thesis using 1 by simp
          qed
        qed
        show ?thesis proof(cases "the ((pf_labels cc) ! rep_of l a)")
          (* CASE One *)
          case (One x1)
          from One have Some: "(pf_labels cc) ! rep_of l a = Some (One x1)" using not_None 
            by auto
          then have IH: "output2' \<supseteq> output1' - pending_equation_to_set (pf_labels cc ! k)
\<and> output2' \<subseteq> output1'" using 
            1 repa_neq_repb x_def One l_upd_invar l_upd_def
            l_upd_def x_def 
            by (metis (no_types, lifting) \<open>path (proof_forest cc) c p1 x\<close> explain_list_invar_def path_nodes_lt_length_l recursive_calls(1) recursive_calls(2))
          have output_recursive: "output1 = {x1} \<union> output1'" using explain_along_path_simp2 1 recursive_calls repa_neq_repb Some x_def
            by simp
          have "l[rep_of l a := x] = l[k := proof_forest cc ! k]" 
            by (simp add: same_l(1))
          then show ?thesis using * output_recursive 
            using One True IH \<open>output2 = output2'\<close> Some by force
        next
          case (Two x21 x22)
            (* CASE Two *)
          from Two have Some: "(pf_labels cc) ! rep_of l a = Some (Two x21 x22)" using not_None 
            by auto
          then obtain a1 a2 a3 a4 a5 a6 where Some': 
            "(pf_labels cc) ! rep_of l a = Some (Two (F a1 a2 \<approx> a3) (F a4 a5 \<approx> a6))"
            using not_None pf_labels_invar_property
            by auto
          then have IH: "output2' \<supseteq> output1' - pending_equation_to_set (pf_labels cc ! k)
\<and> output2' \<subseteq> output1'" using 
            1 repa_neq_repb x_def Two l_upd_invar l_upd_def
            l_upd_def x_def 
            by (smt (z3) "*" \<open>path (proof_forest cc) c p1 x\<close> length_explain_list_cc_list option.sel path_nodes_lt_length_l recursive_calls(1) same_l(2) same_length_invar_def)
          have output_recursive: "output1 = {(F a1 a2 \<approx> a3), (F a4 a5 \<approx> a6)} \<union> output1'" 
            using explain_along_path_simp3[OF repa_neq_repb Some' recursive_calls(1)[unfolded x_def]]
            by (simp add: "1.hyps" "1.prems"(4))
          have "l[rep_of l a := x] = l[k := proof_forest cc ! k]" 
            by (simp add: same_l(1))
          then show ?thesis using * output_recursive 
            using Two True IH \<open>output2 = output2'\<close> Some Diff_cancel Some' Un_Diff sup_bot_right by force
        qed
      next
        case False': False
          (* CASE when the edge we add to output is also added in the updated list case *)
          (* To show: the new added edge is not equal to the edge k *)
        let ?l_upd = "l[k := (proof_forest cc) ! k]"
        have ***: "rep_of l a = rep_of ?l_upd a" 
          using False' "1.prems" a_in_bounds explain_list_invar_def path_nodes_lt_length_l rep_of_fun_upd' rep_of_refl 
          by (metis list_update_same_conv)
        then have *: "l[rep_of l a := x, k := (proof_forest cc) ! k] = ?l_upd[rep_of l a := x]"
          using False' 
          by (simp add: list_update_swap)
        have "explain_list_invar ?l_upd (proof_forest cc)" 
          using explain_list_invar_fun_upd using "1.prems"(1) unfolding proof_forest_invar_def 
          using "1.prems"(2) "1.prems"(6) by presburger
        then have domain: "explain_along_path_dom (cc, ?l_upd, a, c)" 
          using explain_along_path_domain 
          using "1.prems"(1) "1.prems"(3) by blast
        then have **: 
          "explain_along_path cc (?l_upd[rep_of ?l_upd a := proof_forest cc ! rep_of ?l_upd a])
     (proof_forest cc ! rep_of ?l_upd a) c = (output2', new_l2', pend2')"
          "rep_of ?l_upd a \<noteq> rep_of ?l_upd c"
          using "*" "***" recursive_calls(2) apply auto[1]
          using x_def apply force
          using fun_upd_somewhere_else_does_not_join_a_and_c "1.prems" False' a_in_bounds repa_neq_repb by blast

        then show ?thesis
        proof(cases "pf_labels cc ! k = None \<or> proof_forest cc ! k = k")
          case True
          then have *: "pf_labels cc ! k = None \<Longrightarrow> pending_equation_to_set (pf_labels cc ! k) = {}"
            by simp
          have "proof_forest cc ! k = k \<Longrightarrow> l ! k = k" 
            using "1.prems"(2) "1.prems"(6) explain_list_invar_def by fastforce
          with "1.prems" have "proof_forest cc ! k = k \<Longrightarrow> pf_labels cc ! k = None" 
            unfolding l_upd_def pf_labels_invar_def
            by (metis explain_list_invar_def)


          show ?thesis proof(cases "the ((pf_labels cc) ! rep_of l a)")
            (* CASE One *)
            case One': (One x1)
            from One' have Some: "(pf_labels cc) ! rep_of l a = Some (One x1)" using not_None 
              by auto
            then have IH: "output2' \<supseteq> output1' - pending_equation_to_set (pf_labels cc ! k)
\<and> output2' \<subseteq> output1'" using 
              1 repa_neq_repb x_def One' l_upd_invar l_upd_def
              l_upd_def x_def 
              by (metis (no_types, lifting) \<open>path (proof_forest cc) c p1 x\<close> explain_list_invar_def path_nodes_lt_length_l recursive_calls)
            have o2: "output2 = {x1} \<union> output2'" 
              using explain_along_path_simp2 ** Some *** domain 1(8) by simp
            have output_recursive: "output1 = {x1} \<union> output1'" 
              using explain_along_path_simp2 1 recursive_calls repa_neq_repb Some x_def
              by simp

            then show ?thesis 
              using 1 True IH o2 by blast
          next
            case (Two x21 x22)
              (* CASE Two *)
            from Two have Some: "(pf_labels cc) ! rep_of l a = Some (Two x21 x22)" using not_None 
              by auto
            then obtain a1 a2 a3 a4 a5 a6 where Some': 
              "(pf_labels cc) ! rep_of l a = Some (Two (F a1 a2 \<approx> a3) (F a4 a5 \<approx> a6))"
              using not_None pf_labels_invar_property
              by auto
            then have IH: "output2' \<supseteq> output1' - pending_equation_to_set (pf_labels cc ! k)
\<and> output2' \<subseteq> output1'" using 
              1 repa_neq_repb l_upd_invar 
              unfolding l_upd_def x_def 
              by (metis (no_types, lifting) \<open>\<And>thesis. (\<And>p1. path (proof_forest cc) c p1 x \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> explain_list_invar_def option.sel recursive_calls(1) recursive_calls(2) x_def)
            have output_recursive: "output1 = {(F a1 a2 \<approx> a3), (F a4 a5 \<approx> a6)} \<union> output1'" 
              using explain_along_path_simp3[OF repa_neq_repb Some' recursive_calls(1)[unfolded x_def]]
              by (simp add: "1.hyps" "1.prems"(4))
            have o2: "output2 = {(F a1 a2 \<approx> a3), (F a4 a5 \<approx> a6)} \<union> output2'" 
              using explain_along_path_simp3[OF **(2) Some'[unfolded ***]] ** Some' *** domain 1(8) 
              by auto
            then show ?thesis using * output_recursive 
              using Two True IH Some' by blast
          qed
        next
          case False

          have not_equal: "rep_of l a = proof_forest cc ! k \<Longrightarrow> k \<noteq> proof_forest cc ! rep_of l a"
            (* Otherwise there would be a cycle in the tree *)
          proof
            assume equal: "rep_of l a = proof_forest cc ! k" "k = proof_forest cc ! rep_of l a"
            then have "path (proof_forest cc) (rep_of l a) [rep_of l a, k] k" 
              by (metis "1.prems"(2) "1.prems"(6) False \<open>rep_of l a < length (proof_forest cc)\<close> explain_list_invar_def path.step single)
            moreover have "path (proof_forest cc) k [k, rep_of l a] (rep_of l a)"
              using equal by (metis calculation path.step path_nodes_lt_length_l single)
            ultimately have "path (proof_forest cc) k [k, rep_of l a, k] k" 
              using \<open>proof_forest cc ! rep_of l a \<noteq> rep_of l a\<close> local.equal(2) path.step path_nodes_lt_length_l by blast
            then show False 
              using path_no_cycle "1.prems" proof_forest_invar_def path_nodes_lt_length_l by auto 
          qed

          show ?thesis proof(cases "the ((pf_labels cc) ! rep_of l a)")
            (* CASE One *)
            case (One x1)
            from One have Some: "(pf_labels cc) ! rep_of l a = Some (One x1)" using not_None 
              by auto
            then have IH: "output2' \<supseteq> output1' - pending_equation_to_set (pf_labels cc ! k)
\<and> output2' \<subseteq> output1'" using 
              1 repa_neq_repb x_def One l_upd_invar l_upd_def
              l_upd_def x_def 
              by (metis (no_types, lifting) \<open>path (proof_forest cc) c p1 x\<close> explain_list_invar_def recursive_calls)
            have "output2 = {x1} \<union> output2'" 
              using explain_along_path_simp2 ** Some *** domain 1(8) by simp
            have output_recursive: "output1 = {x1} \<union> output1'" using explain_along_path_simp2 1 recursive_calls repa_neq_repb Some x_def
              by simp


            then obtain k\<^sub>3 k\<^sub>4 where x1: "x1 = (k\<^sub>3 \<approx> k\<^sub>4)"
              "(k\<^sub>3 = proof_forest cc ! rep_of l a
 \<and> k\<^sub>4 = rep_of l a \<or> k\<^sub>3 = rep_of l a \<and> k\<^sub>4 = proof_forest cc ! rep_of l a)"
              using One pf_labels_invar_property by auto
            have pf_labels_invar_property': "\<exists> k\<^sub>1 k\<^sub>2 k\<^sub>3 k\<^sub>4 k\<^sub>5 k\<^sub>6 . (pf_labels cc ! k = Some (One (k\<^sub>1 \<approx> k\<^sub>2))
\<or>  pf_labels cc ! k = Some (Two (F k\<^sub>3 k\<^sub>4 \<approx> k\<^sub>1) (F k\<^sub>5 k\<^sub>6 \<approx> k\<^sub>2)))
          \<and> (k\<^sub>1 = proof_forest cc ! k \<and> k\<^sub>2 = k \<or> k\<^sub>1 = k \<and> k\<^sub>2 = proof_forest cc ! k)
          \<and> valid_vars_pending (the (pf_labels cc ! k)) (cc_list cc)" 
              using pf_labels_invar_def "1.prems"(1,2,6) False explain_list_invar_def 
              by fastforce

            then have "x1 \<notin> pending_equation_to_set (pf_labels cc ! k)"
            proof(cases "the (pf_labels cc ! k)")
              case One': (One x1')
              then obtain k\<^sub>1 k\<^sub>2 where x1': "x1' = (k\<^sub>1 \<approx> k\<^sub>2)"
                "(k\<^sub>1 = proof_forest cc ! k \<and> k\<^sub>2 = k \<or> k\<^sub>1 = k \<and> k\<^sub>2 = proof_forest cc ! k)"
                using pf_labels_invar_property' by auto
              then show ?thesis using x1 x1' False' not_equal
                by (metis False One' equation.inject(1) option.exhaust_sel pending_equation_to_set.simps(2) singletonD)
            next
              case (Two x21' x22')
              then obtain k\<^sub>1 k\<^sub>2 k11 k12 k21 k22
                where x1': "x21' = (F k11 k12 \<approx> k\<^sub>1)" "x22' = (F k21 k22 \<approx> k\<^sub>2)"
                  "(k\<^sub>1 = proof_forest cc ! k \<and> k\<^sub>2 = k \<or> k\<^sub>1 = k \<and> k\<^sub>2 = proof_forest cc ! k)"
                using pf_labels_invar_property' by auto
              then show ?thesis using x1 x1' False' not_equal
                using False Two by force
            qed
            then show ?thesis 
              using IH \<open>output1 = {x1} \<union> output1'\<close> \<open>output2 = {x1} \<union> output2'\<close> by blast
          next
            (* CASE Two *)
            case (Two x21 x22)
            from Two have Some: "(pf_labels cc) ! rep_of l a = Some (Two x21 x22)" using not_None
              by auto
            then obtain a1 a2 a3 a4 a5 a6 where Some': 
              "(pf_labels cc) ! rep_of l a = Some (Two (F a1 a2 \<approx> a3) (F a4 a5 \<approx> a6))"
              using not_None pf_labels_invar_property
              by auto
            then have IH: "output2' \<supseteq> output1' - pending_equation_to_set (pf_labels cc ! k)
\<and> output2' \<subseteq> output1'" using 
              1 repa_neq_repb l_upd_invar 
              unfolding l_upd_def x_def 
              by (metis (no_types, lifting) \<open>\<And>thesis. (\<And>p1. path (proof_forest cc) c p1 x \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> explain_list_invar_def option.sel path_nodes_lt_length_l recursive_calls(1) recursive_calls(2) x_def)
            have output_recursive: "output1 = {(F a1 a2 \<approx> a3), (F a4 a5 \<approx> a6)} \<union> output1'" 
              using explain_along_path_simp3[OF repa_neq_repb Some' recursive_calls(1)[unfolded x_def]]
              by (simp add: "1.hyps" "1.prems"(4))
            have o2: "output2 = {(F a1 a2 \<approx> a3), (F a4 a5 \<approx> a6)} \<union> output2'"
              using explain_along_path_simp3[OF **(2) Some'[unfolded ***]] ** Some' *** domain 1(8) 
              by auto
            then have x1: 
              "(a3 = proof_forest cc ! rep_of l a
 \<and> a6 = rep_of l a \<or> a3 = rep_of l a \<and> a6 = proof_forest cc ! rep_of l a)"
              using Some' pf_labels_invar_property by auto
            have pf_labels_invar_property': "\<exists> k\<^sub>1 k\<^sub>2 k\<^sub>3 k\<^sub>4 k\<^sub>5 k\<^sub>6 . (pf_labels cc ! k = Some (One (k\<^sub>1 \<approx> k\<^sub>2))
\<or>  pf_labels cc ! k = Some (Two (F k\<^sub>3 k\<^sub>4 \<approx> k\<^sub>1) (F k\<^sub>5 k\<^sub>6 \<approx> k\<^sub>2)))
          \<and> (k\<^sub>1 = proof_forest cc ! k \<and> k\<^sub>2 = k \<or> k\<^sub>1 = k \<and> k\<^sub>2 = proof_forest cc ! k)
          \<and> valid_vars_pending (the (pf_labels cc ! k)) (cc_list cc)" 
              using pf_labels_invar_def "1.prems"(1,2,6) False explain_list_invar_def 
              by fastforce

            then have "x21 \<notin> pending_equation_to_set (pf_labels cc ! k)
\<or> x22 \<notin> pending_equation_to_set (pf_labels cc ! k)"
            proof(cases "the (pf_labels cc ! k)")
              case (One x1')
              then obtain k\<^sub>1 k\<^sub>2 where x1': "x1' = (k\<^sub>1 \<approx> k\<^sub>2)"
                "(k\<^sub>1 = proof_forest cc ! k \<and> k\<^sub>2 = k \<or> k\<^sub>1 = k \<and> k\<^sub>2 = proof_forest cc ! k)"
                using pf_labels_invar_property' by auto
              then show ?thesis 
                using False One Two option.exhaust_sel option.sel pending_equation_to_set.simps(2) pf_labels_invar_property singleton_iff valid_vars_pending.simps(4) valid_vars_pending.simps(5) by fastforce
            next
              case Two': (Two x21' x22')
              then obtain k\<^sub>1 k\<^sub>2 k11 k12 k21 k22
                where x1': "x21' = (F k11 k12 \<approx> k\<^sub>1)" "x22' = (F k21 k22 \<approx> k\<^sub>2)"
                  "(k\<^sub>1 = proof_forest cc ! k \<and> k\<^sub>2 = k \<or> k\<^sub>1 = k \<and> k\<^sub>2 = proof_forest cc ! k)"
                using pf_labels_invar_property' by auto
              have pending_set: "pending_equation_to_set (pf_labels cc ! k) = {F k11 k12 \<approx> k\<^sub>1, F k21 k22 \<approx> k\<^sub>2}"
                by (metis False Two' option.exhaust_sel pending_equation_to_set.simps(3) x1'(1) x1'(2))
              have x: "x21 = (F a1 a2 \<approx> a3)" "x22 = (F a4 a5 \<approx> a6)" 
                using Some' Two by fastforce+
              show ?thesis unfolding x pending_set using not_equal x1'(3) x1
                by (metis False' \<open>proof_forest cc ! rep_of l a \<noteq> rep_of l a\<close> equation.inject(2) insert_iff singleton_iff)
            qed
            then show ?thesis 
              using IH output_recursive o2 Some Some' by force
          qed
        qed
      qed
    qed
  qed
qed

lemma explain_along_path_output_new_l:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"

"path (proof_forest cc) c p2' a"

"path (proof_forest cc) c' p' a'"
"explain_along_path cc l a' c' = (output1', new_l', pend1')"

"explain_along_path cc l a c = (output1, new_l1, pend1)"

"explain_along_path cc new_l' a c = (output2, new_l2, pend2)"
shows "output2 \<supseteq> output1 - output1' \<and>
output2 \<subseteq> output1"
proof-
  have "explain_along_path_dom (cc, l, a', c')" using assms explain_along_path_domain 
    by blast
  then show ?thesis using assms proof(induction 
      arbitrary: output1' new_l' pend1' output2 new_l2 pend2 output1 new_l1 pend1 p'
      rule: explain_along_path.pinduct)
    case (1 cc l a' c')
    then show ?case 
    proof(cases "rep_of l a' = rep_of l c'")
      case True
      with 1(8) have "output1' = {}" "new_l' = l" using explain_along_path_simp1 
        by simp+
      then show ?thesis 
        using 1(10,9) by simp
    next
      case False
      define b' where "b' = (proof_forest cc) ! rep_of l a'"
      have invar: "explain_list_invar (l[rep_of l a' := b']) (proof_forest cc)" 
        using explain_list_invar_step proof_forest_invar_def "1.prems" 
        by (metis b'_def explain_list_invar_def path_nodes_lt_length_l)
      obtain p2' where path_to_rep: "path (proof_forest cc) c' p2' b'" 
        using path_to_parent_of_rep_of_l_a_explain_along_path_case_2 "1.prems" b'_def 
        by (metis (no_types, lifting) False explain_list_invar_def path_nodes_lt_length_l)
      obtain p3' where path_to_lca: "path (proof_forest cc) c p3' a"
        using "1.prems" lowest_common_ancestor_correct explain_list_invar_def 
        using proof_forest_invar_def by fastforce
      have not_none: "(pf_labels cc) ! rep_of l a' \<noteq> None" using pf_labels_explain_along_path_case_2 
        using "1.prems"(1,2,4) False explain_list_invar_def path_nodes_lt_length_l by auto
      then show ?thesis 
      proof(cases "the ((pf_labels cc) ! rep_of l a')")
        case (One x1)
        then have Some: "(pf_labels cc) ! rep_of l a' = Some (One x1)"
          using not_none by auto
        then obtain output_rec' new_l_rec' pending_rec' where 
          rec': "(output_rec', new_l_rec', pending_rec') = explain_along_path cc (l[rep_of l a' := b']) b' c'"
          by (metis prod_cases3)
        then have rec: "(output1', new_l', pend1') = ({x1} \<union> output_rec', new_l_rec', pending_rec')"
          using "1.hyps" "1.prems"(5) False Some b'_def explain_along_path_simp2 by auto
        obtain output1_fun_upd new_l1_fun_upd pend1_fun_upd
          output2_fun_upd new_l2_fun_upd pend2_fun_upd
          where rec_alt: "explain_along_path cc (l[rep_of l a' := b']) a c 
                 = (output1_fun_upd, new_l1_fun_upd, pend1_fun_upd)"
            "explain_along_path cc new_l_rec' a c = (output2_fun_upd, new_l2_fun_upd, pend2_fun_upd)"
          using prod_cases3 by metis
        have IH: "output1_fun_upd - output_rec' \<subseteq> output2_fun_upd \<and> output2_fun_upd \<subseteq> output1_fun_upd"
          using 1(2) using "1.prems" rec' rec_alt path_to_rep False b'_def One 1(4-) invar
          by metis
        have pfl_rep_of_a: "pending_equation_to_set (pf_labels cc ! rep_of l a') = {x1}"
          by (simp add: Some)
        have fun_upd: "output1 - pending_equation_to_set (pf_labels cc ! rep_of l a') 
\<subseteq> output1_fun_upd \<and> output1_fun_upd \<subseteq> output1" 
          using explain_along_path_output_fun_upd[OF 1(4,5) path_to_lca 1(9)] 
          by (metis "1.prems"(6) Diff_empty Diff_subset Pair_inject b'_def linorder_le_less_linear list_update_beyond rec_alt(1)) 
        then show ?thesis using IH fun_upd rec pfl_rep_of_a 
          using "1.prems"(7) rec_alt(2) by auto
      next
        case (Two x21 x22)
        then obtain x\<^sub>1 x\<^sub>2 x y\<^sub>1 y\<^sub>2 y where Some: "(pf_labels cc) ! rep_of l a' = 
Some (Two (F x\<^sub>1 x\<^sub>2 \<approx> x) (F y\<^sub>1 y\<^sub>2 \<approx> y))"
          using pf_labels_Two_valid "1.prems" False by metis
        then obtain output_rec' new_l_rec' pending_rec' where 
          rec': "(output_rec', new_l_rec', pending_rec') = explain_along_path cc (l[rep_of l a' := b']) b' c'"
          by (metis prod_cases3)
        then have rec: "(output1', new_l', pend1') = ({(F x\<^sub>1 x\<^sub>2 \<approx> x), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> output_rec', new_l_rec', [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pending_rec')"
          using "1.hyps" "1.prems"(5) False Some b'_def explain_along_path_simp3 by metis
        obtain output1_fun_upd new_l1_fun_upd pend1_fun_upd
          output2_fun_upd new_l2_fun_upd pend2_fun_upd
          where rec_alt: "explain_along_path cc (l[rep_of l a' := b']) a c 
                 = (output1_fun_upd, new_l1_fun_upd, pend1_fun_upd)"
            "explain_along_path cc new_l_rec' a c = (output2_fun_upd, new_l2_fun_upd, pend2_fun_upd)"
          using prod_cases3 by metis
        have IH: "output1_fun_upd - output_rec' \<subseteq> output2_fun_upd \<and> output2_fun_upd \<subseteq> output1_fun_upd"
          using False b'_def 1(4) invar 1(6,7) path_to_rep using "1.prems" rec' rec_alt Some
          by (metis "1.IH"(2) False b'_def invar option.sel path_to_rep)
        have pfl_rep_of_a: "pending_equation_to_set (pf_labels cc ! rep_of l a') = {(F x\<^sub>1 x\<^sub>2 \<approx> x), (F y\<^sub>1 y\<^sub>2 \<approx> y)}"
          by (simp add: Some)
        have fun_upd: "output1 - pending_equation_to_set (pf_labels cc ! rep_of l a') 
\<subseteq> output1_fun_upd \<and> output1_fun_upd \<subseteq> output1" 
          using explain_along_path_output_fun_upd[OF 1(4,5) path_to_lca 1(9)] 
          by (metis "1.prems"(6) Diff_empty Diff_subset Pair_inject b'_def linorder_le_less_linear list_update_beyond rec_alt(1)) 
        then show ?thesis using IH fun_upd rec pfl_rep_of_a 
          using "1.prems"(7) rec_alt(2) by auto
      qed
    qed
  qed
qed

lemma explain_along_path_fun_upd_new_l:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"

"path (proof_forest cc) c p2 a"

"explain_along_path cc l a c = (output1, new_l1, pend1)"

"explain_along_path cc (l[k := proof_forest cc ! k]) a c 
                   = (output1_fun_upd, new_l1_fun_upd, pend1_fun_upd)"

"k < length l"
shows "new_l1_fun_upd = new_l1[k := proof_forest cc ! k]"
  using assms 
proof(induction arbitrary: output1_fun_upd new_l1_fun_upd pend1_fun_upd
    rule: explain_along_path_induct)
  case (base cc l a c p)
  let ?l_upd = "l[k := proof_forest cc ! k]"
  have "rep_of ?l_upd a = rep_of ?l_upd c" using rep_of_fun_upd4 rep_of_fun_upd' using base unfolding explain_list_invar_def 
    by (smt (verit, ccfv_threshold) base.hyps(3) list_update_same_conv path_nodes_lt_length_l rep_of_iff rep_of_next_recursive_step_explain_along_path single)
  with base have "new_l1_fun_upd = l[k := proof_forest cc ! k]"
    by (auto simp add: explain_along_path_simp1)
  then show ?case 
    by blast
next
  case (One cc l a c p1 p2 b x1 x11 x12 output_rec' new_l_rec' pending_rec')
  let ?l_upd = "l[k := proof_forest cc ! k]"
  obtain output_rec_upd' new_l_rec_upd' pending_rec_upd' 
    where 
      rec': 
      "explain_along_path cc (l[rep_of l a := b, k := proof_forest cc ! k]) b c = (output_rec_upd', new_l_rec_upd', pending_rec_upd')"
    by (metis prod_cases3)
  from One(9) have same_l: "l[rep_of l a := b, k := proof_forest cc ! k] = l[k := proof_forest cc ! k, rep_of l a := b]"
    by (metis list_update_swap)

  then have IH: "new_l_rec_upd' = new_l_rec'[k := proof_forest cc ! k]" 
    using One by (metis length_list_update rec')
  then show ?case 
  proof(cases "k = rep_of l a")
    case True
      (* CASE when the edge we add to output is not added in the updated list case *)
      (* the updated list case is equal to the next recursive call of the normal list case *)

    with One(9) have same_l: "l[rep_of l a := b] = l[k := proof_forest cc ! k]"
      "l[rep_of l a := b] = (l[rep_of l a := b, k := (proof_forest cc) ! k])"
      by auto
    then have *: "new_l_rec' = new_l_rec_upd'" 
      using rec' One(7,9) by auto
    have same_rep: "rep_of l b = rep_of (l[rep_of l a := b]) a" 
      using One.prems One.hyps unfolding One(9) explain_list_invar_def 
      by (metis (mono_tags, lifting) One.hyps(3) list_update_same_conv path_nodes_lt_length_l proof_forest_invar_def rep_of_fun_upd_rep_of rep_of_l_a_is_root_in_pf_if_parent_has_same_rep)
    have "new_l1_fun_upd = new_l_rec_upd'" 
    proof(cases "rep_of ?l_upd b = rep_of ?l_upd c")
      (*Case one of the recursive call: base case*)
      case True
      then have 1: "new_l_rec_upd' = l[rep_of l a := b, k := proof_forest cc ! k]" using rec' same_l explain_along_path_simp1 
        by force
      have "rep_of ?l_upd b = rep_of ?l_upd a" using same_rep unfolding One(9)  
        by (metis (no_types, lifting) One.hyps(3) One.hyps(4) One.hyps(5) One.hyps(6) One.hyps(8) One.hyps(9) explain_list_invar_def nth_list_update_eq path_no_root path_nodes_lt_length_l rep_of_bound rep_of_fun_upd' rep_of_min same_l(1))
      then have "new_l1_fun_upd = l[k := proof_forest cc ! k]" using same_l explain_along_path_simp1 same_rep True 
        using One.prems(1) by fastforce
      with 1 show ?thesis using same_l 
        by simp
    next
      case False
        (* Case two of the recursive call *)
      define l_upd where "l_upd = ?l_upd"
      define b2 where "b2 = (proof_forest cc) ! rep_of l_upd b"
      then have invar: "explain_list_invar l_upd (proof_forest cc)" 
        using One.hyps(6) same_l(1) l_upd_def by auto
      then have pfl_not_None: "((pf_labels cc) ! rep_of l_upd b) \<noteq> None" using pf_labels_explain_along_path_case_2 One False
        unfolding b2_def by (metis l_upd_def length_list_update)
      have recursive_calls':  
        "explain_along_path cc l_upd b c = (output_rec_upd', new_l_rec_upd', pending_rec_upd')" 
        using rec' same_l(2) l_upd_def by (simp add: True)
      obtain output12 new_l12 pend12
        where recursive_calls2:
          "(output12, new_l12, pend12) = 
                explain_along_path cc (l_upd[rep_of l_upd b := (proof_forest cc) ! rep_of l_upd b]) b2 c"
        by (metis prod_cases3)
      have domain: "explain_along_path_dom (cc, l_upd, b, c)" using explain_along_path_domain 
        using explain_along_path_domain One.hyps(2) One.hyps(5) \<open>explain_list_invar l_upd (proof_forest cc)\<close> by presburger
      have *: "rep_of l_upd b = rep_of l_upd a"
        unfolding l_upd_def using rep_of_next_recursive_step_explain_along_path One.prems One.hyps
        by (smt (verit) True explain_list_invar_def path_nodes_lt_length_l)
      have two_recursive_calls_same: "explain_along_path cc (l_upd[rep_of l_upd b := (proof_forest cc) ! rep_of l_upd b]) b2 c
= explain_along_path cc (l_upd[rep_of l_upd a := (proof_forest cc) ! rep_of l_upd a]) ((proof_forest cc) ! rep_of l_upd a) c"
        unfolding same_l 
        by (simp add: "*" b2_def)
      have recursive_calls'': "explain_along_path cc l_upd a c = (output1_fun_upd, new_l1_fun_upd, pend1_fun_upd)" 
        using l_upd_def True One.prems(1) by blast
      have prems: "rep_of l_upd a \<noteq> rep_of l_upd c"
        "(output12, new_l12, pend12) =
    explain_along_path cc (l_upd[rep_of l_upd a := proof_forest cc ! rep_of l_upd a]) (proof_forest cc ! rep_of l_upd a) c"
        "explain_along_path_dom (cc, l_upd, a, c)"
        using "*" False l_upd_def apply auto[1]
         apply (simp add: two_recursive_calls_same recursive_calls2)
        using explain_along_path_domain invar One.prems One.hyps by blast
      show ?thesis proof(cases "the ((pf_labels cc) ! rep_of l_upd b)")
        case (One a'2)
          (* Case two of the recursive call: the edge has one label *)
        have **: "pf_labels cc ! rep_of l_upd b = Some (One a'2)" 
          using pfl_not_None One by force
        have prems2: "rep_of l_upd b \<noteq> rep_of l_upd c"
          by (simp add: "*" prems(1))
        then have 1: "new_l_rec_upd' = new_l1_fun_upd" using same_l False 
            recursive_calls2 recursive_calls' domain b2_def False "*" "**" explain_along_path_simp2 prems(3) recursive_calls'' by auto
        have "pf_labels cc ! rep_of l_upd a = Some (One a'2)" by (metis "*" \<open>pf_labels cc ! rep_of l_upd b = Some (One a'2)\<close>)
        then have "new_l1_fun_upd = new_l12" using explain_along_path_simp2 prems
            One.hyps recursive_calls2 recursive_calls'' by force
        then show ?thesis using 1 by simp
      next
        case (Two a'2 b'2)
          (* Case two of the recursive call: the edge has two labels *)
        have Two': "pf_labels cc ! rep_of l_upd b = Some (Two a'2 b'2)" 
          using pfl_not_None Two by force
        then obtain aa bb a1a a2a b1b b2b where "a'2 = (F a1a a2a \<approx> aa)" "b'2 = (F b1b b2b \<approx> bb)"
          and pf_labels_two: "pf_labels cc ! rep_of l_upd b = Some (Two (F a1a a2a \<approx> aa) (F b1b b2b \<approx> bb))"
          using pf_labels_Two_valid 
          by (metis "*" One.hyps(2) One.hyps(5) Two invar pending_equation.inject(2) prems(1) the_state.simps)
        then have 1: "new_l_rec_upd' = new_l12"
          using explain_along_path_simp3[OF False pf_labels_two[unfolded l_upd_def]] 
            recursive_calls2 recursive_calls' domain b2_def False Two' 
          by (metis One.IH One.prems(2) l_upd_def length_list_update rec')
        have "pf_labels cc ! rep_of l_upd a = Some (Two (F a1a a2a \<approx> aa) (F b1b b2b \<approx> bb))" 
          using "*" pf_labels_two by auto
        then have "new_l1_fun_upd = new_l12" 
          by (smt (verit, best) "*" One.IH One.hyps(3) One.hyps(6) One.hyps(9) One.prems(1) One.prems(2) True domain explain_along_path_simp3 explain_list_invar_def l_upd_def prems(1) prems(2) prems(3) same_l(2))
        then show ?thesis using 1 by simp
      qed
    qed
    then show ?thesis using * 
      using IH by blast
  next
    case False': False
      (* CASE when the edge we add to output is also added in the updated list case *)
      (* To show: the new added edge is not equal to the edge k *)
    then have *: "rep_of ?l_upd a \<noteq> rep_of ?l_upd c" 
      using fun_upd_somewhere_else_does_not_join_a_and_c One 
      by (smt (verit, ccfv_SIG) explain_list_invar_def path_nodes_lt_length_l)
    have **: "rep_of l a = rep_of ?l_upd a" using False' 
      by (metis One.hyps(3,4) One.prems(2) explain_list_invar_def list_update_id path_nodes_lt_length_l rep_of_fun_upd' rep_of_refl)
    have dom: "explain_along_path_dom (cc, l[k := proof_forest cc ! k], a, c)" 
      using explain_along_path_domain One.hyps One.hyps(4) One.prems(2) explain_list_invar_fun_upd proof_forest_invar_def by blast
    then have recursive: "new_l1_fun_upd = new_l_rec_upd'"
      using explain_along_path_simp2 rec' One same_l dom 
      by (metis "*" "**" Pair_inject)
    then show ?thesis 
      using IH by blast
  qed
next
  case (Two cc l a c p1 p2 b x21 x22 x21a x22a x23 x21b x22b x23a output_rec' new_l_rec' pending_rec')
    (* TODO this proof is exactly the same as case One *)
  let ?l_upd = "l[k := proof_forest cc ! k]"
  obtain output_rec_upd' new_l_rec_upd' pending_rec_upd' 
    where 
      rec': 
      "explain_along_path cc (l[rep_of l a := b, k := proof_forest cc ! k]) b c = (output_rec_upd', new_l_rec_upd', pending_rec_upd')"
    by (metis prod_cases3)
  from Two(9) have same_l: "l[rep_of l a := b, k := proof_forest cc ! k] = l[k := proof_forest cc ! k, rep_of l a := b]"
    by (metis list_update_swap)

  then have IH: "new_l_rec_upd' = new_l_rec'[k := proof_forest cc ! k]" 
    using Two by (metis length_list_update rec')
  then show ?case 
  proof(cases "k = rep_of l a")
    case True
      (* CASE when the edge we add to output is not added in the updated list case *)
      (* the updated list case is equal to the next recursive call of the normal list case *)

    with Two(9) have same_l: "l[rep_of l a := b] = l[k := proof_forest cc ! k]"
      "l[rep_of l a := b] = (l[rep_of l a := b, k := (proof_forest cc) ! k])"
      by auto
    then have *: "new_l_rec' = new_l_rec_upd'" 
      using rec' Two(7,9) by auto
    have same_rep: "rep_of l b = rep_of (l[rep_of l a := b]) a" 
      using Two.prems Two.hyps unfolding Two(9) explain_list_invar_def 
      by (metis (mono_tags, lifting) Two.hyps(3) list_update_same_conv path_nodes_lt_length_l proof_forest_invar_def rep_of_fun_upd_rep_of rep_of_l_a_is_root_in_pf_if_parent_has_same_rep)
    have "new_l1_fun_upd = new_l_rec_upd'" 
    proof(cases "rep_of ?l_upd b = rep_of ?l_upd c")
      (*Case one of the recursive call: base case*)
      case True
      then have 1: "new_l_rec_upd' = l[rep_of l a := b, k := proof_forest cc ! k]" using rec' same_l explain_along_path_simp1 
        by force
      have "rep_of ?l_upd b = rep_of ?l_upd a" using same_rep Two.hyps(3-9)
        by (metis (no_types, lifting) explain_list_invar_def nth_list_update_eq path_no_root path_nodes_lt_length_l rep_of_bound rep_of_fun_upd' rep_of_min same_l(1))
      then have "new_l1_fun_upd = l[k := proof_forest cc ! k]" using same_l explain_along_path_simp1 same_rep True 
        using Two.prems(1) by fastforce
      with 1 show ?thesis using same_l 
        by simp
    next
      case False
        (* Case two of the recursive call *)
      define l_upd where "l_upd = ?l_upd"
      define b2 where "b2 = (proof_forest cc) ! rep_of l_upd b"
      then have invar: "explain_list_invar l_upd (proof_forest cc)" 
        using Two.hyps(6) same_l(1) l_upd_def by auto
      then have pfl_not_None: "((pf_labels cc) ! rep_of l_upd b) \<noteq> None" using pf_labels_explain_along_path_case_2 Two False
        unfolding b2_def by (metis l_upd_def length_list_update)
      have recursive_calls':  
        "explain_along_path cc l_upd b c = (output_rec_upd', new_l_rec_upd', pending_rec_upd')" 
        using rec' same_l(2) l_upd_def by (simp add: True)
      obtain output12 new_l12 pend12
        where recursive_calls2:
          "(output12, new_l12, pend12) = 
                explain_along_path cc (l_upd[rep_of l_upd b := (proof_forest cc) ! rep_of l_upd b]) b2 c"
        by (metis prod_cases3)
      have domain: "explain_along_path_dom (cc, l_upd, b, c)" using explain_along_path_domain 
        using explain_along_path_domain Two.hyps(2) Two.hyps(5) \<open>explain_list_invar l_upd (proof_forest cc)\<close> by presburger
      have *: "rep_of l_upd b = rep_of l_upd a"
        unfolding l_upd_def using rep_of_next_recursive_step_explain_along_path Two.prems Two.hyps
        by (smt (verit) True explain_list_invar_def path_nodes_lt_length_l)
      have two_recursive_calls_same: "explain_along_path cc (l_upd[rep_of l_upd b := (proof_forest cc) ! rep_of l_upd b]) b2 c
= explain_along_path cc (l_upd[rep_of l_upd a := (proof_forest cc) ! rep_of l_upd a]) ((proof_forest cc) ! rep_of l_upd a) c"
        unfolding same_l 
        by (simp add: "*" b2_def)
      have recursive_calls'': "explain_along_path cc l_upd a c = (output1_fun_upd, new_l1_fun_upd, pend1_fun_upd)" 
        using l_upd_def True Two.prems(1) by blast
      have prems: "rep_of l_upd a \<noteq> rep_of l_upd c"
        "(output12, new_l12, pend12) =
    explain_along_path cc (l_upd[rep_of l_upd a := proof_forest cc ! rep_of l_upd a]) (proof_forest cc ! rep_of l_upd a) c"
        "explain_along_path_dom (cc, l_upd, a, c)"
        using "*" False l_upd_def apply auto[1]
         apply (simp add: two_recursive_calls_same recursive_calls2)
        using explain_along_path_domain invar Two.prems Two.hyps by blast
      show ?thesis proof(cases "the ((pf_labels cc) ! rep_of l_upd b)")
        case (One a'2)
          (* Case two of the recursive call: the edge has one label *)
        have **: "pf_labels cc ! rep_of l_upd b = Some (One a'2)" 
          using pfl_not_None One by force
        have prems2: "rep_of l_upd b \<noteq> rep_of l_upd c"
          by (simp add: "*" prems(1))
        then have 1: "new_l_rec_upd' = new_l1_fun_upd" using same_l False 
            recursive_calls2 recursive_calls' domain b2_def False "*" "**" explain_along_path_simp2 prems(3) recursive_calls'' by auto
        have "pf_labels cc ! rep_of l_upd a = Some (One a'2)" by (metis "*" \<open>pf_labels cc ! rep_of l_upd b = Some (One a'2)\<close>)
        then have "new_l1_fun_upd = new_l12" using explain_along_path_simp2 prems
            Two.hyps recursive_calls2 recursive_calls'' by force
        then show ?thesis using 1 by simp
      next
        case (Two a'2 b'2)
          (* Case two of the recursive call: the edge has two labels *)
        have Two': "pf_labels cc ! rep_of l_upd b = Some (Two a'2 b'2)" 
          using pfl_not_None Two by force
        then obtain aa bb a1a a2a b1b b2b where "a'2 = (F a1a a2a \<approx> aa)" "b'2 = (F b1b b2b \<approx> bb)"
          and pf_labels_two: "pf_labels cc ! rep_of l_upd b = Some (Two (F a1a a2a \<approx> aa) (F b1b b2b \<approx> bb))"
          using pf_labels_Two_valid 
          by (metis "*" Two.hyps(2) Two.hyps(5) Two invar pending_equation.inject(2) prems(1) the_state.simps)
        then have 1: "new_l_rec_upd' = new_l12"
          using explain_along_path_simp3[OF False pf_labels_two[unfolded l_upd_def]] 
            recursive_calls2 recursive_calls' domain b2_def False Two' 
          by (metis Two.IH Two.prems(2) l_upd_def length_list_update rec')
        have "pf_labels cc ! rep_of l_upd a = Some (Two (F a1a a2a \<approx> aa) (F b1b b2b \<approx> bb))" 
          using "*" pf_labels_two by auto
        then have "new_l1_fun_upd = new_l12" 
          by (smt (verit, best) "*" Two.IH Two.hyps(3,6,9) Two.prems(1) Two.prems(2) True domain explain_along_path_simp3 explain_list_invar_def l_upd_def prems(1) prems(2) prems(3) same_l(2))
        then show ?thesis using 1 by simp
      qed
    qed
    then show ?thesis using * 
      using IH by blast
  next
    case False': False
      (* CASE when the edge we add to output is also added in the updated list case *)
      (* To show: the new added edge is not equal to the edge k *)
    then have *: "rep_of ?l_upd a \<noteq> rep_of ?l_upd c" 
      using fun_upd_somewhere_else_does_not_join_a_and_c Two 
      by (smt (verit, ccfv_SIG) explain_list_invar_def path_nodes_lt_length_l)
    have **: "rep_of l a = rep_of ?l_upd a" using False' 
      by (metis Two.hyps(3,4) Two.prems(2) explain_list_invar_def list_update_id path_nodes_lt_length_l rep_of_fun_upd' rep_of_refl)
    have dom: "explain_along_path_dom (cc, l[k := proof_forest cc ! k], a, c)" 
      using explain_along_path_domain Two.hyps Two.hyps(4) Two.prems(2) explain_list_invar_fun_upd proof_forest_invar_def by blast
    then have recursive: "new_l1_fun_upd = new_l_rec_upd'"
      using explain_along_path_simp3 rec' Two same_l dom
      by (metis "*" "**" Pair_inject)
    then show ?thesis 
      using IH by blast
  qed
qed 

lemma explain_along_path_output2_new_l:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"

"rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
"c = lowest_common_ancestor (proof_forest cc) a b"
"a < length l" "b < length l"

"path (proof_forest cc) c' p2' a'"

"explain_along_path cc l a' c' = (output1', new_l', pend1')"

"explain_along_path cc l a c = (output1, new_l1, pend1)"
"explain_along_path cc new_l1 b c = (output12, new_l12, pend12)"

"explain_along_path cc new_l' a c = (output2, new_l2, pend2)"
"explain_along_path cc new_l2 b c = (output22, new_l22, pend22)"

"k < length l"
shows "output22 \<supseteq> output12 - output1' \<and>
output22 \<subseteq> output12"
proof-
  have "explain_along_path_dom (cc, l, a', c')" using assms explain_along_path_domain 
    by blast
  then show ?thesis using assms proof(induction 
      arbitrary: output1' new_l' pend1' output2 new_l2 pend2 output1 new_l1 pend1 p2'
      output12 new_l12 pend12 output22 new_l22 pend22
      rule: explain_along_path.pinduct)
    case (1 cc l a' c')
    then show ?case 
    proof(cases "rep_of l a' = rep_of l c'")
      case True
      with 1(11) have "output1' = {}" "new_l' = l" using explain_along_path_simp1 
        by simp+
      then show ?thesis 
        using 1 by simp
    next
      case False
      define b' where "b' = (proof_forest cc) ! rep_of l a'"
      have invar: "explain_list_invar (l[rep_of l a' := b']) (proof_forest cc)" 
        "rep_of l a' < length l"
        "explain_list_invar new_l1 (proof_forest cc)" 
        using explain_list_invar_step proof_forest_invar_def "1.prems" 
          apply (metis b'_def explain_list_invar_def path_nodes_lt_length_l)
         apply (metis "1.prems"(2) "1.prems"(7) explain_list_invar_def path_nodes_lt_length_l rep_of_bound)
        using "1.prems" explain_list_invar_explain_along_path'' by blast
      obtain p2' where path_to_rep: "path (proof_forest cc) c' p2' b'" 
        using path_to_parent_of_rep_of_l_a_explain_along_path_case_2 "1.prems" b'_def 
        by (metis (no_types, lifting) False explain_list_invar_def path_nodes_lt_length_l)
      obtain p3' p4' where path_to_lca: "path (proof_forest cc) c p3' a"
        "path (proof_forest cc) c p4' b"
        using "1.prems" lowest_common_ancestor_correct explain_list_invar_def 
        using proof_forest_invar_def by fastforce
      have not_none: "(pf_labels cc) ! rep_of l a' \<noteq> None" using pf_labels_explain_along_path_case_2 
        using "1.prems" False explain_list_invar_def path_nodes_lt_length_l by auto
      then obtain output_rec' new_l_rec' pending_rec' 
        where 
          rec': "explain_along_path cc (l[rep_of l a' := b']) b' c' = (output_rec', new_l_rec', pending_rec')"
        by (metis prod_cases3)
      obtain output1_fun_upd new_l1_fun_upd pend1_fun_upd
        output2_fun_upd new_l2_fun_upd pend2_fun_upd
        output1_fun_upd2 new_l1_fun_upd2 pend1_fun_upd2
        output2_fun_upd2 new_l2_fun_upd2 pend2_fun_upd2
        where rec_alt: "explain_along_path cc (l[rep_of l a' := b']) a c 
                 = (output1_fun_upd, new_l1_fun_upd, pend1_fun_upd)"
          "explain_along_path cc new_l1_fun_upd b c 
                 = (output1_fun_upd2, new_l1_fun_upd2, pend1_fun_upd2)"
          "explain_along_path cc new_l_rec' a c = (output2_fun_upd, new_l2_fun_upd, pend2_fun_upd)"
          "explain_along_path cc new_l2_fun_upd b c = (output2_fun_upd2, new_l2_fun_upd2, pend2_fun_upd2)"
        using prod_cases3 by metis
      have new_l_fun_upd: "new_l1_fun_upd = new_l1[rep_of l a' := b']" 
        using explain_along_path_fun_upd_new_l "1.prems"(1,2,9) b'_def invar(2) path_to_lca(1) rec_alt(1) by blast
      then have fun_upd: "output12 - pending_equation_to_set (pf_labels cc ! rep_of l a') 
\<subseteq> output1_fun_upd2 \<and> output1_fun_upd2 \<subseteq> output12" 
        using explain_along_path_output_fun_upd[OF "1.prems"(1) invar(3) path_to_lca(2)] using invar
        by (metis (mono_tags, lifting) "1.prems"(10) "1.prems"(2) b'_def explain_list_invar_def rec_alt(2))
      then show ?thesis
      proof(cases "the ((pf_labels cc) ! rep_of l a')")
        case (One x1)
        then have Some: "(pf_labels cc) ! rep_of l a' = Some (One x1)"
          using not_none by auto
        have IH: "output1_fun_upd2 - output_rec' \<subseteq> output2_fun_upd2 \<and> output2_fun_upd2 \<subseteq> output1_fun_upd2"
          using 1(2)[OF False b'_def One 1(4) invar(1) 1(6,7) _ _ path_to_rep rec' rec_alt] 
          by (simp add: "1.prems"(13,5,6))
        have pfl_rep_of_a: "pending_equation_to_set (pf_labels cc ! rep_of l a') = {x1}"
          by (simp add: Some)
        then have rec: "(output1', new_l', pend1') = ({x1} \<union> output_rec', new_l_rec', pending_rec')"
          using "1.hyps" "1.prems" False Some b'_def explain_along_path_simp2 
          by (metis rec')
        then show ?thesis using IH fun_upd rec pfl_rep_of_a 
          using "1.prems"(11) "1.prems"(12) rec_alt(3) rec_alt(4) by auto
      next
        case (Two x21 x22)
        then obtain x\<^sub>1 x\<^sub>2 x y\<^sub>1 y\<^sub>2 y where Some: "(pf_labels cc) ! rep_of l a' = 
Some (Two (F x\<^sub>1 x\<^sub>2 \<approx> x) (F y\<^sub>1 y\<^sub>2 \<approx> y))"
          using pf_labels_Two_valid "1.prems" False by meson
        then have rec: "(output1', new_l', pend1') = ({(F x\<^sub>1 x\<^sub>2 \<approx> x), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> output_rec', new_l_rec', [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pending_rec')"
          using "1.hyps" "1.prems" False Some b'_def explain_along_path_simp3 rec' by metis
        have IH: "output1_fun_upd2 - output_rec' \<subseteq> output2_fun_upd2 \<and> output2_fun_upd2 \<subseteq> output1_fun_upd2"
          using "1.prems" rec' rec_alt Some
          by (metis (no_types, lifting) "1.IH"(2) False b'_def invar(1) length_list_update option.sel path_to_rep)
        have pfl_rep_of_a: "pending_equation_to_set (pf_labels cc ! rep_of l a') = {(F x\<^sub>1 x\<^sub>2 \<approx> x), (F y\<^sub>1 y\<^sub>2 \<approx> y)}"
          by (simp add: Some)
        then show ?thesis using IH fun_upd rec pfl_rep_of_a 
          by (metis (no_types, lifting) "1.prems"(11) "1.prems"(12) Pair_inject Un_Diff le_iff_sup rec_alt(3) rec_alt(4) set_diff_diff_left sup_assoc)
      qed
    qed
  qed
qed

lemma explain_along_path_output_new_new_l:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"

"path (proof_forest cc) c p2' a"

"rep_of (proof_forest cc) a' = rep_of (proof_forest cc) b'"
"c' = lowest_common_ancestor (proof_forest cc) a' b'"
"a' < length l" "b' < length l"

"explain_along_path cc l a' c' = (output1', new_l', pend1')"
"explain_along_path cc new_l' b' c' = (output2', new_new_l', pend2')"

"explain_along_path cc l a c = (output1, new_l1, pend1)"

"explain_along_path cc new_new_l' a c = (output2, new_l2, pend2)"

"k < length l"
shows "output2 \<supseteq> output1 - output1' - output2' \<and>
output2 \<subseteq> output1"
proof-
  obtain p1 where p1: "path (proof_forest cc) c' p1 a'" 
    using lowest_common_ancestor_correct assms explain_list_invar_def 
    using proof_forest_invar_def by force
  obtain output2_int new_l2_int pend2_int where
    rec_int: "explain_along_path cc new_l' a c = (output2_int, new_l2_int, pend2_int)"
    using prod_cases3 by blast
  then have 1: "output2_int \<supseteq> output1 - output1' \<and> output2_int \<subseteq> output1"
    using explain_along_path_output_new_l assms p1 rec_int 
    by simp  
  have "explain_list_invar new_l' (proof_forest cc)" 
    using explain_list_invar_explain_along_path'' assms 
    by blast
  obtain p2 where p2: "path (proof_forest cc) c' p2 b'" 
    using lowest_common_ancestor_correct assms explain_list_invar_def 
    using proof_forest_invar_def by force
  then have 2: "output2 \<supseteq> output2_int - output2' \<and> output2 \<subseteq> output2_int"
    using explain_along_path_output_new_l assms
    by (metis (no_types, lifting) \<open>explain_list_invar new_l' (proof_forest cc)\<close> length_explain_list_cc_list rec_int)
  then show ?thesis using 1 2 
    by fast
qed

lemma explain_along_path_output2_new_new_l:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"

"rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
"c = lowest_common_ancestor (proof_forest cc) a b"
"a < length l" "b < length l"

"rep_of (proof_forest cc) a' = rep_of (proof_forest cc) b'"
"c' = lowest_common_ancestor (proof_forest cc) a' b'"
"a' < length l" "b' < length l"

"explain_along_path cc l a' c' = (output1', new_l', pend1')"
"explain_along_path cc new_l' b' c' = (output2', new_new_l', pend2')"

"explain_along_path cc l a c = (output1, new_l1, pend1)"
"explain_along_path cc new_l1 b c = (output12, new_l12, pend12)"

"explain_along_path cc new_new_l' a c = (output2, new_l2, pend2)"
"explain_along_path cc new_l2 b c = (output22, new_l22, pend22)"

"k < length l"
shows "output22 \<supseteq> output12 - output1' - output2' \<and>
output22 \<subseteq> output12"
proof-
  obtain p1 where p1: "path (proof_forest cc) c p1 a" 
    using lowest_common_ancestor_correct assms explain_list_invar_def 
    using proof_forest_invar_def by force
  obtain p2 p3 p4 where p2: "path (proof_forest cc) c p2 b" "path (proof_forest cc) c' p3 a'" 
    "path (proof_forest cc) c' p4 b'" 
    using lowest_common_ancestor_correct assms explain_list_invar_def 
    using proof_forest_invar_def by force
  have invar: "explain_list_invar new_l1 (proof_forest cc)" 
    "explain_list_invar new_l' (proof_forest cc)"
    "length new_l' = length l"
    using explain_list_invar_explain_along_path 
    using assms explain_list_invar_explain_along_path'' apply blast+
    using assms by (metis explain_list_invar_explain_along_path'' length_explain_list_cc_list)
  obtain output2_int new_l2_int pend2_int output22_int new_l22_int pend22_int where
    rec_int: "explain_along_path cc new_l' a c = (output2_int, new_l2_int, pend2_int)"
    "explain_along_path cc new_l2_int b c = (output22_int, new_l22_int, pend22_int)"
    using prod_cases3 by metis
  then have 2: "output22_int \<supseteq> output12 - output1' \<and> output22_int \<subseteq> output12"
    using explain_along_path_output2_new_l[OF assms(1-6) p2(2) assms(11,13,14) rec_int] assms
    by blast
  then have 3: "output22 \<supseteq> output22_int - output2' \<and> output22 \<subseteq> output22_int"
    using explain_along_path_output2_new_l[OF assms(1) invar(2) assms(3,4)
        _ _ p2(3) assms(12) rec_int assms(15,16)] assms(6,5) invar(3)
    by simp
  then show ?thesis using 2 3
    by blast
qed

text \<open>Das sind die letzen zwei lemmata die ich brauche um \<open>cc_explain_aux_app\<close> zu beweisen.\<close>
lemma cc_explain_new_l:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set ys1 . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ys2 . a < nr_vars cc \<and> b < nr_vars cc"

"rep_of (proof_forest cc) a' = rep_of (proof_forest cc) b'"
"c' = lowest_common_ancestor (proof_forest cc) a' b'"
"a' < length l" "b' < length l"

"explain_along_path cc l a' c' = (output1', new_l', pend1')"
"explain_along_path cc new_l' b' c' = (output2', new_new_l', pend2')"

"subseq ys2 ys1"
shows
  "cc_explain_aux cc new_new_l' ys2 \<subseteq> cc_explain_aux cc l ys1"
proof-
  have dom: "cc_explain_aux_dom (cc, l, ys1)"
    using cc_explain_aux_domain assms by blast
  show ?thesis 
    using dom assms proof(induction 
      arbitrary: output1' new_l' pend1' output2' new_new_l' pend2' ys2 
      rule: cc_explain_aux.pinduct)
    case (1 cc l)
    have "cc_explain_aux cc new_new_l' [] = {}" 
      by (simp add: cc_explain_aux_simp1)
    moreover have "cc_explain_aux cc l [] = {}" 
      by (simp add: cc_explain_aux_simp1)
    moreover have "ys2 = []" using 1 
      using list_emb_Nil2 by auto
    ultimately show ?case 
      by simp
  next
    case (2 cc l a b xs)
    have "explain_list_invar new_l' (proof_forest cc)" 
      using explain_list_invar_explain_along_path'' 2 
      by metis
    then have invar2': "explain_list_invar new_new_l' (proof_forest cc)" 
      using explain_list_invar_explain_along_path''' "2.prems" 
      by blast
    then have dom: "cc_explain_aux_dom (cc, l, (a,b) # xs)"
      "cc_explain_aux_dom (cc, new_new_l', ys2)"
      using cc_explain_aux_domain 2 apply metis
      using cc_explain_aux_domain 2 \<open>explain_list_invar new_new_l' (proof_forest cc)\<close> by presburger
    have in_bounds: "a < nr_vars cc" "b < nr_vars cc" 
      using 2 by auto
    then show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      then have same_rep: "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
        using 2 in_bounds True are_congruent_rep_of(2) by presburger
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"

      obtain output1_eap new_l_eap pending1_eap output2_eap new_new_l_eap pending2_eap
        where eap: "(output1_eap, new_l_eap, pending1_eap) = explain_along_path cc l a c" 
          "(output2_eap, new_new_l_eap, pending2_eap) = explain_along_path cc new_l_eap b c"
        by (metis prod_cases3)


      obtain a2 b2 ys2' where ys2: "ys2 = (a2, b2) # ys2'" 
        "a2 < nr_vars cc" "b2 < nr_vars cc"  
        using "2.prems"(4,11) sorry
      then have subseq0: "subseq ys2' xs" 
        by (metis "2.prems"(11) subseq_Cons' subseq_Cons2_iff)
      have "a = a2" using "2.prems"(11) ys2(1) list_emb.intros sorry
      define c2 where "c2 = lowest_common_ancestor (proof_forest cc) a2 b2"
      then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" 
        "path (proof_forest cc) c p2 b"  
        using 2 in_bounds explain_along_path_lowest_common_ancestor 
        by (metis True c_def)

      have "explain_along_path_dom (cc, l, a, c)" 
        using explain_along_path_domain 2 p by presburger
      then show ?thesis proof(cases "are_congruent cc (a2 \<approx> b2)")
        case True': True
        obtain output_eap2 new_l_eap2 pend_eap2 output2_eap2 new_new_l_eap2 pend2_eap2
          where eap2: "(output_eap2, new_l_eap2, pend_eap2) = explain_along_path cc new_new_l' a2 c2" 
            "(output2_eap2, new_new_l_eap2, pend2_eap2) = explain_along_path cc new_l_eap2 b2 c2"
          by (metis prod_cases3)
        have *: "length l = length new_new_l_eap2"
          "length new_new_l' = length l" "length l = length new_l_eap2" "length l = nr_vars cc"
          "length l = length new_new_l_eap" 
          sorry

        then have "explain_list_invar new_l_eap2 (proof_forest cc)" 
          using explain_list_invar_explain_along_path''[OF "2.prems"(1) invar2' _ _ _ c2_def eap2(1)[symmetric]] True
            *(2,4) in_bounds(1) in_bounds(2) True' ys2(2) ys2(3) by presburger
        then have invar2'': "explain_list_invar new_new_l_eap2 (proof_forest cc)" 
          using explain_list_invar_explain_along_path''' "2.prems" 
          by (metis "*"(2) "*"(4) True' c2_def eap2(1) eap2(2) ys2(2) ys2(3))
        then have in_bounds2: "\<forall>a\<in>set (pend_eap2 @ pend2_eap2 @ ys2').
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
          using explain_along_path_pending_in_bounds2[OF "2.prems"(1) invar2'(1) _ _ _ True' c2_def eap2]
          by (metis "2.prems"(4) list.set_intros(2) ys2(1) ys2(2) ys2(3))


        then have bounds1: "\<forall>(a, b)\<in>set (pending1_eap @ pending2_eap @ xs) . a < nr_vars cc \<and> b < nr_vars cc"
          using explain_along_path_pending_in_bounds2[OF 2(4,5,6) _ _ True c_def eap] ys2 eap "2.prems"(3)
          by simp
        then have invar1: "explain_list_invar new_l_eap (proof_forest cc)" 
          using eap 
            explain_list_invar_explain_along_path'' 
          by (metis "*"(4) "2.prems"(1) "2.prems"(2) True c_def in_bounds(1) in_bounds(2))
        then have invar2: "explain_list_invar new_new_l_eap (proof_forest cc)" 
          using eap explain_list_invar_explain_along_path''' 
          by (metis "*"(4) "2.prems"(1) "2.prems"(2) True c_def in_bounds(1) in_bounds(2))
        have same_length: "length l = length new_new_l'" 
          using "2.prems"(2) \<open>explain_list_invar new_new_l' (proof_forest cc)\<close> explain_list_invar_def by fastforce



        have subseq1: "subseq pend_eap2 pending1_eap" sorry
        have subseq2: "subseq pend2_eap2 pending2_eap" sorry
        obtain output1_eap3 new_l_eap3 pending1_eap3 output2_eap3 new_new_l_eap3 pending2_eap3
          where eap3: "(output1_eap3, new_l_eap3, pending1_eap3) = explain_along_path cc new_new_l_eap a' c'" 
            "(output2_eap3, new_new_l_eap3, pending2_eap3) = explain_along_path cc new_l_eap3 b' c'"
          by (metis prod_cases3)

        then have IH: "cc_explain_aux cc new_new_l_eap3 (pend_eap2 @ pend2_eap2 @ ys2') 
\<subseteq> cc_explain_aux cc new_new_l_eap (pending1_eap @ pending2_eap @ xs)"
          using  2(2)[OF True c_def _ _ _ _ _ _ "2.prems"(1) invar2 bounds1 _ "2.prems"(5,6)
              _ _ eap3[symmetric]] 
          by (metis "*"(5) "2.prems"(7) "2.prems"(8) eap(1) eap(2) in_bounds2 list_emb_append_mono subseq0 subseq1 subseq2)       

        have recursive_call1: "cc_explain_aux cc new_new_l' ys2 =
 output_eap2 \<union> output2_eap2 \<union> cc_explain_aux cc new_new_l_eap2 (pend_eap2 @ pend2_eap2 @ ys2')"
          using cc_explain_aux_simp2[OF _ c2_def True' eap2] dom(2) ys2 
          by auto
        have recursive_call2: "cc_explain_aux cc l ((a,b) # xs) =
output1_eap \<union> output2_eap \<union> cc_explain_aux cc new_new_l_eap (pending1_eap @ pending2_eap @ xs)"
          using cc_explain_aux_simp2[OF _ c_def True eap] dom(1) ys2(1) by auto


        have "output2_eap2 \<subseteq> output2_eap" 
          using explain_along_path_output_new_new_l[OF 2(4,5)] sorry

        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry
      qed
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed

lemma cc_explain_new_l_part_2:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set ys . a < nr_vars cc \<and> b < nr_vars cc"

"rep_of (proof_forest cc) a' = rep_of (proof_forest cc) b'"
"c' = lowest_common_ancestor (proof_forest cc) a' b'"
"a' < length l" "b' < length l"

"explain_along_path cc l a' c' = (output1', new_l', pend1')"
"explain_along_path cc new_l' b' c' = (output2', new_new_l', pend2')"

"set ys1 \<supseteq> set ys2"
shows
  "cc_explain_aux cc new_new_l' ys1 \<union> output1' \<union> output2' \<supseteq> cc_explain_aux cc l ys2"
proof-
  have dom: "cc_explain_aux_dom (cc, l , ys)"
    using cc_explain_aux_domain assms by blast
  show ?thesis 
    using dom assms proof(induction 
      arbitrary: output1' new_l' pend1' output2' new_new_l' pend2'
      rule: cc_explain_aux.pinduct)
    case (1 cc l)
    have "cc_explain_aux cc new_new_l' [] = {}" 
      by (simp add: cc_explain_aux_simp1)
    moreover have "cc_explain_aux cc l [] = {}" 
      by (simp add: cc_explain_aux_simp1)
    ultimately show ?case 
      sorry
  next
    case (2 cc l a b xs)
    have "explain_list_invar new_l' (proof_forest cc)" 
      using explain_list_invar_explain_along_path'' 2 
      by metis
    then have "explain_list_invar new_new_l' (proof_forest cc)" 
      using explain_list_invar_explain_along_path''' "2.prems" 
      by blast
    then have dom: "cc_explain_aux_dom (cc, l, (((a,b) # xs)))"
      "cc_explain_aux_dom (cc, new_new_l', (((a,b) # xs)))"
      using cc_explain_aux_domain 2 apply blast
      using cc_explain_aux_domain 2 \<open>explain_list_invar new_new_l' (proof_forest cc)\<close> by presburger
    have in_bounds: "a < nr_vars cc" "b < nr_vars cc" 
      using 2 by auto
    then show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      then have same_rep: "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
        using 2 in_bounds True are_congruent_rep_of(2) by presburger
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"
      obtain output1_eap new_l_eap pending1_eap output2_eap new_new_l_eap pending2_eap
        where eap: "(output1_eap, new_l_eap, pending1_eap) = explain_along_path cc l a c" 
          "(output2_eap, new_new_l_eap, pending2_eap) = explain_along_path cc new_l_eap b c"
        by (metis prod_cases3)
      then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" 
        "path (proof_forest cc) c p2 b"  
        using 2 in_bounds explain_along_path_lowest_common_ancestor 
        by (metis True c_def)
      then have bounds1: "\<forall>(a, b)\<in>set pending1_eap. a < nr_vars cc \<and> b < nr_vars cc"
        using explain_along_path_pending_in_bounds 2 eap  
        by (metis snd_conv)
      have "explain_along_path_dom (cc, l, a, c)" 
        using explain_along_path_domain 2 p by presburger
      then have invar1: "explain_list_invar new_l_eap (proof_forest cc)" 
        using eap 
          explain_list_invar_explain_along_path' 
        by (metis "2.prems"(1,2) in_bounds(1) p(1))
      then have invar2: "explain_list_invar new_new_l_eap (proof_forest cc)" 
        using eap 
          explain_list_invar_explain_along_path' 
        by (metis "2.prems"(1) explain_along_path_domain in_bounds(2) p(2))
      from invar1 have "\<forall>(a, b)\<in>set pending2_eap. a < nr_vars cc \<and> b < nr_vars cc"
        using explain_along_path_pending_in_bounds 2 eap snd_conv 
        by (metis p(2))
      then have in_bounds2: "\<forall>a\<in>set (pending1_eap @ pending2_eap @ xs).
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
        using bounds1 2 by auto
      have same_length: "length l = length new_new_l'" 
        using "2.prems"(2) \<open>explain_list_invar new_new_l' (proof_forest cc)\<close> explain_list_invar_def by fastforce

      obtain output_eap2 new_l_eap2 pend_eap2 output2_eap2 new_new_l_eap2 pend2_eap2 
        where eap2: "(output_eap2, new_l_eap2, pend_eap2) = explain_along_path cc new_new_l' a c" 
          "(output2_eap2, new_new_l_eap2, pend2_eap2) = explain_along_path cc new_l_eap2 b c"
        by (metis prod_cases3)
      have "cc_explain_aux cc l ((a, b) # xs) = 
output1_eap \<union> output2_eap \<union> cc_explain_aux cc new_new_l_eap (pending1_eap @ pending2_eap @ xs)"
        using cc_explain_aux_simp2[OF 2(1) c_def True eap] by blast
      have "cc_explain_aux cc new_new_l' ((a, b) # xs) = 
 output_eap2 \<union> output2_eap2 \<union> cc_explain_aux cc new_new_l_eap2 (pend_eap2 @ pend2_eap2 @ xs)"
        using cc_explain_aux_simp2[OF dom(2) c_def True eap2] by blast
      have IH: "cc_explain_aux cc new_new_l' (pending1_eap @ pending2_eap @ xs) \<subseteq> cc_explain_aux cc new_new_l' (pending1_eap @ pending2_eap @ xs) \<and>
    cc_explain_aux cc new_new_l' (pending1_eap @ pending2_eap @ xs) \<subseteq> cc_explain_aux cc new_new_l' (pending1_eap @ pending2_eap @ xs) \<union> output_eap2 \<union> output2_eap2"
        using 2(2)[OF True c_def _ _ _ _ _ _ "2.prems"(1)] eap 2  eap2 same_length 2

        sorry

      have "output2_eap2 \<supseteq> output2' - output1_eap - output2_eap \<and>
output2_eap2 \<subseteq> output2_eap" 
        using explain_along_path_output_new_new_l[OF 2(4,5)] sorry

      then show ?thesis using IH sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed

lemma cc_explain_new_new_l:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set ys . a < nr_vars cc \<and> b < nr_vars cc"

"a' < length l" "b' < length l"
"rep_of (proof_forest cc) a' = rep_of (proof_forest cc) b'"
"c' = lowest_common_ancestor (proof_forest cc) a' b'"
"explain_along_path cc l a' c' = (output', new_l', pend')"
"explain_along_path cc new_l' b' c' = (output2', new_new_l', pend2')"
shows
  "cc_explain_aux cc new_new_l' ys \<subseteq> cc_explain_aux cc l ys \<and>
cc_explain_aux cc new_new_l' ys \<union> output' \<union> output2' \<supseteq> cc_explain_aux cc l ys"
  using assms cc_explain_new_l cc_explain_new_l_part_2
  by auto

theorem cc_explain_aux_app:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ys . a < nr_vars cc \<and> b < nr_vars cc"
  shows "cc_explain_aux cc l (xs @ ys) = cc_explain_aux cc l xs \<union> cc_explain_aux cc l ys"
proof-
  have dom: "cc_explain_aux_dom (cc, l, xs)"
    using assms cc_explain_aux_domain by presburger
  then show ?thesis
    using assms proof(induction rule: cc_explain_aux.pinduct)
    case (1 cc l)
    then show ?case
      using cc_explain_aux.psimps by auto
  next
    case (2 cc l a b xs)
    then have "\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc" 
      by auto
    have " \<forall>(a, b)\<in>set (((a,b) # xs) @ ys). a < nr_vars cc \<and> b < nr_vars cc"
      using 2 by auto
    then have dom: "cc_explain_aux_dom (cc, l, (((a,b) # xs) @ ys))"
      "cc_explain_aux_dom (cc, l, ((a, b) # xs))"
      using cc_explain_aux_domain 2 by blast+
    have in_bounds: "a < nr_vars cc" "b < nr_vars cc" "a < length l" "b < length l" 
      using 2 unfolding explain_list_invar_def same_length_invar_def by auto
    then show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      then have same_rep: "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
        using 2 in_bounds True are_congruent_rep_of(2) by presburger
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"
      obtain output1 new_l pending1 output2 new_new_l pending2 
        where eap: "(output1, new_l, pending1) = explain_along_path cc l a c" 
          "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
        by (metis prod_cases3)
      then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" 
        "path (proof_forest cc) c p2 b"  
        using 2 in_bounds explain_along_path_lowest_common_ancestor 
        by (metis True c_def)
      then have bounds1: "\<forall>(a, b)\<in>set pending1. a < nr_vars cc \<and> b < nr_vars cc"
        using explain_along_path_pending_in_bounds 2 eap  
        by (metis snd_conv)
      have "explain_along_path_dom (cc, l, a, c)" 
        using explain_along_path_domain 2 p 
        by blast
      then have invar1: "explain_list_invar new_l (proof_forest cc)" 
        using eap 
          explain_list_invar_explain_along_path' 
        by (metis "2.prems"(1,2) in_bounds(1) p(1))
      then have invar2: "explain_list_invar new_new_l (proof_forest cc)" 
        using eap 
          explain_list_invar_explain_along_path' 
        by (metis "2.prems"(1) explain_along_path_domain in_bounds(2) p(2))
      from invar1 have "\<forall>(a, b)\<in>set pending2. a < nr_vars cc \<and> b < nr_vars cc"
        using explain_along_path_pending_in_bounds 2 eap snd_conv 
        by (metis p(2))
      then have in_bounds2: "\<forall>a\<in>set (pending1 @ pending2 @ xs).
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall>a\<in>set ys.
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
        using bounds1 2 by auto
      have *: "cc_explain_aux cc new_new_l ys \<subseteq> cc_explain_aux cc l ys"
        "cc_explain_aux cc new_new_l ys \<union> output1 \<union> output2 \<supseteq> cc_explain_aux cc l ys"
        using cc_explain_new_new_l[OF "2.prems"(1,2,4) in_bounds(3,4) same_rep]
        by (metis c_def eap(1) eap(2))+
      have "cc_explain_aux cc l (((a, b) # xs) @ ys) = 
output1 \<union> output2 \<union> cc_explain_aux cc new_new_l (pending1 @ pending2 @ xs @ ys)"
        using cc_explain_aux_simp2 c_def True eap dom
        by auto

      also have "... = output1 \<union> output2 \<union> cc_explain_aux cc new_new_l (pending1 @ pending2 @ xs) 
\<union> cc_explain_aux cc new_new_l ys"
        using 2 c_def eap invar2 in_bounds2 True by auto
      also have "... = cc_explain_aux cc l ((a, b) # xs) \<union> cc_explain_aux cc new_new_l ys"
        using True c_def cc_explain_aux_simp2 dom(2) eap
        by simp
      also have "... = cc_explain_aux cc l ((a, b) # xs) \<union> cc_explain_aux cc l ys" 
        using 2 * True c_def cc_explain_aux_simp2 eap(1) eap(2) sup_commute by auto
      finally show ?thesis 
        by simp
    next
      case False
      then have "cc_explain_aux cc l (((a, b) # xs) @ ys) = cc_explain_aux cc l (xs @ ys)"
        using cc_explain_aux_simp3 dom by auto
      then show ?thesis 
        using False 2 cc_explain_aux_simp3 dom(2) 
        using \<open>\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc\<close> by presburger
    qed
  qed
qed

lemma cc_explain_aux_Cons:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "a < nr_vars cc" "b < nr_vars cc"
  shows "cc_explain_aux cc l ((a,b) # xs) = cc_explain_aux cc l [(a,b)] \<union> cc_explain_aux cc l xs"
proof-
  have *:"\<forall> (a, b) \<in> set [(a,b)] . a < nr_vars cc \<and> b < nr_vars cc"
    using assms by simp
  then show ?thesis 
    using cc_explain_aux_app[OF assms(1-2) * assms(3)] assms by simp
qed

abbreviation cc_invar_reduced :: "congruence_closure \<Rightarrow> bool"
  where
    "cc_invar_reduced cc \<equiv> (((((((((cc_list_invar cc)) 
        \<and> proof_forest_invar cc)) \<and> same_eq_classes_invar cc) 
        \<and> same_length_invar cc (nr_vars cc)))))"

lemma cc_explain_correctness_invar_fun_upd:
  assumes "cc_invar_reduced \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr>" 
    "cc_explain_correctness_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "cc_explain_correctness_invar ?base")
    "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr>"
    "explain_list_invar la (pf[e := e'])"
    "\<forall>(aa, ba)\<in>set eqs. aa < length l2 \<and> ba < length l2"
    "x \<in> set eqs" "x = (aa, ba)" 
    "are_congruent \<lparr>cc_list = l2, 
    use_list = u2, 
    lookup = t2, 
    pending = pe2,
    proof_forest = pf[e := e'], 
    pf_labels = pfl[e := Some eq], 
    input = ip2\<rparr> (aa \<approx> ba)"
  shows "(aa \<approx> ba)
    \<in> Congruence_Closure
        (cc_explain_aux
          \<lparr>cc_list = l2, 
    use_list = u2, 
    lookup = t2, 
    pending = pe2,
    proof_forest = pf[e := e'], 
    pf_labels = pfl[e := Some eq], 
    input = ip2\<rparr>
          la eqs \<union>
         cc_list_set la)"
  unfolding cc_explain_correctness_invar_def
  sorry

lemma cc_explain_correctness_invar_independent_from_use_list:
  assumes "cc_invar_reduced \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr>" 
    "cc_explain_correctness_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "cc_explain_correctness_invar ?base")
  shows "cc_explain_correctness_invar \<lparr>cc_list = l, use_list = u2, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  sorry


lemma cc_explain_correctness_invar_mini_step:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr>" 
    "cc_explain_correctness_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    (is "cc_explain_correctness_invar ?base")
"True"
    "rep_of pf a \<noteq> rep_of pf b"
    "a < length l" "b < length l"
  shows "cc_explain_correctness_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
    (is "cc_explain_correctness_invar ?step")
  unfolding cc_explain_correctness_invar_def
proof(standard, standard, standard, standard, standard, standard, standard)
  fix la eqs x aa ba
  assume prems: "explain_list_invar la (proof_forest ?step)"
    "\<forall>(aa, ba)\<in>set eqs. aa < nr_vars ?step \<and> ba < nr_vars ?step"
    "x \<in> set eqs" "x = (aa, ba)" 
    "are_congruent ?step (aa \<approx> ba)"
  then have explain_list_invar_base: "nr_vars ?step = nr_vars ?base"
    "explain_list_invar la (proof_forest ?base)" 
    unfolding congruence_closure.select_convs apply force sorry
  have "ufa_invar pf" "a < length pf" "b < length pf" 
    using assms unfolding proof_forest_invar_def same_length_invar_def by auto 
  with add_edge_domain have dom: "add_edge_dom (pf, a, b)" 
    by (simp add: assms(4))
  from dom assms prems
  show "(aa \<approx> ba) \<in> Congruence_Closure (cc_explain_aux ?step la eqs \<union> cc_list_set la)" 
  proof(induction arbitrary: l pfl eq rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then have "add_edge pf e e' = pf[e := e']" "add_label pfl pf e eq = pfl[e := Some eq]"
         apply (simp add: "1.hyps" add_edge.psimps)
        by (metis True add_label.domintros add_label.psimps)
      then show ?thesis 
        using cc_explain_correctness_invar_fun_upd
          1(9,10,13) sorry
    next
      case False
      let ?l = "ufa_union l e e'"
      have "e < length pf" "pf ! e < length pf" "pf ! e < length l"
        using "1.prems"(1,5) unfolding same_length_invar_def congruence_closure.select_convs 
          apply presburger using "1.prems"(1,5) unfolding same_length_invar_def cc_list_invar_def congruence_closure.select_convs 
         apply (metis congruence_closure.select_convs(5) proof_forest_invar_def ufa_invarD(2))
        using "1.prems"(1,5) unfolding same_length_invar_def cc_list_invar_def proof_forest_invar_def congruence_closure.select_convs 
        by (metis ufa_invarD(2))
      then have "rep_of pf e = rep_of pf (pf ! e)" 
        using "1.prems"(1) unfolding proof_forest_invar_def congruence_closure.select_convs 
        by (simp add: rep_of_iff)
      then have "rep_of l e = rep_of l (pf ! e)" 
        using "1.prems"(1) unfolding same_eq_classes_invar_def congruence_closure.select_convs 
        using \<open>e < length pf\<close> \<open>pf ! e < length pf\<close> by blast
      have "rep_of ?l e = rep_of ?l (pf ! e)" 
        using "1.prems"(1) unfolding cc_list_invar_def congruence_closure.select_convs  
        using "1.prems"(5) "1.prems"(6) \<open>pf ! e < length l\<close> \<open>rep_of l e = rep_of l (pf ! e)\<close> rep_of_ufa_union_invar by blast
      then have "ufa_union l e e' = ufa_union ?l (pf ! e) e"
        using "1.prems"(1) unfolding cc_list_invar_def congruence_closure.select_convs 
        by (metis "1.prems"(5) "1.prems"(6) length_list_update list_update_id rep_of_min ufa_union_invar)
      have 2: "add_edge pf e e' = add_edge (pf[e := e']) (pf ! e) e"
        using "1.hyps" False add_edge.psimps by auto
      then have 3: "add_label pfl pf e eq = 
add_label (pfl[e := Some eq]) pf (pf ! e) (the (pfl ! e))"
        using "1.prems" add_label.psimps add_label_domain False 
        unfolding proof_forest_invar_def same_length_invar_def
        by (metis congruence_closure.select_convs(1) congruence_closure.select_convs(5))
      obtain pER where "path pf (rep_of pf e) pER e" 
        using "1.prems" path_to_root_correct 
        unfolding proof_forest_invar_def same_length_invar_def 
        by (metis cc_list_loop proof_forest_loop propagate_loop.simps(2))
      then have pER: "path pf (rep_of pf e) (butlast pER) (pf ! e)" 
        using "1.prems" False path_butlast path_nodes_lt_length_l rep_of_min
        unfolding proof_forest_invar_def same_length_invar_def 
        by (metis proof_forest_loop propagate_loop.simps(2))
      have e_e': "e < length pf" "e' < length pf" using "1.prems"
        using \<open>path pf (rep_of pf e) pER e\<close> path_nodes_lt_length_l apply presburger
        using "1.prems" False
        unfolding proof_forest_invar_def same_length_invar_def 
        by (metis cc_list_loop proof_forest_loop propagate_loop.simps(2))
      have "path pf (pf ! e) [pf ! e, e] e" 
        using False e_e'(1) pER path.step path_nodes_lt_length_l single by auto
      have e_notin_path: "e \<notin> set (butlast pER)" 
        using "1.prems" \<open>path pf (rep_of pf e) pER e\<close> path_remove_right unfolding proof_forest_invar_def
        by simp
      have *:"cc_invar_reduced
   \<lparr>cc_list = ?l, use_list = u, lookup = t, pending = (the (pfl ! e)) # pe, proof_forest = pf[e := e'],
      pf_labels = (pfl[e := Some eq]), input = ip\<rparr>" sorry (*NOT TRUE*)
      have 4: "cc_explain_correctness_invar
   \<lparr>cc_list = ?l, use_list = u, lookup = t, pending = the (pfl ! e) # pe, proof_forest = pf[e := e'],
      pf_labels = pfl[e := Some eq], input = ip\<rparr>" sorry
      have 5: "validity_invar
   \<lparr>cc_list = ?l, use_list = u, lookup = t, pending = the (pfl ! e) # pe, proof_forest = pf[e := e'],
      pf_labels = pfl[e := Some eq], input = ip\<rparr>" sorry
      have 6: "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        using "1.prems" False rep_of_fun_upd_aux1 \<open>path pf (pf ! e) [pf ! e, e] e\<close>
        unfolding proof_forest_invar_def
        by (metis e_e'(2) length_list_update nth_list_update_eq path_nodes_lt_length_l proof_forest_loop propagate_loop.simps(2) rep_of_fun_upd' rep_of_idx ufa_invar_fun_upd')
      have 7: "pf ! e < length ?l"
        "e < length ?l " using "1.prems"(1) unfolding proof_forest_invar_def 
         apply (simp add: \<open>pf ! e < length l\<close>)
        by (simp add: "1.prems"(5))
      have 8: "explain_list_invar la
   (proof_forest
     \<lparr>cc_list = ufa_union ?l (pf ! e) e, use_list = u[rep_of ?l (pf ! e) := []], lookup = t, pending = pe,
        proof_forest = add_edge (pf[e := e']) (pf ! e) e,
        pf_labels = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e)),
        input = ip\<rparr>)" 
        using "1.prems"(7) "2" by fastforce
      have 9:"\<forall>a\<in>set eqs.
     case a of
     (aa, ba) \<Rightarrow>
       aa < nr_vars
             \<lparr>cc_list = ufa_union ?l (pf ! e) e, use_list = u[rep_of ?l (pf ! e) := []], lookup = t,
                pending = pe, proof_forest = add_edge (pf[e := e']) (pf ! e) e,
                pf_labels = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e)),
                input = ip\<rparr> \<and>
       ba < nr_vars
             \<lparr>cc_list = ufa_union ?l (pf ! e) e, use_list = u[rep_of ?l (pf ! e) := []], lookup = t,
                pending = pe, proof_forest = add_edge (pf[e := e']) (pf ! e) e,
                pf_labels = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e)),
                input = ip\<rparr>" sorry
      have 10: "are_congruent
   \<lparr>cc_list = ufa_union ?l (pf ! e) e, use_list = u[rep_of ?l (pf ! e) := []], lookup = t, pending = pe,
      proof_forest = add_edge (pf[e := e']) (pf ! e) e,
      pf_labels = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e)), input = ip\<rparr>
   (aa \<approx> ba)" sorry
      from 1(2)[OF False * 4 5 6 7 8 9 _ _ 10] have "(aa \<approx> ba)
    \<in> Congruence_Closure
        (cc_explain_aux
          \<lparr>cc_list = ufa_union ?l (pf ! e) e, use_list = u[rep_of ?l (pf ! e) := []], lookup = t,
             pending = pe, proof_forest = add_edge (pf[e := e']) (pf ! e) e,
             pf_labels = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e)), 
input = ip\<rparr>
          la eqs \<union>
         cc_list_set la)"
        using "1.prems" sorry
      then have IH: "(aa \<approx> ba)
    \<in> Congruence_Closure
        (cc_explain_aux
          \<lparr>cc_list = ufa_union l e e', use_list = u[rep_of ?l (pf ! e) := []], lookup = t,
             pending = pe, proof_forest = add_edge (pf[e := e']) (pf ! e) e,
             pf_labels = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e)), 
input = ip\<rparr>
          la eqs \<union>
         cc_list_set la)"
        using "1.prems" \<open>ufa_union l e e' = ufa_union (ufa_union l e e') (pf ! e) e\<close> by auto
      from pER e_notin_path have 4: "add_label (pfl[e := Some eq]) pf (pf ! e) (the (pfl ! e)) = 
add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e))"
        using "1.prems" \<open>path pf (rep_of pf e) pER e\<close> add_label_fun_upd[of pf "pf ! e" "butlast pER" e' e] e_e' False
        unfolding proof_forest_invar_def same_length_invar_def
        by (metis path_nodes_lt_length_l path_rep_eq proof_forest_loop propagate_loop.simps(2))
          (* TODO show that it makes no difference if we have "u[rep_of l e := []]" or "u[rep_of ?l (pf ! e) := []]"*)
      have "rep_of pf (pf ! e) = rep_of pf e"
        using "1.prems" unfolding proof_forest_invar_def 
        by (simp add: e_e'(1) rep_of_idx)
      have "rep_of l (pf ! e) = rep_of l e" using "1.prems" unfolding same_eq_classes_invar_def
        by (metis "1.prems"(1) \<open>rep_of pf (pf ! e) = rep_of pf e\<close> e_e'(1) pER path_nodes_lt_length_l same_eq_classes_invar_divided)
      then show ?thesis using IH 2 3 4  "*" "6" \<open>pf ! e < length pf\<close> \<open>rep_of (ufa_union l e e') e = rep_of (ufa_union l e e') (pf ! e)\<close> e_e'(1) length_list_update same_eq_classes_invar_divided
        by (metis (no_types, lifting))
    qed
  qed
qed


section \<open>paths\<close>

definition labels_on_path where
"labels_on_path p pfl = \<Union>{pending_set' [the (pfl ! x)] | x. x \<in> set p}"

definition labels_in_uf where
"labels_in_uf l pfl = \<Union>{pending_set' [the (pfl ! x)] | x. l ! x \<noteq> x}"


lemma labels_in_uf_same_rep:
  assumes "path l a p b"
  shows "labels_on_path (tl p) pfl \<subseteq> labels_in_uf l pfl"
proof
  fix eq 
  assume "eq \<in> labels_on_path (tl p) pfl"
  then obtain x where x: "x \<in> set (tl p)" "eq \<in> pending_set' [the (pfl ! x)]"
    unfolding labels_on_path_def by fast
  then have "l ! x \<noteq> x" using assms path_not_first_no_root 
    by (metis (no_types, lifting) in_set_conv_nth length_0_conv length_pos_if_in_set list.sel(3) not_gr_zero nth_Cons_0 path.cases)
  then show "eq \<in> labels_in_uf l pfl"
    using x unfolding labels_in_uf_def by blast
qed

subsection \<open>\<open>explain_along_path\<close> abstraction\<close>

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

subsubsection \<open>Abstraction\<close>

lemma explain_along_path_is_labels_on_path:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "output = labels_on_path (tl p) (pf_labels cc) - labels_in_uf l (pf_labels cc)"
using assms proof(induction rule: explain_along_path_induct)
  case (base cc l a c p)
  have "path l c p a" 
    using path_pf_same_rep base unfolding proof_forest_invar_def by metis
  then have "x \<in> set (tl p) \<Longrightarrow> l ! x \<noteq> x" for x 
    using base.hyps(3) explain_list_invar_def path_contains_no_root by auto
  then have "\<Union> {pending_set' [the (pf_labels cc ! x)] |x. x \<in> set (tl p)} \<subseteq>
    \<Union> {pending_set' [the (pf_labels cc ! x)] |x. l ! x \<noteq> x}" 
    by auto
  then show ?case unfolding labels_on_path_def labels_in_uf_def 
    by auto
next
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  have "labels_in_uf (l[rep_of l a := x]) (pf_labels cc) = 
labels_in_uf l (pf_labels cc) - pending_set' [the (pf_labels cc ! x)]"
    sorry
  then show ?case sorry
next
  case (Two cc l a c p1 p2 x x21 x22 x21a x22a x23 x21b x22b x23a "output" new_l pend)
  then show ?case sorry
qed

text \<open>The set of edges on the path between a and b remains the same after an add_edge operation. \<close>


lemma path_invariant_after_add_edge:
  assumes "c = lowest_common_ancestor pf a b"
    "c' = lowest_common_ancestor (add_edge pf e e') a b"
    "path pf c pAC a" "path pf c pBC b"  
    "path (add_edge pf e e') c' pAC' a" "path (add_edge pf e e') c' pBC' b" 
    "ufa_invar pf" "e < length pf" "e' < length pf" "rep_of pf e \<noteq> rep_of pf e'"
  shows
    "\<Union>{pending_set' [the (pfl ! x)] | x. x \<in> set (tl pAC) \<and> l ! x = x}
\<union> \<Union>{pending_set' [the (pfl ! x)] | x. x \<in> set (tl pBC) \<and> l ! x = x}
= \<Union>{pending_set' [the ((add_label pfl pf e lbl) ! x)] | x. x \<in> set (tl pAC') \<and> l ! x = x}
\<union> \<Union>{pending_set' [the ((add_label pfl pf e lbl) ! x)] | x. x \<in> set (tl pBC') \<and> l ! x = x}"
    (is "?base = ?step")
proof-
  have dom: "add_label_dom (pfl, pf, e, lbl)"
    using add_label_domain assms by blast
  from dom assms show "?base = ?step"
  proof(induction arbitrary: c' pAC' pBC' rule: add_label.pinduct)
    case (1 pfl pf e lbl)
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      with "1.prems" have "add_label pfl pf e lbl = (pfl[e := Some lbl])" 
        using "1.hyps" add_label.psimps by auto
      have dom': "add_edge_dom (pf, e, e')"
        using add_edge_domain "1.prems" by blast
      with "1.prems"  have "add_edge pf e e' = (pf[e := e'])" 
        using "1.hyps" add_edge.psimps True by presburger
      have "ufa_invar (add_edge pf e e')" 
        by (simp add: "1.prems" add_edge_ufa_invar_invar)
      have "e \<notin> set (tl pAC)" "e \<notin> set (tl pBC)" 
        using "1.prems" True path_contains_no_root by blast+
      then have paths: "path (pf[e := e']) c pAC a" "path (pf[e := e']) c pBC b"  
        by (auto simp add: "1.prems"(3-) path_fun_upd)
      from "1.prems" have "c = c'" using lowest_common_ancestor_fun_upd
        by (metis True \<open>add_edge pf e e' = pf[e := e']\<close> path_nodes_lt_length_l path_rep_eq)
      then have "pAC = pAC'"  "pBC = pBC'" 
        using "1.prems" \<open>add_edge pf e e' = pf[e := e']\<close> paths \<open>ufa_invar (add_edge pf e e')\<close> path_unique by auto
      have "x \<noteq> e \<Longrightarrow> pfl ! x = add_label pfl pf e lbl ! x" for x 
        by (simp add: \<open>add_label pfl pf e lbl = pfl[e := Some lbl]\<close>)
      then show ?thesis 
        using \<open>e \<notin> set (tl pAC)\<close> \<open>e \<notin> set (tl pBC)\<close> \<open>pAC = pAC'\<close> \<open>pBC = pBC'\<close> by fastforce
    next
      case False
      define c'' where "c'' = lowest_common_ancestor (add_edge pf (pf ! e) e') a b"
      have "path (add_edge pf (pf ! e) e') c'' pAC' a"
        "path (add_edge pf (pf ! e) e') c'' pBC' b" using 1 unfolding c''_def sorry
      have "ufa_invar pf \<Longrightarrow>
    pf ! e < length pf \<Longrightarrow>
    e' < length pf \<Longrightarrow>
    rep_of pf (pf ! e) \<noteq> rep_of pf e'" sorry
      \<comment> \<open>Problem: c' could be anything after add_edge\<close>
      have IH: 
        "\<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pAC) \<and> l ! x = x} \<union>
    \<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pBC) \<and> l ! x = x}
    = \<Union> {pending_set' [the (add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)) ! x)] |x.
          x \<in> set (tl pAC') \<and> l ! x = x} \<union>
       \<Union> {pending_set' [the (add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)) ! x)] |x.
           x \<in> set (tl pBC') \<and> l ! x = x}"
        using 1 False sorry
      then have 2: "\<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pAC) \<and> l ! x = x} \<union>
    \<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pBC) \<and> l ! x = x}
= \<Union> {pending_set' [the (pfl ! x)] |x. x \<in> set (tl pAC) \<and> l ! x = x} \<union>
    \<Union> {pending_set' [the (pfl ! x)] |x. x \<in> set (tl pBC) \<and> l ! x = x}"
        sorry
      from False have "add_label pfl pf e lbl = add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e))"
        by (simp add: "1.hyps" add_label.psimps)
      then show ?thesis using False 2 IH by simp
    qed
  qed
qed

text \<open>lemmata for simplifying \<open>cc_explain\<close>\<close>

lemma explain_along_path_fun_upd1:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "l ! a = a"
    "a \<in> set p"
    "pf_labels cc ! a = Some (One (k\<^sub>1 \<approx> k\<^sub>2))"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows
    "explain_along_path cc (l[a := (proof_forest cc) ! a]) a c =
(output \<union> {k\<^sub>1 \<approx> k\<^sub>2}, 
new_l[a := (proof_forest cc) ! a], 
pend)"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path_domain by blast
  then show ?thesis
    using assms proof(induction rule: explain_along_path.pinduct)
    case (1 cc l a c)
    then show ?case proof(cases "rep_of l a = rep_of l c")
      case True
        (* a can't be on the path to c because l ! a = a *)
      then show ?thesis using explain_along_path.psimps 1 sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed

end