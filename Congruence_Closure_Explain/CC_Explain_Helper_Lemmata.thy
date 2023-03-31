theory CC_Explain_Helper_Lemmata
  imports CC_Explain
begin 

subsection \<open>Conversion of the pending list to a set\<close>
text \<open>This function is needed in order to interpret the pending list of the explain
operation as a set of equations.\<close>
fun pending_set_explain :: "(nat * nat) list \<Rightarrow> equation set"
  where
    "pending_set_explain pend = set (map (\<lambda>(a, b) . (a \<approx> b)) pend)"

lemma pending_set_explain_Cons:
  "pending_set_explain ((a, b) # pend) = {(a \<approx> b)} \<union> pending_set_explain pend"
  by auto

lemma explain_along_path_lowest_common_ancestor:
  assumes "cc_invar cc"
"a < nr_vars cc"
"b < nr_vars cc"
"are_congruent cc (a \<approx> b)"
"c = lowest_common_ancestor (proof_forest cc) a b"
obtains p1 p2 where "path (proof_forest cc) c p1 a" 
      "path (proof_forest cc) c p2 b"
proof-
  assume *: "(\<And>p1 p2.
        path (proof_forest cc) c p1 a \<Longrightarrow>
        path (proof_forest cc) c p2 b \<Longrightarrow> thesis)"
  have 1: "ufa_invar (proof_forest cc)" 
    using assms proof_forest_invar_def by blast
  moreover have 2: "a < length (proof_forest cc)"
"b < length (proof_forest cc)"
    using assms same_length_invar_def by auto
  moreover have 3: "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    using are_congruent_rep_of assms 
    by blast
  ultimately show thesis
      using * assms(5) lowest_common_ancestor_correct 
      by presburger
qed

text \<open>These functions are needed in order to interpret the additional union find as the set
of labels on the corresponding edges in the proof forest.\<close>

fun pe_to_set :: "pending_equation option \<Rightarrow> equation set"
  where
    "pe_to_set None = {}"
  | "pe_to_set (Some (One a')) = {a'}"
  | "pe_to_set (Some (Two a' b')) = {a', b'}"

fun pending_set' :: "pending_equation list \<Rightarrow> equation set"
  where
    "pending_set' [] = {}"
  | "pending_set' ((One a') # xs) = {a'} \<union> pending_set' xs"
  | "pending_set' ((Two a' b') # xs) = {a', b'} \<union> pending_set' xs"

subsection \<open>Lemmata about invariants\<close>

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

subsection \<open>Lemmata about are_congruent\<close>

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

subsection \<open>Lemmata about lowest_common_ancestor\<close>

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

subsection \<open>Helper lemmata about \<open>explain_along_path\<close>\<close>

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

lemma explain_along_path_new_l_length:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "length l = length new_l" 
proof-
  from assms have "explain_list_invar new_l (proof_forest cc)" using
explain_along_path_domain[OF assms(1-3)] explain_list_invar_explain_along_path'[OF _ assms(2,1,3,4)]
    by blast
  with assms(2) show ?thesis unfolding explain_list_invar_def 
    by presburger
qed

subsection \<open>Induction rule for \<open>explain_along_path\<close>.\<close>

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

subsection \<open>Induction rule for \<open>cc_explain_aux\<close>.\<close>

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


end
