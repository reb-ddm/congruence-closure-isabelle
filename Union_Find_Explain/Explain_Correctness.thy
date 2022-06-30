section \<open>Correctness proofs for Explain\<close>
theory Explain_Correctness
  imports Helper_Functions "HOL.List"
begin 

subsection \<open>\<open>explain\<close> lemmas\<close>

paragraph \<open>A few lemmas about intermediate results of explain\<close>

lemma k_and_outgoing_edge_same_rep:
  assumes "ufe_invar ufe"
    and "(uf_list ufe) ! k \<noteq> k"
    and "k < length (uf_list ufe)"
  shows "rep_of (uf_list ufe) k = rep_of (uf_list ufe) (fst ((unions ufe) ! (the ((au ufe) ! k))))
          \<and> rep_of (uf_list ufe) k = rep_of (uf_list ufe) (snd ((unions ufe) ! (the ((au ufe) ! k))))"
  using assms proof(induction rule: apply_unions_induct)
  case initial
  have "rep_of (uf_list (initial_ufe (length (uf_list ufe)))) k = k" 
    by (simp add: assms(3) rep_of_refl)
  with initial show ?case by simp
next
  case (union pufe x y)
  with ufe_invar_imp_ufa_invar have invar: "ufa_invar (uf_list pufe)"
    by blast
  show ?case 
  proof(cases "(uf_list pufe) ! k = k")
    case True
      \<comment>\<open>k was a root before, but after the union it isn't any more. 
        Therefore k was equal to rep_of x before the union.\<close>
    with invar have rep: "rep_of (uf_list pufe) k = k" 
      by (simp add: rep_of_refl) 
    then have uf_list: "uf_list (ufe_union pufe x y) = (uf_list pufe)[rep_of (uf_list pufe) x := rep_of (uf_list pufe) y]"
      by (simp add: invar ufe_union_uf_list union.hyps(2))
    with union.prems(1) uf_list have k: "k = rep_of (uf_list pufe) x" 
      by (metis True nth_list_update_neq rep_of_refl)
    with union rep_of_ufe_union_invar have 1: "rep_of (uf_list (ufe_union pufe x y)) k = rep_of (uf_list (ufe_union pufe x y)) x"
      by (metis uf_list rep length_list_update)
    then have unions: "unions (ufe_union pufe x y) = unions pufe @ [(x, y)]" 
      by (metis True ufe_union1_ufe ufe_union2_unions union.prems(1))
    then have au: "au (ufe_union pufe x y) = (au pufe)[rep_of (uf_list pufe) x := Some (length (unions pufe))]"
      by (metis rep True k list_update_id uf_list ufe_union2_au union.prems(1))
    from length_au union have "k < length (au pufe)" 
      by (metis length_list_update uf_list)
    with k au have "(au (ufe_union pufe x y)) ! k = Some (length (unions pufe))" 
      by simp
    then have "(unions (ufe_union pufe x y) ! (the ((au (ufe_union pufe x y)) ! k))) = (x, y)"
      by (simp add: unions)
    then show ?thesis 
      by (metis "1" fstI invar sndI uf_list ufa_union_aux union.hyps(2) union.hyps(3))
  next
    case False
      \<comment>\<open>k was not a root. The induction hypotheses applies.\<close>
    with invar have "rep_of (uf_list pufe) k \<noteq> k" 
      by (metis rep_of_min ufe_union_length_uf_list union.prems(2))
    with union have 1: "rep_of (uf_list pufe) k = rep_of (uf_list pufe) (fst (unions pufe ! the (au pufe ! k)))"
      by (metis False ufe_union_length_uf_list)
    obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
      using ufe_data_structure.cases by blast
    with union have "k < length l1" 
      by (metis ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
    with False au_Some_if_not_root union obtain a where "(a1 ! k) = Some a" 
      by (metis pufe rep_of_refl ufe_data_structure.select_convs(1))
    with union au_Some_valid have "a < length u1" 
      by (metis apply_unions_length_au length_replicate pufe ufe_data_structure.select_convs(2) ufe_data_structure.select_convs(3) ufe_union_length_uf_list)
    with union have "fst (u1 ! a) < length l1" "snd (u1 ! a) < length l1"
      by (simp_all add: pufe)
    then have 2: "fst (unions pufe ! the (au pufe ! k)) < length (uf_list pufe)" "snd (unions pufe ! the (au pufe ! k)) < length (uf_list pufe)"
      by (simp_all add: \<open>a1 ! k = Some a\<close> pufe)
    with 1 2 union rep_of_ufe_union_invar have "fst (unions pufe ! the (au pufe ! k)) = fst (unions (ufe_union pufe x y) ! the (au (ufe_union pufe x y) ! k))"
      "snd (unions pufe ! the (au pufe ! k)) = snd (unions (ufe_union pufe x y) ! the (au (ufe_union pufe x y) ! k))"
      by (metis \<open>a < length u1\<close> \<open>a1 ! k = Some a\<close> au_ufe_union_Some_invar option.sel pufe ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(2) ufe_data_structure.select_convs(3) unions_ufe_union_invar)+
    with 1 2 union rep_of_ufe_union_invar show ?thesis
      by (metis False \<open>k < length l1\<close> pufe ufe_data_structure.select_convs(1))
  qed
qed

lemma k_and_outgoing_edge_same_rep_before_union:
  assumes "ufe_invar before"
    and "after = ufe_union before x2 y2"
    and "x < length (uf_list before)" and "y < length (uf_list before)"
    and "x2 < length (uf_list before)" and "y2 < length (uf_list before)"
    and "rep_of (uf_list before) x \<noteq> rep_of (uf_list before) y"
    and same_rep_after: "rep_of (uf_list after) x = rep_of (uf_list after) y"
    and "rep_of (uf_list before) y = rep_of (uf_list after) y"
  shows "rep_of (uf_list before) x2 = rep_of (uf_list before) x
          \<and> rep_of (uf_list before) y = rep_of (uf_list before) y2"
proof-
  have *: "uf_list after = (uf_list before)[rep_of (uf_list before) x2 := rep_of (uf_list before) y2]"
    by (metis assms(2) assms(7) assms(8) assms(9) ufe_union1_uf_list ufe_union2_uf_list)
  moreover have "rep_of (uf_list before) x \<noteq> rep_of (uf_list after) x"
    using assms(7) assms(8) assms(9) by auto
  have "ufe_invar after"  
    using union_ufe_invar assms(1,2) 
    by (smt (verit, ccfv_threshold) assms(5) assms(6) old.unit.exhaust ufe_data_structure.surjective)
  then have invar:  "ufa_invar (uf_list after)" "ufa_invar (uf_list before)"
    using assms(1) ufe_invar_imp_ufa_invar by blast+
  ultimately have rep_x_eq_x2: "rep_of (uf_list before) x = rep_of (uf_list before) x2"
    by (metis assms(3) assms(5) assms(6) assms(7) assms(9) same_rep_after ufa_union_aux)
  from * have "rep_of (uf_list after) x2 = rep_of (uf_list before) y2" 
    by (simp add: assms(5) assms(6) invar(2) ufa_union_aux)
  with same_rep_after have "rep_of (uf_list after) x = rep_of (uf_list before) y2"
    by (metis "*" rep_x_eq_x2 assms(3) assms(5) assms(6) invar(2) rep_of_ufa_union_invar)
  from same_rep_after assms(9)have "rep_of (uf_list after) x = rep_of (uf_list before) y"
    by simp
  then show ?thesis 
    by (simp add: \<open>rep_of (uf_list after) x = rep_of (uf_list before) y2\<close> \<open>rep_of (uf_list before) x = rep_of (uf_list before) x2\<close>)
qed

lemma explain_case_x_x_neq_lca:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x \<ge> newest_index_y"
  shows "x \<noteq> lca"
proof-
  have invar: "ufa_invar l" using assms(1,2) ufe_invar_imp_ufa_invar 
    by fastforce
  from find_newest_x_neq_None_or_find_newest_y_neq_None assms 
  obtain k_x' where "newest_index_x = Some k_x'" 
    by (metis less_eq_option_None_is_None option.collapse ufe_data_structure.select_convs(1))
  with find_newest_on_path_if_Some show *: "x \<noteq> lca"
    using assms(3) assms(5) find_newest_on_path.domintros invar by blast
qed

lemma explain_case_y_y_neq_lca:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x < newest_index_y"
  shows "y \<noteq> lca"
proof-
  have invar: "ufa_invar l" using assms(1,2) ufe_invar_imp_ufa_invar 
    by fastforce
  from find_newest_x_neq_None_or_find_newest_y_neq_None assms 
  obtain k_y' where "newest_index_y = Some k_y'" 
    by (metis less_option_None option.collapse)
  with find_newest_on_path_if_Some show *: "y \<noteq> lca"
    using assms find_newest_on_path.domintros invar by blast
qed

lemma explain_case_x_newest_index_x_Some:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "(ax, bx) = u ! the (newest_index_x)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x \<ge> newest_index_y"
  shows "\<exists> k .newest_index_x = Some k \<and> k < length u" 
    and "ax < length l" and "bx < length l"
proof-
  have invar: "ufa_invar l" using assms(1,2) ufe_invar_imp_ufa_invar 
    by fastforce
  with assms explain_case_x_x_neq_lca have *: "x \<noteq> lca"
    by blast
  from assms lowest_common_ancestor_correct obtain pX where "path l lca pX x" 
    using invar by presburger
  with * find_newest_on_path_Some assms
  obtain k_x where k_x: "newest_index_x = Some k_x \<and> k_x < length u" 
    by blast
  then show "\<exists>k. newest_index_x = Some k \<and> k < length u" by simp
  with k_x assms have "fst (u ! k_x) < length l" "snd (u ! k_x) < length l"
    by auto
  with assms show "ax < length l" "bx < length l"
    by (metis k_x fst_conv snd_conv option.sel)+
qed

lemma explain_case_y_newest_index_y_Some:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "(ay, by) = u ! the (newest_index_y)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x < newest_index_y"
  shows "\<exists> k .newest_index_y = Some k \<and> k < length u" 
    and "ay < length l" and "by < length l"
proof-
  have invar: "ufa_invar l" using assms(1,2) ufe_invar_imp_ufa_invar 
    by fastforce
  with assms explain_case_y_y_neq_lca have *: "y \<noteq> lca"
    using assms find_newest_on_path.domintros invar by blast
  from assms lowest_common_ancestor_correct obtain pY where "path l lca pY y" 
    using invar by presburger
  with * find_newest_on_path_Some assms
  obtain k_y where k_y: "newest_index_y = Some k_y \<and> k_y < length u" 
    by blast
  then show "\<exists>k. newest_index_y = Some k \<and> k < length u" by simp
  with k_y assms have "fst (u ! k_y) < length l" "snd (u ! k_y) < length l"
    by auto
  with assms show "ay < length l" "by < length l"
    by (metis k_y fst_conv snd_conv option.sel)+
qed

lemma explain_case_x_newest_index_index2:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "x \<noteq> lca"
  shows "\<exists> i p . path l lca p x \<and> newest_index_x = (a ! (p ! i)) \<and> i < length p \<and> i > 0"
proof-
  from assms(1) have invar: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  from invar assms lowest_common_ancestor_correct 
  obtain p where "path l lca p x" 
    by presburger
  with assms find_newest_on_path_correct have **: "newest_index_x = (MAX i\<in>set [1..<length p]. a ! (p ! i))"
    using \<open>x \<noteq> lca\<close> invar path_unique by blast
  from assms have "length a = length l" 
    by (metis apply_unions_length_au length_replicate ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))
  then have *: "i \<in> (set [1..<length p]) \<Longrightarrow> (p ! i) < length a" for i 
    using \<open>path l lca p x\<close> nodes_path_lt_length_l by simp
  have  "length p > 1" 
    by (metis \<open>path l lca p x\<close> \<open>x \<noteq> lca\<close> length_0_conv less_one list_decomp_1 nat_neq_iff path_not_empty path_single)
  then have "set [1..<length p] \<noteq> {}" "finite(set [1..<length p])" 
    by simp_all
  with ** have "newest_index_x \<in> (\<lambda> i . a ! (p ! i)) ` (set [1..<length p])" 
    by (metis empty_is_image eq_Max_iff finite_imageI)
  then obtain i where "newest_index_x = a ! (p ! i)" and "i < length p \<and> 0 < i" 
    by auto
  then have "path l lca p x \<and> newest_index_x = a ! (p ! i) \<and> i < length p \<and> 0 < i"
    by (simp add: \<open>path l lca p x\<close>)
  then show ?thesis 
    by auto
qed

lemma explain_case_x_newest_index_index:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x \<ge> newest_index_y"
  shows "\<exists> i p . path l lca p x \<and> newest_index_x = (a ! (p ! i)) \<and> i < length p \<and> i > 0"
proof-
  from assms(1) have invar: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  from assms have "x \<noteq> lca" 
    using explain_case_x_x_neq_lca by blast
  with assms explain_case_x_newest_index_index2 show ?thesis 
    by auto
qed

lemma explain_case_y_newest_index_index2:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "y \<noteq> lca"
  shows "\<exists> i p . path l lca p y \<and> newest_index_y = (a ! (p ! i)) \<and> i < length p \<and> i > 0"
proof-
  from assms(1) have invar: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  from invar assms lowest_common_ancestor_correct 
  obtain p where "path l lca p y" 
    by presburger
  with assms find_newest_on_path_correct have **: "newest_index_y = (MAX i\<in>set [1..<length p]. a ! (p ! i))"
    using \<open>y \<noteq> lca\<close> invar path_unique by blast
  from assms have "length a = length l" 
    by (metis apply_unions_length_au length_replicate ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))
  then have *: "i \<in> (set [1..<length p]) \<Longrightarrow> (p ! i) < length a" for i 
    using \<open>path l lca p y\<close> nodes_path_lt_length_l by simp
  have  "length p > 1" 
    by (metis \<open>path l lca p y\<close> \<open>y \<noteq> lca\<close> length_0_conv less_one list_decomp_1 nat_neq_iff path_not_empty path_single)
  then have "set [1..<length p] \<noteq> {}" "finite(set [1..<length p])" 
    by simp_all
  with ** have "newest_index_y \<in> (\<lambda> i . a ! (p ! i)) ` (set [1..<length p])" 
    by (metis empty_is_image eq_Max_iff finite_imageI)
  then obtain i where "newest_index_y = a ! (p ! i)" and "i < length p \<and> 0 < i" 
    by auto
  then have "path l lca p y \<and> newest_index_y = a ! (p ! i) \<and> i < length p \<and> 0 < i"
    by (simp add: \<open>path l lca p y\<close>)
  then show ?thesis 
    by auto
qed

lemma explain_case_y_newest_index_index:
  assumes "ufe_invar  \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x < newest_index_y"
  shows "\<exists> i p . path l lca p y \<and> newest_index_y = (a ! (p ! i)) \<and> i < length p \<and> i > 0"
proof-
  from assms(1) have invar: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  from assms have "y \<noteq> lca" 
    using explain_case_y_y_neq_lca by blast
  with assms explain_case_y_newest_index_index2 show ?thesis 
    by auto
qed

lemma explain_case_x_rep_of_ax_bx:
  assumes "ufe_invar ufe_before"
    and "ufe_before = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "(ax, bx) = u ! the (newest_index_x)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x \<ge> newest_index_y"
  shows "rep_of l ax = rep_of l x" and "rep_of l bx = rep_of l x"
proof-
  from assms have invar: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar) 
  from assms have "lca \<noteq> x" 
    using explain_case_x_x_neq_lca by blast
  with assms explain_case_x_newest_index_index obtain p i where p: "path l lca p x" 
    and i: "newest_index_x = (a ! (p ! i)) \<and> i < length p \<and> i > 0" 
    by metis
  with nodes_path_rep_of p invar have *: "rep_of l (p ! i) = rep_of l x" 
    by blast
  from path_not_first_no_root i p have no_root: "l ! (p ! i) \<noteq> (p ! i)" 
    by blast
  from nodes_path_lt_length_l p i have "p ! i < length l" 
    by blast
  with k_and_outgoing_edge_same_rep assms 
  have "rep_of l (p ! i) = rep_of l ax" "rep_of l (p ! i) = rep_of l bx" 
    by (metis fst_eqD snd_eqD i no_root ufe_data_structure.select_convs(1,2,3))+
  with * show "rep_of l ax = rep_of l x" and "rep_of l bx = rep_of l x"
    by simp_all
qed

lemma explain_case_y_rep_of_ay_by:
  assumes "ufe_invar ufe_before"
    and "ufe_before = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "(ay, by) = u ! the (newest_index_y)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x < newest_index_y"
  shows "rep_of l ay = rep_of l y" and "rep_of l by = rep_of l y"
proof-
  from assms have invar: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar) 
  from assms have "lca \<noteq> y" 
    using explain_case_y_y_neq_lca by blast
  with assms explain_case_y_newest_index_index obtain p i where p: "path l lca p y" 
    and i: "newest_index_y = (a ! (p ! i)) \<and> i < length p \<and> i > 0" 
    by metis
  with nodes_path_rep_of p invar have *: "rep_of l (p ! i) = rep_of l y" 
    by blast
  from path_not_first_no_root i p have no_root: "l ! (p ! i) \<noteq> (p ! i)" 
    by blast
  from nodes_path_lt_length_l p i have "p ! i < length l" 
    by blast
  with k_and_outgoing_edge_same_rep assms 
  have "rep_of l (p ! i) = rep_of l ay" "rep_of l (p ! i) = rep_of l by" 
    by (metis fst_eqD snd_eqD i no_root ufe_data_structure.select_convs(1,2,3))+
  with * show "rep_of l ay = rep_of l y" and "rep_of l by = rep_of l y"
    by simp_all
qed

paragraph \<open>Inverse direction of \<open>explain.domintros\<close>:\<close>

lemma explain_domain_cases:
  assumes "explain_dom (ufe, x, y)"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
    and "lca = lowest_common_ancestor l x y"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "(ax, bx) = u ! the (newest_index_x)"
    and "(ay, by) = u !  the (newest_index_y)"
    and "\<not> (x = y \<or> rep_of l x \<noteq> rep_of l y)"
  shows "newest_index_x \<ge> newest_index_y
          \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, ax)" 
    and "newest_index_x \<ge> newest_index_y
          \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, bx, y)"
    and "\<not> (newest_index_x \<ge> newest_index_y)
          \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, x, by)"
    and "\<not> (newest_index_x \<ge> newest_index_y)
          \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, ay, y)"
  using assms proof(induction ufe x y 
    arbitrary: l u a lca newest_index_x newest_index_y ax bx ay "by" rule: explain.pinduct)
  case IH: (1 l2 u2 a2 x2 y2)
  {
    case 1
    show ?case 
      thm explain_cases[of l u a x2 ax ]
    proof(cases rule: explain_cases[of l u a x2 ax ])
      case (base ufe)
      then show ?thesis using explain.domintros by blast
    next
      case case_x
      then show ?thesis using 1 IH(1) IH(2) IH(3) explain_case_x_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a x2 _ _ ax]
        by (metis (no_types, opaque_lifting) old.prod.exhaust ufe_data_structure.ext_inject)
    next
      case case_y
      then show ?thesis
        using 1 IH(1) IH(4) IH(5) explain_case_y_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a x2 _ _ ax]
        by (metis (no_types, opaque_lifting) old.prod.exhaust ufe_data_structure.ext_inject)
    qed
    case 2
    show ?case 
    proof(cases rule: explain_cases[of l u a bx y2])
      case base
      then show ?thesis 
        using explain.domintros by blast
    next
      case case_x
      then show ?thesis 
        using 2 IH(1) IH(6) IH(7) explain_case_x_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a bx _ _ y2] 
        by (metis surj_pair ufe_data_structure.ext_inject)
    next
      case case_y
      then show ?thesis 
        using 2 IH(1) IH(8) IH(9) explain_case_y_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a bx _ _ y2] 
        by (metis (no_types, opaque_lifting) old.prod.exhaust ufe_data_structure.ext_inject) 
    qed 
  next
    case 3
    show ?case
    proof(cases rule: explain_cases[of l u a x2 "by" ])
      case base
      then show ?thesis using explain.domintros by blast
    next
      case case_x
      then show ?thesis 
        using 3 IH(1) IH(10) IH(11) explain_case_x_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a x2 _ _ "by"] 
        by (metis (no_types, opaque_lifting) old.prod.exhaust ufe_data_structure.ext_inject)
    next
      case case_y
      then show ?thesis 
        using 3 IH(1) IH(12) IH(13) explain_case_y_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a x2 _ _ "by"]  
        by (metis (no_types, opaque_lifting) old.prod.exhaust ufe_data_structure.ext_inject) 
    qed
  next
    case 4
    show ?case 
    proof(cases rule: explain_cases[of l u a ay y2])
      case base
      then show ?thesis 
        using explain.domintros by blast
    next
      case case_x
      then show ?thesis 
        using 4 IH(1) IH(14) IH(15)  explain_case_x_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a ay _ _ y2]  
        by (metis (no_types, opaque_lifting) old.prod.exhaust ufe_data_structure.ext_inject)
    next
      case case_y
      then show ?thesis 
        using 4 IH(1) IH(16) IH(17)  explain_case_y_domain[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>" l u a ay _ _ y2] 
        by (metis (no_types, opaque_lifting) old.prod.exhaust ufe_data_structure.ext_inject)   
    qed
  }
qed

paragraph \<open>Other useful lemmas\<close>

lemma au_entries_neq:
  assumes "ufe_invar ufe" and "i1 \<noteq> i2"
    and "i1 < length (uf_list ufe)" and "i2 < length (uf_list ufe)"
    and "(au ufe) ! i1 = Some k1" and "(au ufe) ! i2 = Some k2"
  shows "k1 \<noteq> k2"
  using assms proof(induction rule: apply_unions_induct)
  case initial
  then show ?case by simp
next
  case (union pufe x y)
  then show ?case 
  proof(cases "au pufe ! i1 = Some k1")
    case True
    then show ?thesis 
    proof(cases "au pufe ! i2 = Some k2")
      case True
      have "au (ufe_union pufe x y) ! i1 = Some k1"
        by (simp add: union.prems(4))
      moreover have "au (ufe_union pufe x y) ! i2 = Some k2"
        by (simp add: union.prems(5))
      ultimately show ?thesis using union 
        by (metis apply_unions_length_au au_valid length_replicate less_irrefl_nat less_option_Some nth_list_update_eq nth_list_update_neq ufe_data_structure.select_convs(3) ufe_union1_au ufe_union2_au ufe_union_length_uf_list) 
    next
      case False
      have "au pufe ! i2 = None" 
      proof(rule ccontr)
        assume "au pufe ! i2 \<noteq> None "
        then obtain k3 where  "au pufe ! i2 = Some k3" by blast
        with union(1,2,3,8) au_ufe_union_Some_invar 
        have "au (ufe_union pufe x y) ! i2 = Some k3" by blast
        then show "False" 
          using False \<open>au pufe ! i2 = Some k3\<close> union.prems(5) by auto
      qed
      from union.prems(5) have "i2 = rep_of (uf_list pufe) x" 
        by (metis False nth_list_update_neq ufe_union1_au ufe_union2_au)
      with union.prems(1,4) have "au pufe ! i1 = Some k1" 
        by (metis nth_list_update_neq ufe_union1_ufe ufe_union2_au)
      with union(1) au_valid union.prems(2) have "k1 < length (unions pufe)" 
        by (metis apply_unions_length_au length_replicate less_option_Some ufe_data_structure.select_convs(3) ufe_union_length_uf_list)
      moreover have "k2 = length (unions pufe)"
        by (metis False nth_list_update' option.inject ufe_union1_au ufe_union2_au union.prems(5))
      ultimately show ?thesis by blast
    qed
  next
    case False
    have "au pufe ! i1 = None" 
    proof(rule ccontr)
      assume "au pufe ! i1 \<noteq> None "
      then obtain k3 where  "au pufe ! i1 = Some k3" by blast
      with union(1,2,3,8) au_ufe_union_Some_invar 
      have "au (ufe_union pufe x y) ! i1 = Some k3" by blast
      then show "False" 
        using False \<open>au pufe ! i1 = Some k3\<close> union.prems(4) by auto
    qed
    from union.prems(4) have "i1 = rep_of (uf_list pufe) x" 
      by (metis False nth_list_update_neq ufe_union1_au ufe_union2_au)
    with union.prems(1, 5) have "au pufe ! i2 = Some k2" 
      by (metis nth_list_update_neq ufe_union1_ufe ufe_union2_au)
    with union(1) au_valid union.prems(3) have "k2 < length (unions pufe)" 
      by (metis apply_unions_length_au length_replicate less_option_Some ufe_data_structure.select_convs(3) ufe_union_length_uf_list)
    moreover have "k1 = length (unions pufe)" 
      by (metis False nth_list_update' option.inject ufe_union1_au ufe_union2_au union.prems(4))
    ultimately show ?thesis by blast
  qed
qed

lemma paths_lca_disjoint:
  assumes "ufa_invar l"
    and "path l (lowest_common_ancestor l x y) pX x"
    and "path l (lowest_common_ancestor l x y) pY y"
    and "i1 < length pX"
    and "i2 < length pY"
    and "i1 \<noteq> 0"
  shows "pX ! i1 \<noteq> pY ! i2"
proof
  let ?lca = "lowest_common_ancestor l x y"
  let ?prefixX = "path_to_root l ?lca @ tl (take i1 pX @ [pX ! i1])"
  let ?prefixY = "path_to_root l ?lca @ tl (take i2 pY @ [pY ! i2])"
  let ?pathX = "path_to_root l ?lca @ tl pX"
  let ?pathY = "path_to_root l ?lca @ tl pY"
  assume assm: "pX ! i1 = pY ! i2"
  have "pX = take i1 pX @ drop i1 pX" by simp
  with path_divide2 assms have 
    p1: "path l ?lca (take i1 pX @ [pX ! i1]) (pX ! i1)" 
    and "path l (pX ! i1) (drop i1 pX) x"
    by (metis Cons_nth_drop_Suc hd_drop_conv_nth list.discI)+
  from path_divide2 assms have 
    "path l ?lca (take i2 pY @ [pY ! i2]) (pY ! i2)" 
    and "path l (pY ! i2) (drop i2 pY) y"
    by (metis append_take_drop_id drop_eq_Nil2 hd_drop_conv_nth le_antisym less_imp_le_nat nat_neq_iff)+
  with p1 path_unique have pY_pX_eq: "take i2 pY @ [pY ! i2] = take i1 pX @ [pX ! i1]" 
    by (metis assm assms(1))
  have path_rep_lca: "path l (rep_of l x) (path_to_root l ?lca) ?lca"
    by (metis assms(1) assms(2) path_nodes_lt_length_l path_rep_eq path_to_root_correct)
  then have "path l (rep_of l x) ?pathX x"
    and "path l (rep_of l x) ?pathY y"
    using assms path_concat1 by auto
  then have paths_to_root: "path_to_root l x = ?pathX" 
    "path_to_root l y = ?pathY"
    using assms path_to_root_correct path_unique path_rep_eq
    by (metis path_nodes_lt_length_l)+
  have "?pathX = ?prefixX @ tl(drop i1 pX)" 
    and "?pathY = ?prefixY @ tl(drop i2 pY)" using assms
    by (metis append_assoc append_take_drop_id take_Suc_conv_app_nth take_tl tl_drop)+
  then have *: "prefix ?prefixX ?pathX" "prefix ?prefixY ?pathY" 
    using prefixI by blast+
  have "?prefixX = ?prefixY" 
    using pY_pX_eq by auto
  with * have prefix2: "prefix ?prefixX (longest_common_prefix ?pathX ?pathY)"
    by (metis longest_common_prefix_max_prefix)
  then obtain path_lca where "longest_common_prefix ?pathX ?pathY = ?prefixX @ path_lca" 
    using prefixE by blast
  with path_rep_lca path_divide1 
  have "path l (rep_of l x) (longest_common_prefix ?pathX ?pathY) (last (longest_common_prefix ?pathX ?pathY))"
    by (smt (verit, ccfv_SIG) append_is_Nil_conv assms(2) longest_common_prefix_prefix1 paths_iff prefix_def)
  with path_rep_lca have "longest_common_prefix ?pathX ?pathY = path_to_root l ?lca"
    by (metis paths_to_root assms(1) lowest_common_ancestor.simps path_unique)
  then show "False" 
    using prefix2 assms(4,6) path_concat1 by force
qed

lemma explain_index_neq:
  assumes "ufe_invar ufe"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x < length l" and "y < length l"
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)" 
    and "lca = lowest_common_ancestor l x y"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
  shows "newest_index_x \<noteq> newest_index_y"
proof-
  from assms have invar:"ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  with assms lowest_common_ancestor_correct 
  obtain pX where p1: "path l lca pX x" by presburger
  then have dom: "find_newest_on_path_dom (l, a, x, lca)" 
    by (simp add: \<open>ufa_invar l\<close> find_newest_on_path_domain path_nodes_lt_length_l)
  from assms lowest_common_ancestor_correct \<open>ufa_invar l\<close>
  obtain pY where p2: "path l lca pY y" by presburger
  then have "find_newest_on_path_dom (l, a, y, lca)"
    by (simp add: \<open>ufa_invar l\<close> find_newest_on_path_domain path_nodes_lt_length_l)
  consider (a) "x = lca"  | (b) "y = lca" | (c) "x \<noteq> lca \<and> y \<noteq> lca"
    by blast
  then show ?thesis proof(cases)
    case a
    then have *: "find_newest_on_path l a x lca = None"
      using find_newest_on_path.psimps dom by presburger
    then have "y \<noteq> lca" 
      using assms a by blast
    with find_newest_on_path_Some 
    obtain k where "find_newest_on_path l a y lca = Some k"
      by (metis assms(1) assms(2) p2)
    with assms * show ?thesis by force
  next 
    case b
    then have *: "find_newest_on_path l a y lca = None"
      using find_newest_on_path.psimps dom 
      using \<open>find_newest_on_path_dom (l, a, y, lca)\<close> by force
    then have "x \<noteq> lca" 
      using assms b by blast
    with find_newest_on_path_Some 
    obtain k where "find_newest_on_path l a x lca = Some k"
      by (metis assms(1) assms(2) p1)
    with assms * show ?thesis by force
  next
    case c
    with c assms explain_case_x_newest_index_index2 obtain p' i1 
      where p': "path l lca p' x" and i1: "0 < i1 \<and> i1 < length p' \<and> newest_index_x = a ! (p' ! i1)" 
      by metis
    with c assms explain_case_y_newest_index_index2 obtain p'' i2 
      where p'': "path l lca p'' y" and i2: "0 < i2 \<and> i2 < length p'' \<and> newest_index_y = a ! (p'' ! i2)" 
      by metis
    from assms(6) invar i1 i2 p' p'' have p_neq: "(p' ! i1) \<noteq> (p'' ! i2)" 
      by (simp add: paths_lca_disjoint)
    from path_not_first_no_root p' i1 p'' i2
    have no_root: "l ! (p' ! i1) \<noteq> (p' ! i1)" "l ! (p'' ! i2) \<noteq> (p'' ! i2)"
      by blast+
    from p' p'' have path_length: "(p' ! i1) < length l" "(p'' ! i2) < length l" 
      using i1 i2 nodes_path_lt_length_l by blast+
    with assms(1,2) au_Some_if_not_root obtain k1 k2 
      where "a ! (p' ! i1) = Some k1" "a ! (p'' ! i2) = Some k2" 
      using no_root by metis
    with au_entries_neq have "a ! (p' ! i1) \<noteq> a ! (p'' ! i2)" 
      by (metis path_length p_neq assms(1,2) ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))
    with dom assms p1 p2 show ?thesis 
      using i1 i2 by presburger
  qed
qed

lemma explain_case_x_rep_of_ax_bx_ufe_union:
  assumes "ufe_invar ufe_before"
    and "ufe_before = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>"
    and "ufe_union ufe_before x2 y2 = \<lparr>uf_list = l, unions = u, au = a\<rparr> "
    and "lca = lowest_common_ancestor l x y"
    and "x < length l" and "y < length l"
    and "x2 < length l" and "y2 < length l"
    and "newest_index_x = find_newest_on_path l a x lca"
    and "newest_index_y = find_newest_on_path l a y lca"
    and "(ax, bx) = u ! the (newest_index_x)" 
    and "\<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)"
    and "newest_index_x \<ge> newest_index_y"
  shows "rep_of (uf_list ufe_before) ax = rep_of (uf_list ufe_before) x" 
    and "rep_of (uf_list ufe_before) bx = rep_of (uf_list ufe_before) y" 
proof-
  from assms(1,2,3,6,7) union_ufe_invar have ufe_invar: "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
    by (metis assms(8) ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  then have invar: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  from assms  have invar1: "ufa_invar l1"
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  from assms have length_eq: "length l = length l1" 
    by (metis ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  from assms have "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
    using ufe_invar by blast
  then have "rep_of (uf_list ufe_before) ax = rep_of (uf_list ufe_before) x \<and> rep_of (uf_list ufe_before) bx = rep_of (uf_list ufe_before) y" 
  proof(cases "rep_of l1 x = rep_of l1 y")
    case True
    then show ?thesis 
    proof(cases "rep_of l1 x2 = rep_of l1 y2")
      case True
        \<comment> \<open>ufe_after is the same as ufe_before: ax, bx, x and y all have the same rep. \<close>
      with ufe_union1 assms(3) have ufe_not_changed: "\<lparr>uf_list = l1, unions = u1, au = a1\<rparr> = \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
        using assms(2) by force
      with explain_case_x_rep_of_ax_bx assms  show "rep_of (uf_list ufe_before) ax = rep_of (uf_list ufe_before) x \<and> rep_of (uf_list ufe_before) bx = rep_of (uf_list ufe_before) y"
        using assms(12) assms(2) ufe_not_changed 
        by (metis ufe_data_structure.select_convs(1))
    next
      case False
        \<comment> \<open>ufe_after has changed, but lca, newest_index etc. haven't changed. \<close>
      define lca' newest_index_x' newest_index_y' axbx' ayby' 
        where defs1: "lca' = lowest_common_ancestor l1 x y"
          "newest_index_x' = find_newest_on_path l1 a1 x lca'"
          "newest_index_y' = find_newest_on_path l1 a1 y lca'"
          "axbx' = u1 ! the (newest_index_x')" 
          "ayby' = u1 ! the (newest_index_y')"
      obtain ax' bx' ay' by' where defs2: "(ax', bx') = axbx'"
        "(ay', by') = ayby'" by (metis prod.exhaust_sel)
      note defs = defs1 defs2
      with assms defs lowest_common_ancestor_ufe_union_invar have "lca = lca'" 
        by (metis True ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
      from defs lowest_common_ancestor_correct obtain px' py' where "path l1 lca' px' x" "path l1 lca' py' y" 
        using invar1 length_eq True assms(5) assms(6) by presburger
      with defs assms False find_newest_on_path_ufe_union_invar have "newest_index_x' = newest_index_x" 
        and  "newest_index_y' = newest_index_y" 
        by (metis \<open>lca = lca'\<close> length_eq path_nodes_lt_length_l ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))+
      with defs assms explain_case_x_newest_index_x_Some obtain k where "newest_index_x' = Some k \<and> k < length u1" 
        by (metis \<open>lca = lca'\<close> \<open>path l1 lca' px' x\<close>  explain_case_x_x_neq_lca find_newest_on_path_Some ufe_invar)
      with defs assms unions_ufe_union_invar have equalities: "ax' = ax"  "bx' = bx"
        by (metis \<open>newest_index_x' = newest_index_x\<close> length_eq old.prod.inject option.sel ufe_data_structure.select_convs(2))+
      with explain_case_x_rep_of_ax_bx defs assms show ?thesis 
        by (metis True \<open>newest_index_x' = newest_index_x\<close> \<open>newest_index_y' = newest_index_y\<close> \<open>path l1 lca' px' x\<close> length_eq path_nodes_lt_length_l ufe_data_structure.select_convs(1)) 
    qed
  next
    case False
      \<comment> \<open>Before the union, x and y where not in the same equivalence class.
        Therefore ax = x2 and bx = y2.\<close>
    then have False2: "rep_of l1 x2 \<noteq> rep_of l1 y2" 
      using assms(12) assms(2) assms(3) by fastforce
    with assms have union: "l = l1[rep_of l1 x2 := rep_of l1 y2]" 
      "a = a1[rep_of l1 x2 := Some(length u1)]"
      "u = u1 @ [(x2, y2)]"
      by fastforce+
    then have "l ! (rep_of l1 x2) = rep_of l1 y2" 
      by (metis assms(7) invar leI length_list_update list_update_beyond nth_list_update_eq rep_of_bound)
    with False2 have "l1 ! (rep_of l1 y2) = rep_of l1 y2" 
      by (metis assms(8) invar1 length_list_update rep_of_min union(1))
    with False2 union rep_of_refl have "l ! (rep_of l1 y2) = rep_of l1 y2" 
      by (metis nth_list_update_neq)
    with assms have "(rep_of l x2) = l ! (rep_of l1 y2) " 
      by (metis invar1 ufa_union_aux ufe_data_structure.select_convs(1) ufe_union_length_uf_list union(1))
    have "rep_of l1 y2 = rep_of l y2" 
      using assms(7) assms(8) invar1 ufa_union_aux union(1) by auto
    from assms(1) au_valid have length_u_max: "i < length a1 \<Longrightarrow> a1 ! i < Some (length u1)" for i 
      by (metis assms(2) ufe_data_structure.select_convs(2) ufe_data_structure.select_convs(3))
    have "rep_of l1 x2 < length l1" 
      using assms(7) invar1 length_eq rep_of_bound by auto
    from assms(1) have "length a1 = length l1" 
      by (metis apply_unions_length_au assms(2) length_replicate ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))
        \<comment> \<open>at the index rep_of l1 x2 there is the biggest value in the array a. Also, it's on the path from x to rep_of l y.\<close>
    from union have **: "a ! rep_of l1 x2 = Some (length u1)"
      by (simp add: \<open>length a1 = length l1\<close> \<open>rep_of l1 x2 < length l1\<close>)
    have "l1 ! rep_of l1 x = rep_of l1 x"  "l1 ! rep_of l1 y = rep_of l1 y"
      using assms(5,6) invar1 length_eq rep_of_min by auto
    with assms(12) consider (x) "rep_of l1 x = rep_of l1 x2" | (y) "rep_of l1 x = rep_of l1 y2"
      by (metis False assms(5) assms(6) assms(7) assms(8) invar1 length_eq ufa_union_aux union(1))
    then show ?thesis 
    proof(cases)
      case x
      from assms have "rep_of l1 y = rep_of l1 y2" 
        by (metis False invar1 length_eq ufa_union_aux union(1) x)
      from assms have "path l (rep_of l y) [rep_of l y, rep_of l1 x] (rep_of l1 x)"
        by (metis False \<open>l ! rep_of l1 x2 = rep_of l1 y2\<close> \<open>rep_of l1 y = rep_of l1 y2\<close> \<open>rep_of l1 y2 = rep_of l y2\<close> invar1 length_eq path.step rep_of_less_length_l rep_of_ufa_union_invar single union(1) x)
      obtain p_rep_x where p_rep_x: "path l1 (rep_of l1 x) p_rep_x x" 
        using assms(5) invar1 length_eq path_to_rep_of by auto
      with path_ufe_union_invar assms have  "path l (rep_of l1 x) p_rep_x x" 
        by (metis length_eq ufe_data_structure.select_convs(1))
      with p_rep_x have p_rep_x': "path l (rep_of l x) (rep_of l y#p_rep_x) x" 
        by (metis False \<open>l ! rep_of l1 x2 = rep_of l1 y2\<close> \<open>rep_of l1 y = rep_of l1 y2\<close> assms(6) invar1 length_eq path.step path_nodes_lt_length_l rep_of_bound ufa_union_aux union(1) x)
      with path_to_root_correct path_unique have path_to_root_x: "path_to_root l x = rep_of l y#p_rep_x" 
        using assms(5) invar by blast
      obtain p_rep_y where p_rep_y': "path l1 (rep_of l1 y) (rep_of l1 y#p_rep_y) y" 
        using assms(6) invar1 length_eq path_to_rep_of by (metis path.simps)
      then have p_rep_y: "path l (rep_of l y) (rep_of l y#p_rep_y) y" 
        using assms(5) invar1 length_eq path_to_rep_of 
        by (metis (no_types, lifting) False \<open>rep_of l1 y = rep_of l1 y2\<close> invar path_nodes_lt_length_l path_to_root_correct path_to_root_ufa_union1 path_unique ufa_union_aux union(1) x)
      with path_to_root_correct path_unique have path_to_root_y: "path_to_root l y = rep_of l y#p_rep_y" 
        using assms(6) invar by blast
      have "longest_common_prefix (path_to_root l x) (path_to_root l y) = [rep_of l y]"
      proof(rule ccontr, cases "length p_rep_y > 0 \<and> length p_rep_x > 0")
        case True
        assume "longest_common_prefix (path_to_root l x) (path_to_root l y) \<noteq> [rep_of l y]"
        with True have "hd p_rep_y = hd p_rep_x" 
          by (metis list.sel(1) longest_common_prefix.elims longest_common_prefix.simps(1) path_to_root_x path_to_root_y)
        have "hd p_rep_x = rep_of l1 x2" 
          using p_rep_x path_hd x by auto
        then have "path l1 (rep_of l1 x2) p_rep_y y" 
          by (metis True \<open>hd p_rep_y = hd p_rep_x\<close> length_greater_0_conv list_tail_coinc p_rep_y' path.cases path_hd)
        then have "rep_of l1 x2 = rep_of l1 y" 
          by (metis invar1 p_rep_x path_rep_eq x)
        then show "False" using False x by linarith
      next
        case False
        assume "longest_common_prefix (path_to_root l x) (path_to_root l y) \<noteq> [rep_of l y]"
        then show "False" 
          using False \<open>path l (rep_of l1 x) p_rep_x x\<close> path_to_root_x path_to_root_y by force
      qed
      with assms have lca: "lca = rep_of l x" by simp
      from length_u_max have "i < length (p_rep_x) \<Longrightarrow> a1 ! (p_rep_x ! i) < Some (length u1)" for i 
        using \<open>length a1 = length l1\<close> nodes_path_lt_length_l p_rep_x by force
      then have "i < length p_rep_x \<Longrightarrow> i > 0 \<Longrightarrow> a ! (p_rep_x ! i) < Some (length u1)" for i 
        by (metis \<open>l1 ! rep_of l1 x = rep_of l1 x\<close> nth_list_update_neq p_rep_x path_not_first_no_root union(2) x)
      moreover have "hd (p_rep_x) = rep_of l1 x2" 
        using p_rep_x path_hd x by simp
      moreover have "(rep_of l y#p_rep_x) ! (i+1) = p_rep_x ! i" for i
        by simp
      ultimately have *:"i < length (rep_of l y # p_rep_x) \<Longrightarrow> i > 1 \<Longrightarrow> a ! ((rep_of l y # p_rep_x) ! i) < Some (length u1)" for i  
        by simp
      have **: "a ! ((rep_of l y # p_rep_x) ! 1) = Some (length u1)"
        by (metis "**" \<open>\<And>i. (rep_of l y # p_rep_x) ! (i + 1) = p_rep_x ! i\<close> \<open>hd p_rep_x = rep_of l1 x2\<close> ab_semigroup_add_class.add.commute add.right_neutral hd_conv_nth p_rep_x path_not_empty)
      have *: "i < length (rep_of l y # p_rep_x) \<Longrightarrow> i \<ge> 1 \<Longrightarrow> a ! ((rep_of l y # p_rep_x) ! i) \<le> Some (length u1)" for i  
        apply(cases "i > 1")
        using * ** by fastforce+
      have "x \<noteq> rep_of l x"
        by (metis \<open>path l (rep_of l1 x) p_rep_x x\<close> assms(5) invar list_tail_coinc p_rep_x' path_no_cycle path_not_empty)
      with lca find_newest_on_path_correct[OF p_rep_x' invar] path_unique assms
      have "newest_index_x = (MAX i \<in> set [1..<length (rep_of l y#p_rep_x)]. a ! ((rep_of l y#p_rep_x) ! i))"
        using invar p_rep_x' by blast
      also have "(MAX i \<in> set [1..<length (rep_of l y#p_rep_x)]. a ! ((rep_of l y#p_rep_x) ! i)) = a ! ((rep_of l y # p_rep_x) ! 1)"
      proof-
        let ?set = "((\<lambda> i . a ! ((rep_of l y#p_rep_x) ! i)) ` (set [1..<length (rep_of l y#p_rep_x)]))"
        have finite: "finite ?set"
          by simp
        have length: "length (rep_of l y#p_rep_x) > 1" 
          by (metis \<open>path l (rep_of l1 x) p_rep_x x\<close> impossible_Cons list.distinct(1) nat_geq_1_eq_neqz nat_less_le path_not_empty slice_complete slice_eq_bounds_empty)
        then  have *: "i \<in> set [1..<length (rep_of l y#p_rep_x)] \<Longrightarrow> a ! ((rep_of l y#p_rep_x) ! i) \<le> Some (length u1)" for i
          using * by auto
        moreover have "1 \<in> set [1..<length (rep_of l y#p_rep_x)]" 
          by (metis length list.set_intros(1) upt_eq_Cons_conv)
        moreover have "Some (length u1) \<in> ?set"
          using ** by (metis calculation(2) rev_image_eqI)
        ultimately have "Some (length u1) = Max ?set"
          using  Max_eqI finite * 
          by (smt (verit) image_iff)
        then show ?thesis 
          using "**" by presburger
      qed
      with assms have "newest_index_x = a ! (rep_of l1 x)" 
        by (metis "**" \<open>length a1 = length l1\<close> \<open>rep_of l1 x2 < length l1\<close> calculation nth_list_update_eq union(2) x)
      then have "u ! (the (a ! rep_of l1 x)) = (ax, bx)" 
        by (simp add: assms(11))
      moreover have "u ! (the (a ! rep_of l1 x)) = (x2, y2)" 
        by (simp add: \<open>a ! rep_of l1 x2 = Some (length u1)\<close> union(3) x)
      ultimately have "ax = x2" and "bx = y2" by simp_all
      then show ?thesis 
        using \<open>rep_of l1 y = rep_of l1 y2\<close> assms(2) x by fastforce
    next
      case y
        \<comment> \<open>not possible, because newest_index_x > newest_index_y\<close>
      from assms(4-) explain_index_neq[of "\<lparr>uf_list = l, unions = u, au = a\<rparr>"] ufe_invar 
      have "newest_index_x > newest_index_y" 
        by fastforce
      from assms have "rep_of l1 y = rep_of l1 x2" 
        by (metis False invar1 length_eq ufa_union_aux union(1) y)
      with assms have "path l (rep_of l y) [rep_of l y, rep_of l1 y] (rep_of l1 y)"
        by (metis False \<open>l ! rep_of l1 x2 = rep_of l1 y2\<close>  \<open>rep_of l1 y2 = rep_of l y2\<close> invar1 length_eq path.step rep_of_less_length_l rep_of_ufa_union_invar single union(1) y)
      obtain p_rep_x where p_rep_x: "path l1 (rep_of l1 y) p_rep_x y" 
        using assms(6) invar1 length_eq path_to_rep_of by auto
      with path_ufe_union_invar assms have  "path l (rep_of l1 y) p_rep_x y" 
        by (metis length_eq ufe_data_structure.select_convs(1))
      with p_rep_x have p_rep_x': "path l (rep_of l y) (rep_of l y#p_rep_x) y" 
        by (metis False \<open>l ! rep_of l1 x2 = rep_of l1 y2\<close> \<open>l ! rep_of l1 y2 = rep_of l1 y2\<close> \<open>rep_of l x2 = l ! rep_of l1 y2\<close> \<open>rep_of l1 x2 < length l1\<close> \<open>rep_of l1 y = rep_of l1 x2\<close> assms(6) assms(7) assms(8) invar invar1 length_eq path.step rep_of_ufa_union_invar ufa_invarD(2) union(1) y)
      with path_to_root_correct path_unique have path_to_root_x: "path_to_root l y = rep_of l y#p_rep_x" 
        using assms(6) invar by blast
      obtain p_rep_y where p_rep_y': "path l1 (rep_of l1 x) (rep_of l1 x#p_rep_y) x" 
        using assms(5) invar1 length_eq path_to_rep_of by (metis path.simps)
      then have p_rep_y: "path l (rep_of l x) (rep_of l y#p_rep_y) x" 
        using assms(5,6) invar1 length_eq path_to_rep_of 
        by (metis (no_types, lifting) False \<open>rep_of l1 y = rep_of l1 x2\<close> invar path_to_root_correct path_to_root_ufa_union1 path_unique ufa_union_aux union(1) y)
      with path_to_root_correct path_unique have path_to_root_y: "path_to_root l x = rep_of l y#p_rep_y" 
        using assms(5) invar by blast
      have "longest_common_prefix (path_to_root l x) (path_to_root l y) = [rep_of l y]"
      proof(rule ccontr, cases "length p_rep_y > 0 \<and> length p_rep_x > 0")
        case True
        assume "longest_common_prefix (path_to_root l x) (path_to_root l y) \<noteq> [rep_of l y]"
        with True have "hd p_rep_y = hd p_rep_x" 
          by (metis list.sel(1) longest_common_prefix.elims longest_common_prefix.simps(1) path_to_root_x path_to_root_y)
        have "hd p_rep_x = rep_of l1 y2" 
          using p_rep_x path_hd y 
          by (metis True \<open>hd p_rep_y = hd p_rep_x\<close> \<open>l1 ! rep_of l1 y = rep_of l1 y\<close> length_greater_0_conv list_tail_coinc p_rep_y' path.cases)
        then have "path l1 (rep_of l1 y2) p_rep_y x" 
          by (metis True \<open>hd p_rep_y = hd p_rep_x\<close> length_greater_0_conv list_tail_coinc p_rep_y' path.cases path_hd)
        then have "rep_of l1 y2 = rep_of l1 y"
          using \<open>hd p_rep_x = rep_of l1 y2\<close> p_rep_x path_hd by auto 
        then show "False" using False y by presburger
      next
        case False
        assume "longest_common_prefix (path_to_root l x) (path_to_root l y) \<noteq> [rep_of l y]"
        then show "False" 
          by (metis False \<open>path l (rep_of l1 y) p_rep_x y\<close> length_greater_0_conv longest_common_prefix.simps(1) longest_common_prefix.simps(2) path_not_empty path_to_root_x path_to_root_y)
      qed
      with assms have lca: "lca = rep_of l x" by simp
      from length_u_max have "i < length (p_rep_x) \<Longrightarrow> a1 ! (p_rep_x ! i) < Some (length u1)" for i 
        using \<open>length a1 = length l1\<close> nodes_path_lt_length_l p_rep_x by force
      then have "i < length p_rep_x \<Longrightarrow> i > 0 \<Longrightarrow> a ! (p_rep_x ! i) < Some (length u1)" for i 
        by (metis \<open>l1 ! rep_of l1 y = rep_of l1 y\<close> \<open>rep_of l1 y = rep_of l1 x2\<close> nth_list_update_neq p_rep_x path_not_first_no_root union(2))
      moreover have "hd (p_rep_x) = rep_of l1 x2" 
        using p_rep_x path_hd \<open>rep_of l1 y = rep_of l1 x2\<close> by auto
      moreover have "(rep_of l y#p_rep_x) ! (i+1) = p_rep_x ! i" for i
        by simp
      ultimately have *:"i < length (rep_of l y # p_rep_x) \<Longrightarrow> i > 1 \<Longrightarrow> a ! ((rep_of l y # p_rep_x) ! i) < Some (length u1)" for i  
        by simp
      have **: "a ! ((rep_of l y # p_rep_x) ! 1) = Some (length u1)"
        by (metis "**" \<open>\<And>i. (rep_of l y # p_rep_x) ! (i + 1) = p_rep_x ! i\<close> \<open>hd p_rep_x = rep_of l1 x2\<close> ab_semigroup_add_class.add.commute add.right_neutral hd_conv_nth p_rep_x path_not_empty)
      have *: "i < length (rep_of l y # p_rep_x) \<Longrightarrow> i \<ge> 1 \<Longrightarrow> a ! ((rep_of l y # p_rep_x) ! i) \<le> Some (length u1)" for i  
        apply(cases "i > 1")
        using * ** by fastforce+
      have "y \<noteq> rep_of l y" 
        by (metis \<open>path l (rep_of l1 y) p_rep_x y\<close> assms(6) invar list_tail_coinc p_rep_x' path_no_cycle path_not_empty)
      with lca find_newest_on_path_correct[OF p_rep_x' invar] path_unique assms
      have "newest_index_y = (MAX i \<in> set [1..<length (rep_of l y#p_rep_x)]. a ! ((rep_of l y#p_rep_x) ! i))"
        using invar p_rep_x' by metis
      also have "(MAX i \<in> set [1..<length (rep_of l y#p_rep_x)]. a ! ((rep_of l y#p_rep_x) ! i)) = Some (length u1)"
      proof-
        let ?set = "((\<lambda> i . a ! ((rep_of l y#p_rep_x) ! i)) ` (set [1..<length (rep_of l y#p_rep_x)]))"
        have finite: "finite ?set"
          by simp
        have length: "length (rep_of l y#p_rep_x) > 1" 
          by (metis \<open>path l (rep_of l1 y) p_rep_x y\<close> impossible_Cons list.distinct(1) nat_geq_1_eq_neqz nat_less_le path_not_empty slice_complete slice_eq_bounds_empty)
        then  have *: "i \<in> set [1..<length (rep_of l y#p_rep_x)] \<Longrightarrow> a ! ((rep_of l y#p_rep_x) ! i) \<le> Some (length u1)" for i
          using * by auto
        moreover have "1 \<in> set [1..<length (rep_of l y#p_rep_x)]" 
          by (metis length list.set_intros(1) upt_eq_Cons_conv)
        moreover have "Some (length u1) \<in> ?set"
          using ** by (metis calculation rev_image_eqI)
        ultimately have "Some (length u1) = Max ?set"
          using  Max_eqI finite * 
          by (smt (verit) image_iff)
        then show ?thesis 
          using "**" by presburger
      qed
      with assms have "newest_index_y = Some (length u1)"
        using calculation by presburger
      obtain pLca where "path l lca pLca x" 
        by (metis lca p_rep_y)
      from assms have "lca \<noteq> x" 
        using explain_case_x_x_neq_lca ufe_invar by blast
      with assms ufe_invar explain_case_x_newest_index_index obtain i pLca where "path l lca pLca x \<and> newest_index_x = (a ! (pLca ! i)) \<and> i < length pLca \<and> i > 0"
        by metis
      then have "newest_index_x \<le> Some (length u1)" 
        by (metis \<open>length a1 = length l1\<close> \<open>newest_index_y < newest_index_x\<close> \<open>newest_index_y = Some (length u1)\<close> length_eq length_u_max nodes_path_lt_length_l nth_list_update_eq nth_list_update_neq order.asym union(2))
      then have "False" 
        using \<open>newest_index_y < newest_index_x\<close> \<open>newest_index_y = Some (length u1)\<close> verit_comp_simplify1(3) by blast
      then show ?thesis by simp
    qed
  qed
  then show "rep_of (uf_list ufe_before) ax = rep_of (uf_list ufe_before) x" 
    "rep_of (uf_list ufe_before) bx = rep_of (uf_list ufe_before) y" by simp_all
qed

paragraph \<open>The order of the parameters in explain can be switched\<close>

lemma explain_symmetric_domain:
  assumes "explain_dom (ufe, x, y)"
    and "ufe_invar ufe"
    and "x < length (uf_list ufe)" and "y < length (uf_list ufe)"
  shows "explain_dom (ufe, y, x)"
  using assms proof(induction ufe x y rule: explain.pinduct)
  case (1 l u a x y)
  then have invar: "ufa_invar l"
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  define lca' newest_index_x' newest_index_y' axbx' ayby' 
    where defs1: "lca' = lowest_common_ancestor l y x"
      "newest_index_x' = find_newest_on_path l a y lca'"
      "newest_index_y' = find_newest_on_path l a x lca'"
      "axbx' = u ! the (newest_index_x')" 
      "ayby' = u ! the (newest_index_y')"
  obtain ax' bx' ay' by' where defs2: "(ax', bx') = axbx'"
    "(ay', by') = ayby'" by (metis prod.exhaust_sel)
  note defs = defs1 defs2
  then show ?case 
  proof(cases rule: explain_cases[of l u a x y])
    case base
    then show ?thesis using explain_empty_domain by auto
  next
    case (case_x ufe lca newest_index_x newest_index_y ax bx ay "by")
    with defs lowest_common_ancestor_symmetric have "lca = lca'" 
      by presburger
    then have "newest_index_x' = newest_index_y" 
      and  "newest_index_y' = newest_index_x"
      by (auto simp add: case_x defs)
    then have equalities: "ax' = ay"  "ay' = ax"  "bx' = by"  "by' = bx"
      by (metis Pair_inject case_x defs)+
    from lowest_common_ancestor_correct case_x "1.prems" invar 
    obtain p where  p: "path l lca p x" 
      by (metis ufe_data_structure.select_convs(1))
    obtain k_x where k_x: "newest_index_x = Some k_x \<and> k_x < length u" "ax < length l" "bx < length l"
      using case_x explain_case_x_newest_index_x_Some 
      by (metis "1.prems" ufe_data_structure.select_convs(1))
    have *: "explain_dom (ufe, x, ax)" "explain_dom (ufe, bx, y)"
      using "1.hyps" case_x explain_domain_cases(1,2) by metis+
    from explain_index_neq case_x "1.prems" have "\<not> newest_index_y' \<le> newest_index_x'" 
      by (metis  \<open>newest_index_x' = newest_index_y\<close> \<open>newest_index_y' = newest_index_x\<close> dual_order.eq_iff ufe_data_structure.select_convs(1))
    then have "explain_dom (ufe, x, ay')" "explain_dom (ufe, by', y)"
      by (auto simp add: "*" equalities)
    with 1 case_x k_x show ?thesis 
      by (metis  \<open>\<not> newest_index_y' \<le> newest_index_x'\<close>  \<open>lca = lca'\<close> \<open>newest_index_x' = newest_index_y\<close> \<open>newest_index_y' = newest_index_x\<close> defs1(1) explain_case_y_domain option.sel ufe_data_structure.select_convs(1))
  next
    case (case_y ufe lca newest_index_x newest_index_y ax bx ay "by")
    with defs lowest_common_ancestor_symmetric have "lca = lca'" 
      by presburger
    then have "newest_index_x' = newest_index_y" 
      and  "newest_index_y' = newest_index_x"
      by (auto simp add: case_y defs)
    then have equalities: "ax' = ay"  "ay' = ax"  "bx' = by"  "by' = bx"
      by (metis Pair_inject case_y defs)+
    from lowest_common_ancestor_correct case_y "1.prems" invar 
    obtain p where  p:"path l lca p y" 
      by (metis ufe_data_structure.select_convs(1))
    with find_newest_x_neq_None_or_find_newest_y_neq_None case_y "1.prems"
    obtain k_y' where "newest_index_y = Some k_y'" 
      by (metis less_eq_option_None option.exhaust_sel)
    with find_newest_on_path_if_Some have "y ~= lca" 
      by (metis case_y(4) find_newest_on_path.domintros invar p path_nodes_lt_length_l)
    with find_newest_on_path_Some[OF p "1.prems"(1)] "1.prems" case_y 
    obtain k_y where k_y: "newest_index_y = Some k_y \<and> k_y < length u" 
      by blast
    with "1.prems" have "fst (u ! k_y) < length l" "snd (u ! k_y) < length l"
      by auto
    then have "ay < length l" "by < length l"
      by (metis k_y case_y(6) fst_conv snd_conv option.sel)+
    have "newest_index_y' \<le> newest_index_x'" 
      using \<open>newest_index_x' = newest_index_y\<close> \<open>newest_index_y' = newest_index_x\<close> case_y(8) by auto
    have *: "explain_dom (ufe, x, by)" "explain_dom (ufe, ay, y)"
      using "1.hyps" case_y explain_domain_cases(3,4) by metis+
    then have "explain_dom (ufe, x, bx')" "explain_dom (ufe, ax', y)"
      by (auto simp add: "*" equalities)
    with 1 case_y show ?thesis 
      by (metis \<open>ay < length l\<close> \<open>by < length l\<close> \<open>lca = lca'\<close> \<open>newest_index_x' = newest_index_y\<close> \<open>newest_index_y' = newest_index_x\<close> \<open>newest_index_y' \<le> newest_index_x'\<close> defs1(1) explain_case_x_domain ufe_data_structure.select_convs(1))
  qed
qed

theorem explain_symmetric:
  assumes "explain_dom (ufe, x, y)"
    and "ufe_invar ufe"
    and "x < length (uf_list ufe)" and "y < length (uf_list ufe)"
  shows "explain ufe x y = explain ufe y x"
  using assms proof(induction ufe x y rule: explain.pinduct)
  case (1 l u a x y)
  then have invar: "ufa_invar l"
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  define lca' newest_index_x' newest_index_y' axbx' ayby' 
    where defs1: "lca' = lowest_common_ancestor l y x"
      "newest_index_x' = find_newest_on_path l a y lca'"
      "newest_index_y' = find_newest_on_path l a x lca'"
      "axbx' = u ! the (newest_index_x')" 
      "ayby' = u ! the (newest_index_y')"
  obtain ax' bx' ay' by' where defs2: "(ax', bx') = axbx'"
    "(ay', by') = ayby'" by (metis prod.exhaust_sel)
  note defs = defs1 defs2
  then show ?case 
  proof(cases rule: explain_cases[of l u a x y])
    case base
    then show ?thesis by auto
  next
    case (case_x ufe lca newest_index_x newest_index_y ax bx ay "by")
    with defs lowest_common_ancestor_symmetric have "lca = lca'" 
      by presburger
    then have "newest_index_x' = newest_index_y" 
      and  "newest_index_y' = newest_index_x"
      by (auto simp add: case_x defs)
    then have equalities: "ax' = ay"  "ay' = ax"  "bx' = by"  "by' = bx"
      by (metis Pair_inject case_x defs)+
    obtain k_x where k_x: "newest_index_x = Some k_x \<and> k_x < length u" "ax < length l" "bx < length l"
      using case_x explain_case_x_newest_index_x_Some 
      by (metis "1.prems" ufe_data_structure.select_convs(1))
    have *: "explain ufe x y = {(ax, bx)} \<union> explain ufe x ax \<union> explain ufe bx y"
      using "1.hyps" case_x explain_case_x by presburger
    from explain_index_neq case_x "1.prems" have "\<not> newest_index_y' \<le> newest_index_x'" 
      by (metis "1.hyps" \<open>newest_index_x' = newest_index_y\<close> \<open>newest_index_y' = newest_index_x\<close> dual_order.eq_iff ufe_data_structure.select_convs(1))
    with explain_case_y have "explain ufe y x = {(ay', by')} \<union> explain ufe y by' \<union> explain ufe ay' x" 
      using case_x "1.hyps" "1.IH"(1,2) defs  explain_symmetric_domain 
      by (metis "1.prems")
    also have "...= {(ax, bx)} \<union> explain ufe x ax \<union> explain ufe bx y"
      using "1.hyps" case_x explain_case_y equalities "1.IH"(1,2)
      using "1.prems" k_x by auto
    finally show ?thesis by (metis "*" case_x(1))
  next
    case (case_y ufe lca newest_index_x newest_index_y ax bx ay "by")
    with defs lowest_common_ancestor_symmetric have "lca = lca'" 
      by presburger
    then have "newest_index_x' = newest_index_y" 
      and  "newest_index_y' = newest_index_x"
      by (auto simp add: case_y defs)
    then have equalities: "ax' = ay"  "ay' = ax"  "bx' = by"  "by' = bx"
      by (metis Pair_inject case_y defs)+
    from lowest_common_ancestor_correct case_y "1.prems" invar
    obtain p where p: "path l lca p y" 
      by (metis ufe_data_structure.select_convs(1))
    with find_newest_x_neq_None_or_find_newest_y_neq_None case_y "1.prems"
    obtain k_y' where "newest_index_y = Some k_y'" 
      by (metis less_eq_option_None option.exhaust_sel)
    with find_newest_on_path_if_Some have "y ~= lca" 
      by (metis case_y(4) find_newest_on_path.domintros invar p path_nodes_lt_length_l)
    with find_newest_on_path_Some[OF p "1.prems"(1)] "1.prems" case_y 
    obtain k_y where k_y: "newest_index_y = Some k_y \<and> k_y < length u" 
      by blast
    with "1.prems" have "fst (u ! k_y) < length l" "snd (u ! k_y) < length l"
      by auto
    then have "ay < length l" "by < length l"
      by (metis k_y case_y(6) fst_conv snd_conv option.sel)+
    have *: "explain ufe x y = {(ay, by)} \<union> explain ufe x by \<union> explain ufe ay y" 
      using "1.hyps" case_y explain_case_y by presburger
    have "newest_index_y' \<le> newest_index_x'" 
      using \<open>newest_index_x' = newest_index_y\<close> \<open>newest_index_y' = newest_index_x\<close> case_y(8) by auto 
    then have "explain ufe y x = {(ax', bx')} \<union> explain ufe y ax' \<union> explain ufe bx' x"
      using case_y 1 defs explain_case_x
      by (metis explain_symmetric_domain)
    also have "...= {(ay, by)} \<union> explain ufe x by \<union> explain ufe ay y" 
      using "1.hyps" "1.IH"(3) "1.IH"(4) case_y explain_case_x equalities 
      using "1.prems" \<open>ay < length l\<close> \<open>by < length l\<close> by auto
    then show ?thesis 
      by (metis "*" calculation case_y(1))
  qed
qed

paragraph \<open>A better case rule for proofs about explain\<close>

text \<open>Given that case_y and case_y are symmetric, we can prove case_y
      more easily with this new case rule. It needs to be used with the 
      \<open>induction\<close> proof method. \<close>

lemma explain_cases_simple[consumes 3, case_names base case_x case_y]:
  assumes "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x < length l" and "y < length l"
    and "\<And> x y ufe . ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr> 
\<Longrightarrow> ufe_invar ufe
\<Longrightarrow> x < length l \<Longrightarrow> y < length l
\<Longrightarrow> x = y \<or> rep_of l x \<noteq> rep_of l y \<Longrightarrow> P x y"
    and "\<And> ufe lca newest_index_x newest_index_y ax bx ay by x y.
  ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>
\<Longrightarrow> ufe_invar ufe
\<Longrightarrow> x < length l \<Longrightarrow> y < length l
\<Longrightarrow> lca = lowest_common_ancestor l x y
\<Longrightarrow> newest_index_x = find_newest_on_path l a x lca
\<Longrightarrow> newest_index_y = find_newest_on_path l a y lca
\<Longrightarrow> (ax, bx) = u ! the (newest_index_x)
\<Longrightarrow> (ay, by) = u ! the (newest_index_y)
\<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)
\<Longrightarrow> newest_index_x > newest_index_y
\<Longrightarrow> P x y"
    and "\<And> ufe lca newest_index_x newest_index_y ax bx ay by x y.
P y x \<Longrightarrow> ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>
\<Longrightarrow> ufe_invar ufe
\<Longrightarrow> x < length l \<Longrightarrow> y < length l
\<Longrightarrow> lca = lowest_common_ancestor l x y
\<Longrightarrow> newest_index_x = find_newest_on_path l a x lca
\<Longrightarrow> newest_index_y = find_newest_on_path l a y lca
\<Longrightarrow> (ax, bx) = u ! the (newest_index_x)
\<Longrightarrow> (ay, by) = u ! the (newest_index_y)
\<Longrightarrow> \<not>(x = y \<or> rep_of l x \<noteq> rep_of l y)
\<Longrightarrow> newest_index_x < newest_index_y
\<Longrightarrow> P x y"
  shows "P x y"
proof-
  define lca' newest_index_x' newest_index_y' axbx' ayby' 
    where defs1: "lca' = lowest_common_ancestor l x y"
      "newest_index_x' = find_newest_on_path l a x lca'"
      "newest_index_y' = find_newest_on_path l a y lca'"
      "axbx' = u ! the (newest_index_x')" 
      "ayby' = u ! the (newest_index_y')"
  obtain ax' bx' ay' by' where defs2: "(ax', bx') = axbx'"
    "(ay', by') = ayby'" by (metis prod.exhaust_sel)
  note defs = defs1 defs2 
  consider (a) "newest_index_x' > newest_index_y'"
    | (b) "newest_index_x' = newest_index_y'"
    | (c) "newest_index_x' < newest_index_y'"
    using linorder_less_linear by auto
  then show ?thesis 
  proof(cases)
    case a 
    with assms defs show ?thesis 
      by metis
  next
    case b
    with assms defs  show ?thesis 
      by (metis explain_index_neq)
  next
    case c
    with assms defs  show ?thesis 
      by (metis lowest_common_ancestor_symmetric ufe_data_structure.select_convs(1))
  qed
qed

subsection \<open>\<open>explain\<close> termination\<close>

lemma explain_domain_ufe_union_invar:
  assumes "explain_dom (ufe, x, y)"
    and "ufe_invar ufe"
    and "x2 < length (uf_list ufe)"
    and "y2 < length (uf_list ufe)"
    and "x < length (uf_list ufe)"
    and "y < length (uf_list ufe)"
    and "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y"
  shows "explain_dom (ufe_union ufe x2 y2, x, y)"
  using assms proof(induction rule: explain.pinduct)
  case (1 l u a x y)
  then have induction_assms: "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr>" "x < length l" "y < length l"
    apply blast
    using 1 by (metis ufe_data_structure.select_convs(1))+
  from induction_assms 1 show ?case
  proof(induction rule: explain_cases_simple)
    case (base x y ufe)
    from "base.hyps"(5) "base.prems"(11) show ?case 
      using explain_empty_domain by auto
  next
    case (case_x ufe lca newest_index_x newest_index_y ax bx ay "by" x y)
    with rep_of_ufe_union_invar 
    have rep: "rep_of (uf_list (ufe_union ufe x2 y2)) x = rep_of (uf_list (ufe_union ufe x2 y2)) y"
      by metis
    with case_x ufe_invar_imp_ufa_invar have "ufa_invar l"
      by (metis ufe_data_structure.select_convs(1))
    obtain l2 u2 a2 where ufe_union: "ufe_union ufe x2 y2 = \<lparr>uf_list = l2, unions = u2, au = a2\<rparr>" 
      using ufe_data_structure.cases by blast 
    show ?case 
    proof(cases "rep_of l x2 = rep_of l y2")
      case True
      with ufe_union case_x ufe_union1_ufe have "ufe_union ufe x2 y2 = ufe" 
        by simp
      with case_x show ?thesis 
        by presburger
    next
      case False
      have "l2 = ufa_union l x2 y2" "u2 = u @ [(x2, y2)]" "a2 = a[rep_of l x2 := Some (length u)]"
        using False case_x ufe_union by simp+
      define lca' newest_index_x' newest_index_y' axbx' ayby' 
        where defs1: "lca' = lowest_common_ancestor l2 x y"
          "newest_index_x' = find_newest_on_path l2 a2 x lca'"
          "newest_index_y' = find_newest_on_path l2 a2 y lca'"
          "axbx' = u2 ! the (newest_index_x')" 
          "ayby' = u2 ! the (newest_index_y')"
      obtain ax' bx' ay' by' where defs2: "(ax', bx') = axbx'"
        "(ay', by') = ayby'" by (metis prod.exhaust_sel)
      note defs = defs1 defs2
      from explain_case_x_rep_of_ax_bx case_x 
      have **: "rep_of l ax = rep_of l x" "rep_of l y = rep_of l bx"
        by (metis order_less_imp_le)+
      with case_x explain_case_x_newest_index_x_Some have *:
        "explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, x, ax)"
        "explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, bx, y)"
        by (metis ufe_data_structure.select_convs(1) order_less_imp_le)+
          \<comment> \<open>ax and bx stay the same after the union\<close>
      from case_x "1.prems" ufe_union 
      have lca_eq: "lca = lca'" 
        by (metis \<open>l2 = ufa_union l x2 y2\<close> \<open>ufa_invar l\<close> defs1(1) lowest_common_ancestor_ufa_union_invar ufe_data_structure.select_convs(1))
      with "1.prems" case_x lowest_common_ancestor_correct obtain plx where  plx: "path l lca plx x" 
        by (metis \<open>ufa_invar l\<close> ufe_data_structure.select_convs(1))
      with find_newest_on_path_ufe_union_invar 
      have nix_eq: "newest_index_x' = newest_index_x" 
        using case_x defs ufe_union lca_eq path_nodes_lt_length_l "1.prems"   
        by (metis ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))
      have  "x < length (uf_list ufe)" "y < length (uf_list ufe)" 
        using "1.prems" case_x by auto
      then obtain k_x where k_x: "newest_index_x = Some k_x \<and> k_x < length u" 
           "ax < length l" "bx < length l"
        using case_x explain_case_x_newest_index_x_Some
        by (metis ufe_data_structure.select_convs(1) order_less_imp_le)
      with "1.prems" ufe_union case_x unions_ufe_union_invar have "(ax, bx) = axbx'" 
        by (metis defs1(4) nix_eq option.sel ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(2))
      with defs have ax_bx_eq: "ax = ax'" "bx = bx'"
        by (metis Pair_inject)+
      from k_x case_x have length_ax_ay: "ax < length (uf_list ufe)" "bx < length (uf_list ufe)" 
        by auto
      with * ax_bx_eq have **: 
        "explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, x, ax')"
        "explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, bx', y)"
        by auto
      from "1.prems" lca_eq case_x lowest_common_ancestor_correct 
      obtain ply where ply: "path l lca ply y" 
        by (metis \<open>ufa_invar l\<close> ufe_data_structure.select_convs(1))
      with "1.prems" defs case_x find_newest_on_path_ufe_union_invar 
      have "newest_index_y' = newest_index_y" 
        by (metis lca_eq path_nodes_lt_length_l ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3) ufe_union)
      with rep ** explain_case_x_domain
        defs ufe_union case_x(1,7,8) nix_eq
      show ?thesis 
        by (metis case_x.hyps(11) explain_empty_domain nless_le)
    qed
  next
    case (case_y ufe lca newest_index_x newest_index_y ax bx ay "by" x y)
    then have dom: "explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, y, x)" 
      using explain_symmetric_domain by presburger
    have *: "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr>"
      "x2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
      "y2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
      "y < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
      "x < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
      "rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) y = rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) x"
      using induction_assms(1) apply blast
      using case_y.prems(7-11) by auto
        \<comment>\<open>We need to prove the induction hypotheses for the symmetric case.\<close>
    with explain_symmetric_domain union_ufe_invar *(1) ufe_union_length_uf_list 
      linorder_not_less case_y lowest_common_ancestor_symmetric  
    have a: "(\<And>xa xba xc xaa xab ya xac xad yba.
        \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
        xa = lowest_common_ancestor l y x \<Longrightarrow>
        xba = find_newest_on_path l a y xa \<Longrightarrow>
        xc = find_newest_on_path l a x xa \<Longrightarrow>
        xaa = u ! the xba \<Longrightarrow>
        (xab, ya) = xaa \<Longrightarrow>
        xac = u ! the xc \<Longrightarrow>
        (xad, yba) = xac \<Longrightarrow>
        xc \<le> xba \<Longrightarrow>
        ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
        x2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        y2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        y < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        xab < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) y =
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) xab \<Longrightarrow>
        explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, y, xab))"  
      by (metis ufe_data_structure.select_convs(1))
    with explain_symmetric_domain union_ufe_invar *(1) ufe_union_length_uf_list 
      linorder_not_less case_y lowest_common_ancestor_symmetric  
    have b: "(\<And>xa xba xc xaa xab ya xac xad yba.
        \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
        xa = lowest_common_ancestor l y x \<Longrightarrow>
        xba = find_newest_on_path l a y xa \<Longrightarrow>
        xc = find_newest_on_path l a x xa \<Longrightarrow>
        xaa = u ! the xba \<Longrightarrow>
        (xab, ya) = xaa \<Longrightarrow>
        xac = u ! the xc \<Longrightarrow>
        (xad, yba) = xac \<Longrightarrow>
        xc \<le> xba \<Longrightarrow>
        ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
        x2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        y2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        ya < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        x < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) ya =
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) x \<Longrightarrow>
        explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, ya, x))"
      by (metis ufe_data_structure.select_convs(1))
    with explain_symmetric_domain union_ufe_invar *(1) ufe_union_length_uf_list 
      linorder_not_less case_y lowest_common_ancestor_symmetric  
      linorder_le_cases
    have c: "(\<And>xa xba xc xaa xab ya xac xad yba.
        \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
        xa = lowest_common_ancestor l y x \<Longrightarrow>
        xba = find_newest_on_path l a y xa \<Longrightarrow>
        xc = find_newest_on_path l a x xa \<Longrightarrow>
        xaa = u ! the xba \<Longrightarrow>
        (xab, ya) = xaa \<Longrightarrow>
        xac = u ! the xc \<Longrightarrow>
        (xad, yba) = xac \<Longrightarrow>
        \<not> xc \<le> xba \<Longrightarrow>
        ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
        x2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        y2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        y < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        yba < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) y =
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) yba \<Longrightarrow>
        explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, y, yba))"
      by metis
    with explain_symmetric_domain union_ufe_invar *(1) ufe_union_length_uf_list 
      linorder_not_less case_y lowest_common_ancestor_symmetric  
      linorder_le_cases
    have d: "(\<And>xa xba xc xaa xab ya xac xad yba.
        \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
        xa = lowest_common_ancestor l y x \<Longrightarrow>
        xba = find_newest_on_path l a y xa \<Longrightarrow>
        xc = find_newest_on_path l a x xa \<Longrightarrow>
        xaa = u ! the xba \<Longrightarrow>
        (xab, ya) = xaa \<Longrightarrow>
        xac = u ! the xc \<Longrightarrow>
        (xad, yba) = xac \<Longrightarrow>
        \<not> xc \<le> xba \<Longrightarrow>
        ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
        x2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        y2 < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        xad < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        x < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) \<Longrightarrow>
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) xad =
        rep_of (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>) x \<Longrightarrow>
        explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, xad, x))"
      by metis
    from * a b c d case_y dom
    have "explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, y, x)" 
      by blast
    with explain_symmetric_domain case_y.prems induction_assms ufe_union_length_uf_list union_ufe_invar show ?case 
      by (metis ufe_data_structure.select_convs(1))
  qed
qed

theorem explain_domain:
  assumes "ufe_invar ufe"
    and "x < length (uf_list ufe)"
    and "y < length (uf_list ufe)"
  shows "explain_dom (ufe, x, y)"
  using assms proof(induction arbitrary: x y rule: apply_unions_induct)
  case initial
  obtain l1 u1 a1 where initial_ufe: "initial_ufe (length (uf_list ufe)) = 
    \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with initial.prems rep_of_refl have "x = y \<or> rep_of l1 x \<noteq> rep_of l1 y"
    by force
  then show ?case using explain.domintros 
    using initial_ufe by blast
next
  case (union pufe x2 y2)
  obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  obtain l2 u2 a2 where pufe_union: "ufe_union pufe x2 y2 = \<lparr>uf_list = l2, unions = u2, au = a2\<rparr>" 
    using ufe_data_structure.cases by blast 
  with union pufe union_ufe_invar have induction_assms: 
"ufe_invar \<lparr>uf_list = l2, unions = u2, au = a2\<rparr>" "x < length l2" "y < length l2"
    by (metis ufe_data_structure.select_convs(1))+
  from induction_assms pufe union pufe_union show ?case
  proof(induction rule: explain_cases_simple)
    case (base x y ufe)
    then show ?case 
      using explain_empty_domain pufe_union by auto
  next
    case (case_x ufe lca newest_index_x newest_index_y ax bx ay "by" x y)
    with explain_case_x_newest_index_x_Some(2,3) case_x order_less_imp_le
    have lengths: "ax < length l2" "bx < length l2"
      by (metis ufe_data_structure.select_convs(1))+
    then have lengths'': "ax < length l1" "bx < length l1"
      by (metis pufe pufe_union ufe_data_structure.select_convs(1) ufe_union_length_uf_list)+
    from case_x pufe_union union.hyps(2,3) ufe_union_length_uf_list
    have l: "x < length l2" "y < length l2" "x2 < length l2" "y2 < length l2"
      by (metis ufe_data_structure.select_convs(1))+
    then have lengths': "x < length (uf_list pufe)" "y < length l1" 
      by (metis pufe pufe_union ufe_data_structure.select_convs(1) ufe_union_length_uf_list)+
    with lengths case_x have *: "explain_dom (pufe, x, ax)" "explain_dom (pufe, bx, y)"
      by (metis pufe_union ufe_data_structure.select_convs(1) ufe_union_length_uf_list)+
    from explain_case_x_rep_of_ax_bx_ufe_union[OF case_x(13,12,19)] l case_x 
    have "rep_of l1 x = rep_of l1 ax" "rep_of l1 y = rep_of l1 bx" 
      by (metis dual_order.strict_iff_not ufe_data_structure.select_convs(1))+
    with  explain_domain_ufe_union_invar * union(1,2,3) lengths' union lengths
    have "explain_dom (ufe_union pufe x2 y2, x, ax)"
      "explain_dom (ufe_union pufe x2 y2, bx, y)"
      by (metis pufe pufe_union ufe_data_structure.select_convs(1) ufe_union_length_uf_list)+
    with case_x have "explain_dom (\<lparr>uf_list = l2, unions = u2, au = a2\<rparr>, x, ax)"
      "explain_dom (\<lparr>uf_list = l2, unions = u2, au = a2\<rparr>, bx, y)"
      by (metis)+
    with explain_case_x_domain case_x(1-12, 19) order_less_imp_le
    show ?case by metis
  next
    case (case_y ufe lca newest_index_x newest_index_y ax bx ay "by" x y)
    then have "explain_dom (ufe_union pufe x2 y2, y, x)" 
       by fastforce
    with explain_symmetric_domain case_y show ?case 
      by (metis pufe_union)
  qed
qed

subsection \<open>\<open>explain\<close> correctness\<close>

theorem explain_valid:
  assumes "ufe_invar ufe"
    and "x < length (uf_list ufe)"
    and "y < length (uf_list ufe)"
    and "xy \<in> (explain ufe x y)"
  shows "xy \<in> set (unions ufe)"
proof-
  from assms explain_domain have "explain_dom (ufe, x, y)"
    by simp
  then show ?thesis
    using assms proof(induction ufe x y arbitrary: xy rule: explain.pinduct)
    case (1 l u a x y)
    then show ?case
    proof(cases "x = y \<or> rep_of l x \<noteq> rep_of l y")
      case True
      with 1 explain_empty show ?thesis
        by simp
    next
      case False
      let ?lca = "lowest_common_ancestor l x y"
      let ?newest_index_x = "find_newest_on_path l a x ?lca"
        and ?newest_index_y = "find_newest_on_path l a y ?lca"
      let ?axbx = "u ! the ?newest_index_x"
        and ?ayby = "u ! the ?newest_index_y"
      from "1.prems" have "ufa_invar l" 
        by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
      from lowest_common_ancestor_correct 1 False obtain pLcaX where 
        pLcaX: "path l ?lca pLcaX x" 
        by (metis \<open>ufa_invar l\<close> ufe_data_structure.select_convs(1))
      then have domain_x: "find_newest_on_path_dom (l, a, x, ?lca)"
        by (simp add: \<open>ufa_invar l\<close> find_newest_on_path_domain path_nodes_lt_length_l)
      from lowest_common_ancestor_correct 1 False obtain pLcaY where 
        pLcaY: "path l ?lca pLcaY y" 
        by (metis \<open>ufa_invar l\<close> ufe_data_structure.select_convs(1))
      then have domain_y: "find_newest_on_path_dom (l, a, y, ?lca)"
        by (simp add: \<open>ufa_invar l\<close> find_newest_on_path_domain path_nodes_lt_length_l)
      from find_newest_x_neq_None_or_find_newest_y_neq_None 1 False
      have not_both_None: "?newest_index_x \<noteq> None \<or> ?newest_index_y \<noteq> None" 
        by (metis ufe_data_structure.select_convs(1))
      obtain ax ay bx "by" where a: "?axbx = (ax, bx)" and b: "?ayby = (ay, by)"
        by (meson prod_decode_aux.cases)
      show ?thesis 
      proof(cases "?newest_index_x \<ge> ?newest_index_y")
        case True
        with not_both_None False have "?newest_index_x \<noteq> None"
          by (metis less_eq_option_None_is_None)
        then have "x \<noteq> ?lca" 
          using domain_x find_newest_on_path.psimps by fastforce
        then obtain k where k: "?newest_index_x = Some k \<and> k < length u"
          using "1.prems" pLcaX find_newest_on_path_Some by blast
        then have index_valid: "k < length u"
          by auto
        from 1 have ax_valid: "ax < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
          by (metis k a fst_conv option.sel ufe_data_structure.select_convs(2))
        with a b 1 True have 2: "xy \<in> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax 
\<Longrightarrow> xy \<in> set (unions \<lparr>uf_list = l, unions = u, au = a\<rparr>)" 
          by (metis False)
        from a b 1 True False have 3: "xy \<in> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y 
\<Longrightarrow> xy \<in> set (unions \<lparr>uf_list = l, unions = u, au = a\<rparr>)"   
          by (metis k option.sel snd_conv ufe_data_structure.select_convs(2))
        from index_valid have 4: "(ax, bx) \<in> set (unions \<lparr>uf_list = l, unions = u, au = a\<rparr>)" 
          using a nth_mem False True 
          by (metis k option.sel ufe_data_structure.select_convs(2))
        from 1(1) True a False have "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
                                  {(ax, bx)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax 
                                  \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y"
          by simp 
        with 2 3 4 show ?thesis
          using "1.prems"(4) by auto
      next 
        case False': False
        with not_both_None False have "?newest_index_y \<noteq> None"
          by fastforce
        then have "y \<noteq> ?lca" 
          using domain_y find_newest_on_path.psimps by fastforce
        then obtain k where k: "?newest_index_y = Some k \<and> k < length u"
          using "1.prems" pLcaY find_newest_on_path_Some by blast
        then have index_valid: "k < length u"
          by auto
        from 1 have ay_valid: "ay < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
          by (metis b fst_conv k option.sel ufe_data_structure.select_convs(2))
        with a b 1 False False' have 2: "xy \<in> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x by 
\<Longrightarrow> xy \<in> set (unions \<lparr>uf_list = l, unions = u, au = a\<rparr>)" 
          by (metis k option.sel snd_eqD ufe_data_structure.select_convs(2))
        from a b 1 False' False have 3: "xy \<in> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ay y 
\<Longrightarrow> xy \<in> set (unions \<lparr>uf_list = l, unions = u, au = a\<rparr>)"   
          by (metis ay_valid)
        from index_valid have 4: "(ay, by) \<in> set (unions \<lparr>uf_list = l, unions = u, au = a\<rparr>)" 
          using b nth_mem False False' 
          by (metis k option.sel ufe_data_structure.select_convs(2))
        from 1(1) False' b False have "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
                                    {(ay, by)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x by 
                                    \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ay y"
          by (simp add: explain.psimps Let_def split: nat.splits) 
        with 2 3 4 show ?thesis
          using "1.prems"(4) by auto
      qed
    qed
  qed
qed

lemma explain_ufe_union_invar:
  assumes "ufe_invar ufe"
    and "ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>"
    and "x < length l1" and "y < length l1" and "x2 < length l1" and "y2 < length l1"
  shows "explain ufe x y \<subseteq> explain (ufe_union ufe x2 y2) x y"
proof-
  from assms explain_domain have dom: "explain_dom (ufe, x, y)"
    by simp
  from dom assms show ?thesis
  proof(induction arbitrary: l1 u1 a1 rule: explain.pinduct)
    case (1 l u a x y)
    then have induction_assms: "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr>" "x < length l" "y < length l"
      by (metis ufe_data_structure.select_convs(1))+
    from induction_assms 1 show ?case
    proof(induction rule: explain_cases_simple)
      case (base x y ufe)
      with explain_empty have "explain ufe x y = {}"
        by force
      with base show ?case by blast
    next
      case (case_x ufe lca newest_index_x newest_index_y ax bx ay "by" x y)
      obtain l2 u2 a2 where union: "ufe_union ufe x2 y2 = \<lparr>uf_list = l2, unions = u2, au = a2\<rparr>"
        using ufe_data_structure.cases by blast
      with case_x rep_of_ufe_union_invar have rep: "rep_of l2 x = rep_of l2 y"
        by (metis ufe_data_structure.select_convs(1))
      define lca' newest_index_x' newest_index_y' axbx' ayby' 
        where defs1: "lca' = lowest_common_ancestor l2 x y"
          "newest_index_x' = find_newest_on_path l2 a2 x lca'"
          "newest_index_y' = find_newest_on_path l2 a2 y lca'"
          "axbx' = u2 ! the (newest_index_x')" 
          "ayby' = u2 ! the (newest_index_y')"
      obtain ax' bx' ay' by' where defs2: "(ax', bx') = axbx'"
        "(ay', by') = ayby'" by (metis prod.exhaust_sel)
      note defs = defs1 defs2
      with lowest_common_ancestor_ufe_union_invar case_x
      have lca: "lca = lca'" 
        by (metis ufe_data_structure.select_convs(1) union)
      from 1 have invar: "ufa_invar l" 
        by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
      with lowest_common_ancestor_correct case_x
      obtain px where px: "path l lca px x" 
        by (metis ufe_data_structure.ext_inject)
      with find_newest_on_path_ufe_union_invar case_x defs lca
      have newest_index_x: "newest_index_x = newest_index_x'"
        by (metis path_nodes_lt_length_l ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3) union)
      from invar lowest_common_ancestor_correct case_x 1
      obtain py where py: "path l lca py y" 
        by (metis ufe_data_structure.ext_inject)
      with find_newest_on_path_ufe_union_invar case_x defs lca
      have newest_index_y: "newest_index_y = newest_index_y'"
        by (metis path_nodes_lt_length_l ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3) union)
      from case_x explain_case_x_x_neq_lca have "lca \<noteq> x" 
        by (metis ufe_data_structure.select_convs(1) order_less_imp_le)
      with find_newest_on_path_Some px
      obtain k where k: "newest_index_x = Some k \<and> k < length u" 
        using case_x by metis
      with newest_index_x have "the newest_index_x = the newest_index_x'"
        by simp
      with newest_index_x defs case_x unions_ufe_union_invar union
      have "(ax, bx) = axbx'" 
        by (metis k option.sel ufe_data_structure.select_convs(2))
      then have "ax = ax'" and "bx = bx'" 
        using defs2(1) by auto
      with case_x have IH: "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax \<subseteq> explain (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2) x ax"
        "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y \<subseteq> explain (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2) bx y"
        by (metis explain_case_x_newest_index_x_Some(2,3) ufe_data_structure.ext_inject order_less_imp_le)+
      from "1.prems" have "ufe_invar \<lparr>uf_list = l2, unions = u2, au = a2\<rparr>" 
        by (metis case_x(1) union union_ufe_invar)
      with explain_domain have "explain_dom (\<lparr>uf_list = l2, unions = u2, au = a2\<rparr>, x, y)" 
        by (metis case_x(1) path_nodes_lt_length_l px py ufe_data_structure.select_convs(1) ufe_union_length_uf_list union)
      with explain_case_x newest_index_x newest_index_y defs rep
      have explain_union: "explain \<lparr>uf_list = l2, unions = u2, au = a2\<rparr> x y
=  {(ax', bx')} \<union> explain \<lparr>uf_list = l2, unions = u2, au = a2\<rparr> x ax' \<union>
  explain \<lparr>uf_list = l2, unions = u2, au = a2\<rparr> bx' y" 
        using case_x.hyps(11) order.strict_implies_order by blast
      with explain_case_x case_x.hyps
      have "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y
=  {(ax, bx)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax \<union>
  explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y"
        by (metis case_x.prems(1) order_less_imp_le)
      then show ?case 
        using \<open>ax = ax'\<close> \<open>bx = bx'\<close> IH  case_x(1) explain_union union by auto
    next
      case (case_y ufe lca newest_index_x newest_index_y ax bx ay "by" x y)
      then have dom: "\<And> x y. x < length l \<Longrightarrow> y < length l \<Longrightarrow> explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, y, x)"
        "\<And> x y. x < length l \<Longrightarrow> y < length l \<Longrightarrow> explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, y, x)"
        apply (metis explain_domain ufe_data_structure.select_convs(1))
        using case_y.hyps case_y.prems(7-11) union_ufe_invar explain_domain 
        by (metis ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
      then have *: "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> "
        "\<lparr>uf_list = l, unions = u, au = a\<rparr> = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>"
        "y < length l1"
        "x < length l1"
        "x2 < length l1"
        "y2 < length l1"
        using induction_assms(1) apply blast
        using case_y.prems(7-11) by auto
          \<comment>\<open>We need to prove the induction hypotheses for the symmetric case.\<close>
      with dom explain_symmetric union_ufe_invar *(1) ufe_union_length_uf_list 
        linorder_not_less case_y lowest_common_ancestor_symmetric  
      have a: "(\<And>xa xb xc xaa xab ya xac xad yb l1 u1 a1.
            \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
            xa = lowest_common_ancestor l y x \<Longrightarrow>
            xb = find_newest_on_path l a y xa \<Longrightarrow>
            xc = find_newest_on_path l a x xa \<Longrightarrow>
            xaa = u ! the xb \<Longrightarrow>
            (xab, ya) = xaa \<Longrightarrow>
            xac = u ! the xc \<Longrightarrow>
            (xad, yb) = xac \<Longrightarrow>
            xc \<le> xb \<Longrightarrow>
            ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
            \<lparr>uf_list = l, unions = u, au = a\<rparr> = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> \<Longrightarrow>
            y < length l1 \<Longrightarrow>
            xab < length l1 \<Longrightarrow>
            x2 < length l1 \<Longrightarrow>
            y2 < length l1 \<Longrightarrow>
            explain \<lparr>uf_list = l, unions = u, au = a\<rparr> y xab
            \<subseteq> explain (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2) y xab)"
        by (metis ufe_data_structure.select_convs(1))
      with dom explain_symmetric union_ufe_invar *(1) ufe_union_length_uf_list 
        linorder_not_less case_y lowest_common_ancestor_symmetric 
      have b: "(\<And>xa xb xc xaa xab ya xac xad yb l1 u1 a1.
            \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
            xa = lowest_common_ancestor l y x \<Longrightarrow>
            xb = find_newest_on_path l a y xa \<Longrightarrow>
            xc = find_newest_on_path l a x xa \<Longrightarrow>
            xaa = u ! the xb \<Longrightarrow>
            (xab, ya) = xaa \<Longrightarrow>
            xac = u ! the xc \<Longrightarrow>
            (xad, yb) = xac \<Longrightarrow>
            xc \<le> xb \<Longrightarrow>
            ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
            \<lparr>uf_list = l, unions = u, au = a\<rparr> = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> \<Longrightarrow>
            ya < length l1 \<Longrightarrow>
            x < length l1 \<Longrightarrow>
            x2 < length l1 \<Longrightarrow>
            y2 < length l1 \<Longrightarrow>
            explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ya x
            \<subseteq> explain (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2) ya x)"
        by (metis ufe_data_structure.select_convs(1))
      with dom explain_symmetric union_ufe_invar *(1) ufe_union_length_uf_list 
        linorder_not_less case_y lowest_common_ancestor_symmetric  
        linorder_le_cases
      have c: "(\<And>xa xb xc xaa xab ya xac xad yb l1 u1 a1.
            \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
            xa = lowest_common_ancestor l y x \<Longrightarrow>
            xb = find_newest_on_path l a y xa \<Longrightarrow>
            xc = find_newest_on_path l a x xa \<Longrightarrow>
            xaa = u ! the xb \<Longrightarrow>
            (xab, ya) = xaa \<Longrightarrow>
            xac = u ! the xc \<Longrightarrow>
            (xad, yb) = xac \<Longrightarrow>
            \<not> xc \<le> xb \<Longrightarrow>
            ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
            \<lparr>uf_list = l, unions = u, au = a\<rparr> = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> \<Longrightarrow>
            y < length l1 \<Longrightarrow>
            yb < length l1 \<Longrightarrow>
            x2 < length l1 \<Longrightarrow>
            y2 < length l1 \<Longrightarrow>
            explain \<lparr>uf_list = l, unions = u, au = a\<rparr> y yb
            \<subseteq> explain (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2) y yb)"
        by metis
      with dom explain_symmetric union_ufe_invar *(1) ufe_union_length_uf_list 
        linorder_not_less case_y lowest_common_ancestor_symmetric  
        linorder_le_cases
      have d: "(\<And>xa xb xc xaa xab ya xac xad yb l1 u1 a1.
            \<not> (y = x \<or> rep_of l y \<noteq> rep_of l x) \<Longrightarrow>
            xa = lowest_common_ancestor l y x \<Longrightarrow>
            xb = find_newest_on_path l a y xa \<Longrightarrow>
            xc = find_newest_on_path l a x xa \<Longrightarrow>
            xaa = u ! the xb \<Longrightarrow>
            (xab, ya) = xaa \<Longrightarrow>
            xac = u ! the xc \<Longrightarrow>
            (xad, yb) = xac \<Longrightarrow>
            \<not> xc \<le> xb \<Longrightarrow>
            ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr> \<Longrightarrow>
            \<lparr>uf_list = l, unions = u, au = a\<rparr> = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> \<Longrightarrow>
            xad < length l1 \<Longrightarrow>
            x < length l1 \<Longrightarrow>
            x2 < length l1 \<Longrightarrow>
            y2 < length l1 \<Longrightarrow>
            explain \<lparr>uf_list = l, unions = u, au = a\<rparr> xad x
            \<subseteq> explain (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2) xad x)"
        by metis
      with dom * a b c d 
      have y_x: "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> y x \<subseteq> explain (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2) y x"
        using case_y.IH by blast
      have union_invar: "ufe_invar (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2)" 
        using case_y.prems(10) case_y.prems(11) case_y.prems(7) induction_assms(1) union_ufe_invar by presburger
      from case_y(2,3) explain_domain have  "explain_dom (\<lparr>uf_list = l, unions = u, au = a\<rparr>, y, x)"
        "explain_dom (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x2 y2, y, x)"
        apply (simp add: case_y.hyps(3) case_y.hyps(4))
        using case_y(2,3) explain_domain union_ufe_invar case_y.hyps(3) case_y.hyps(4) 
        by (metis union_invar ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
      with explain_symmetric explain_domain case_y(2) show ?case 
        by (metis y_x case_y.hyps(3) case_y.hyps(4) induction_assms(1) ufe_data_structure.select_convs(1) ufe_union_length_uf_list union_invar)
    qed
  qed
qed

lemma explain_ufe_union_invar2:
  assumes "ufe_invar ufe"
    and "ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>"
    and "x < length l1" and "y < length l1" and "x2 < length l1" and "y2 < length l1"
    and "(a, b) \<in> (symcl (explain ufe x y))\<^sup>*" 
  shows "(a, b) \<in> (symcl (explain (ufe_union ufe x2 y2) x y))\<^sup>*"
proof-
  from explain_ufe_union_invar assms 
  have "(explain ufe x y) \<subseteq> (explain (ufe_union ufe x2 y2) x y)" by presburger
  with symcl_def have "symcl (explain ufe x y) \<subseteq> symcl (explain (ufe_union ufe x2 y2) x y)"
    by (metis Un_mono converse_mono)
  with explain_ufe_union_invar assms 
    rtrancl_mono_mp[of "symcl (explain ufe x y)" "symcl (explain (ufe_union ufe x2 y2) x y)"] 
  show ?thesis by blast
qed

text \<open>The transitive, reflexive, symmetric closure of \<open>explain ufe x y\<close> must contain (x, y).\<close>

lemma eqcl_union: "a \<in> (symcl A)\<^sup>* \<Longrightarrow> a \<in> (symcl (A \<union> B))\<^sup>*"
  by (metis Un_mono Un_upper1 converse_mono rtrancl_mono_mp symcl_def)

theorem explain_correct:
  assumes "ufe_invar ufe"
    and "x < length (uf_list ufe)"
    and "y < length (uf_list ufe)"
    and "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y"
  shows "(x, y) \<in> (symcl (explain ufe x y))\<^sup>*"
proof-
  from assms explain_domain have "explain_dom (ufe, x, y)"
    by simp
  then show ?thesis
    using assms proof(induction ufe x y rule: explain.pinduct)
    case (1 l u a x y)
    then show ?case
    proof(cases "x = y \<or> rep_of l x \<noteq> rep_of l y")
      case True
      with 1 explain_empty show ?thesis
        by simp
    next
      case False
      let ?lca = "lowest_common_ancestor l x y"
      let ?newest_index_x = "find_newest_on_path l a x ?lca"
        and ?newest_index_y = "find_newest_on_path l a y ?lca"
      let ?axbx = "u ! the ?newest_index_x"
        and ?ayby = "u ! the ?newest_index_y"
      from "1.prems" have "ufa_invar l" 
        by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
      from lowest_common_ancestor_correct 1 False obtain pLcaX where 
        pLcaX: "path l ?lca pLcaX x" 
        by (metis \<open>ufa_invar l\<close> ufe_data_structure.select_convs(1))
      then have domain_x: "find_newest_on_path_dom (l, a, x, ?lca)"
        by (simp add: \<open>ufa_invar l\<close> find_newest_on_path_domain path_nodes_lt_length_l)
      from lowest_common_ancestor_correct 1 False obtain pLcaY where 
        pLcaY: "path l ?lca pLcaY y" 
        by (metis \<open>ufa_invar l\<close> ufe_data_structure.select_convs(1))
      then have domain_y: "find_newest_on_path_dom (l, a, y, ?lca)"
        by (simp add: \<open>ufa_invar l\<close> find_newest_on_path_domain path_nodes_lt_length_l)
      from find_newest_x_neq_None_or_find_newest_y_neq_None 1 False
      have not_both_None: "?newest_index_x \<noteq> None \<or> ?newest_index_y \<noteq> None" 
        by (metis ufe_data_structure.select_convs(1))
      obtain ax ay bx "by" where a: "?axbx = (ax, bx)" and b: "?ayby = (ay, by)"
        by (meson prod_decode_aux.cases)
      show ?thesis 
      proof(cases "?newest_index_x \<ge> ?newest_index_y")
        case True
        with not_both_None False have "?newest_index_x \<noteq> None"
          by (metis less_eq_option_None_is_None)
        then have "x \<noteq> ?lca" 
          using domain_x find_newest_on_path.psimps by fastforce
        then obtain k where k: "?newest_index_x = Some k \<and> k < length u"
          using "1.prems" pLcaX find_newest_on_path_Some by blast
        then have index_valid: "k < length u"
          by auto
        from 1 have ax_valid: "ax < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
"bx < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
           by (metis k a fst_conv snd_conv option.sel ufe_data_structure.select_convs(2))+ 
        from "1.prems" a b have "rep_of l x = rep_of l ax" 
          "rep_of l y = rep_of l bx" using explain_case_x_rep_of_ax_bx 
          by (metis False True ufe_data_structure.select_convs(1))+
        with a b 1 True ax_valid have 2:
"(x, ax) \<in> (symcl (explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax))\<^sup>*"
"(bx, y) \<in> (symcl (explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y))\<^sup>*"
          by (metis False ufe_data_structure.select_convs(1))+
        from 1(1) True a False have recursive_step: "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
                                  {(ax, bx)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x ax 
                                  \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> bx y"
          by simp 
        then have "(ax, bx) \<in> (symcl (explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y))"
          unfolding symcl_def by blast
        with 2 show ?thesis
          using "1.prems"(4) recursive_step
          by (metis converse_rtrancl_into_rtrancl eqcl_union rtrancl_trans sup_commute)
      next 
        case False'': False
        then have False': "?newest_index_x < ?newest_index_y" 
          by simp
        with not_both_None False have "?newest_index_y \<noteq> None"
          by fastforce
        then have "y \<noteq> ?lca" 
          using domain_y find_newest_on_path.psimps by fastforce
        then obtain k where k: "?newest_index_y = Some k \<and> k < length u"
          using "1.prems" pLcaY find_newest_on_path_Some by blast
        then have index_valid: "k < length u"
          by auto
        from 1 have ay_valid: "ay < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
"by < length (uf_list \<lparr>uf_list = l, unions = u, au = a\<rparr>)"
          by (metis b fst_conv snd_conv k option.sel ufe_data_structure.select_convs(2))+
        from "1.prems" a b have "rep_of l x = rep_of l by" 
          "rep_of l y = rep_of l ay" using explain_case_y_rep_of_ay_by 
          by (metis False False' ufe_data_structure.select_convs(1))+
        with a b 1 False False' False'' ay_valid have 2: 
"(x, by) \<in> (symcl (explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x by))\<^sup>*"
"(ay, y) \<in> (symcl (explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ay y))\<^sup>*"
          by (metis ay_valid ufe_data_structure.select_convs(1))+
        from 1(1) False' b False have recursive_step: 
                                    "explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y = 
                                    {(ay, by)} \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x by 
                                    \<union> explain \<lparr>uf_list = l, unions = u, au = a\<rparr> ay y"
          by (simp add: explain.psimps Let_def split: nat.splits) 
        then have "(ay, by) \<in> (symcl (explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y))"
          unfolding symcl_def by blast
        then have "(by, ay) \<in> (symcl (explain \<lparr>uf_list = l, unions = u, au = a\<rparr> x y))"
          unfolding symcl_def by fast
        with 2 show ?thesis
          using "1.prems"(4) recursive_step 
          by (metis eqcl_union r_into_rtrancl rtrancl_trans sup_commute)
      qed
    qed
  qed
qed


text \<open>Invariant: the edges near the root are newer.\<close>

lemma edges_near_root_newer:
  assumes invar: "ufe_invar ufe"
    and lt_length: "i < length (uf_list ufe)"
  assumes no_root: "(uf_list ufe) ! i \<noteq> (uf_list ufe) ! ((uf_list ufe) ! i)"
  shows "(au ufe) ! i < (au ufe) ! ((uf_list ufe) ! i)"
  using assms proof(induction rule: apply_unions_induct)
  case initial
  then show ?case by simp
next
  case (union pufe x y)
  have i: "i < length (uf_list pufe)" 
    using ufe_union_length_uf_list union.prems(1) by auto
  then show ?case 
  proof(cases "uf_list pufe ! i = uf_list pufe ! (uf_list pufe ! i)")
    case True
      \<comment> \<open>(l ! i) was a root.\<close>
    with union ufe_invar_imp_ufa_invar have inv: "ufa_invar (uf_list pufe)" 
      by blast
    obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
      using ufe_data_structure.cases by blast
    then have rep_neq: "rep_of l1 x \<noteq> rep_of l1 y" 
      using True union.prems(2) by force
    with pufe union have i_no_root: "l1 ! i \<noteq> i "
      by (metis i inv nth_list_update_eq nth_list_update_neq rep_of_root ufe_data_structure.select_convs(1) ufe_union2_uf_list)
    from rep_neq have *: "au (ufe_union \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> x y) = a1[rep_of l1 x := Some (length u1)]"
      by simp
        \<comment> \<open>(l ! i) is not a root any more.\<close>
    from i_no_root rep_of_root have **: "rep_of l1 x = l1 ! i" 
      by (metis True inv nth_list_update_neq pufe rep_neq ufe_data_structure.select_convs(1) ufe_union2_uf_list union.hyps(2) union.hyps(3) union.prems(2))
    from inv union have length_l1: "l1 ! i < length l1" 
      by (metis i pufe ufa_invarD(2) ufe_data_structure.select_convs(1))
    from union length_au pufe have length_a1: "length l1 = length a1" 
      by (metis ufe_data_structure.select_convs(1,3))
    with pufe * have au_parent: "au (ufe_union pufe x y) ! (l1 ! i) = Some (length u1)"  
      by (metis length_l1 ** nth_list_update_eq)
    with au_Some_valid union * have "au (ufe_union pufe x y) ! i < Some (length u1)" 
      by (metis length_l1 length_a1 ** au_valid i i_no_root nth_list_update pufe ufe_data_structure.select_convs(1-3))
    then show ?thesis
      by (metis au_parent ** i_no_root nth_list_update_neq pufe rep_neq ufe_data_structure.select_convs(1) ufe_union2_uf_list)
  next
    case False
      \<comment> \<open>(l ! i) was not a root.\<close>
    with au_none_iff_root obtain k where k: "au pufe ! ((uf_list pufe) ! i) = Some k" 
      using i union.hyps(1) by (metis less_option_None not_None_eq union.IH)
    have "uf_list (ufe_union pufe x y) ! i \<noteq> uf_list (ufe_union pufe x y) ! (uf_list (ufe_union pufe x y) ! i)"
      using union.prems(2) by blast
    with au_ufe_union_Some_invar False
    have a: "au (ufe_union pufe x y) ! (uf_list pufe ! i) = au pufe ! (uf_list pufe ! i)" 
      using k union by presburger
    from union have b: "au pufe ! i < au pufe ! (uf_list pufe ! i)" 
      using False i by linarith
    then have "au pufe ! (uf_list pufe ! i) \<noteq> None" 
      by (metis less_option_None)
    from False have *: "uf_list pufe ! i \<noteq> i" 
      by auto
    obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>"
      using ufe_data_structure.cases by blast
    with * obtain k2 where k2: "a1 ! i = Some k2" 
      using i union.hyps(1) au_none_iff_root by force
    have "uf_list (ufe_union pufe x y) ! i \<noteq> i" 
      using union.prems(2) by auto
    then have c: "au (ufe_union pufe x y) ! i = au pufe ! i" 
      using au_ufe_union_Some_invar pufe k2 union 
      by (metis ufe_data_structure.select_convs(3))
    have "au (ufe_union pufe x y) ! (uf_list (ufe_union pufe x y) ! i)
            = au pufe ! (uf_list pufe ! i)" using no_root_ufe_union_invar
      using * a pufe union.hyps by auto
    with a b c show ?thesis by auto
  qed
qed



end