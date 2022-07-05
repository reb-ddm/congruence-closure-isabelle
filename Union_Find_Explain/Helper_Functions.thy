section \<open>Correctness proofs for the helper functions\<close>
theory Helper_Functions
  imports Path 
begin 

subsection \<open>Proofs about the domain of the helper functions\<close>

text \<open>The domain of \<open>path_to_root\<close> is the same as the domain of \<open>rep_of\<close>.\<close>

lemma path_to_root_rel: "rep_of_rel x y \<longleftrightarrow> path_to_root_rel x y" 
proof
  show "rep_of_rel x y \<Longrightarrow> path_to_root_rel x y"
    by (induction x y rule: rep_of_rel.induct) (auto simp add: path_to_root_rel.intros)
next
  show "path_to_root_rel x y \<Longrightarrow> rep_of_rel x y"
    by (induction x y rule: path_to_root_rel.induct) (auto simp add: rep_of_rel.intros)
qed

lemma path_to_root_domain: "rep_of_dom (l, i) \<longleftrightarrow> path_to_root_dom (l, i)" 
  using path_to_root_rel by presburger

subsection \<open>Correctness proof for \<open>path_to_root\<close>.\<close>

theorem path_to_root_correct:
  assumes "ufa_invar l"
    and "x < length l"
  shows "path l (rep_of l x) (path_to_root l x) x"
  using assms proof(induction l x rule: rep_of_induct)
  case (base i)
  with path_to_root.psimps have "path_to_root l i = [i]" 
    using base.hyps path_to_root_domain ufa_invarD(1) by auto
  then show ?case 
    using base path_to_root.psimps base single rep_of_refl by auto
next
  case (step i)
  then have "path l (rep_of l (l ! i)) (path_to_root l (l ! i)) (l ! i)" 
    using ufa_invar_def by blast
  moreover have "path l (l ! i) [l ! i, i] i" 
    using step calculation path.step path_nodes_lt_length_l single by auto
  ultimately show ?case 
    using step path_to_root.psimps path_concat1 rep_of_idx path_to_root_domain ufa_invarD(1) by fastforce
qed

lemma path_to_root_length: "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> length (path_to_root l x) > 0"
proof-
  assume "ufa_invar l" "x < length l"
  have "path_to_root_dom(l, x)" 
    using \<open>ufa_invar l\<close> \<open>x < length l\<close> path_to_root_domain ufa_invarD(1) by auto
  then show ?thesis
    apply(induction rule: path_to_root.pinduct)
    by (simp add: path_to_root.psimps)
qed

subsection \<open>Correctness of \<open>lowest_common_ancestor\<close>.\<close>

abbreviation "common_ancestor l x y ca \<equiv>
(\<exists> p . path l ca p x) \<and>
(\<exists> p . path l ca p y)"

abbreviation "Lowest_common_ancestor l x y ca \<equiv>
(common_ancestor l x y ca \<and> 
(\<forall>r ca2 p3 p4. (path l r p3 ca \<and> path l r p4 ca2 \<and> common_ancestor l x y ca2 
\<longrightarrow> length p3 \<ge> length p4)))"

theorem lowest_common_ancestor_correct:    
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "rep_of l x = rep_of l y"
  shows "Lowest_common_ancestor l x y (lowest_common_ancestor l x y)"
proof-
  have path_root_x: "path l (rep_of l x) (path_to_root l x) x"
    using assms path_to_root_correct by metis
  have path_root_y: "path l (rep_of l y) (path_to_root l y) y"
    using assms path_to_root_correct by metis
  let ?lca = "lowest_common_ancestor l x y"
  let ?lcp = "longest_common_prefix (path_to_root l x) (path_to_root l y)"
  from path_root_x path_root_y path_hd have lcp_not_empty: "?lcp \<noteq> []" 
    by (metis assms(4) list.distinct(1) list.sel(1) list_encode.cases longest_common_prefix.simps(1) path_not_empty)
  obtain p1 where p1_def: "path_to_root l x = ?lcp @ p1"
    using longest_common_prefix_prefix1 prefixE by blast
  from path_divide1 have path_lca_x: "path l ?lca (?lca # p1) x"
    using lcp_not_empty lowest_common_ancestor.simps p1_def path_root_x by presburger
  obtain p2 where p2_def: "(path_to_root l y) = ?lcp @ p2"
    using longest_common_prefix_prefix2 prefixE by blast
  from path_divide1 have path_lca_y: "path l ?lca (?lca # p2) y"
    using p2_def lcp_not_empty lowest_common_ancestor.simps path_root_y by presburger
  then have commmon_ancestor: "common_ancestor l x y ?lca" 
    using path_lca_x by auto
  have "path l r p3 ?lca \<and> path l r p4 ca \<and> common_ancestor l x y ca
\<Longrightarrow> length p3 \<ge> length p4"
    for r p3 p4 ca
  proof(rule ccontr)
    assume assm: "path l r p3 (lowest_common_ancestor l x y) \<and> path l r p4 ca \<and> common_ancestor l x y ca"
      and length: "\<not> length p4 \<le> length p3"
    then obtain pCaY pCaX where pCaY: "path l ca pCaY y" and pCaX: "path l ca pCaX x"
      by blast
    then obtain pRootR where pRootR: "path l (rep_of l x) pRootR r" 
      by (metis assm assms(1) path_nodes_lt_length_l path_rep_eq path_to_root_correct)
    have path_root_ca: "path l (rep_of l x) (pRootR @ tl p4) ca" 
      using assm pRootR path_concat1 by auto
    then have "path l (rep_of l x) (pRootR @ tl p4 @ tl pCaX) x" 
      using pCaX path_concat1 by fastforce 
    then have *: "path_to_root l x = pRootR @ tl p4 @ tl pCaX" 
      using assms(1) path_root_x path_unique by auto
    have "path l (rep_of l x) (pRootR @ tl p4 @ tl pCaY) y" 
      using pCaY path_concat1 path_root_ca by fastforce
    then have "path_to_root l y = pRootR @ tl p4 @ tl pCaY" 
      using assms(1,4) path_root_y path_unique by simp
    then have prefix1: "prefix (pRootR @ tl p4) (path_to_root l x)" 
      and prefix2: "prefix (pRootR @ tl p4) (path_to_root l y)"
      using * by fastforce+
    have path_root_lca: "path l (rep_of l x) (pRootR @ tl p3) ?lca" 
      using assm pRootR path_concat1 by blast
    then have "path l (rep_of l x) (pRootR @ tl p3 @ p1) x" 
      using path_concat1 path_lca_x by fastforce
    then have *: "path_to_root l x = pRootR @ tl p3 @ p1" 
      using assms(1) path_root_x path_unique by auto
    have "path l (rep_of l x) (pRootR @ tl p3 @ p2) y" 
      using path_concat1 path_lca_y path_root_lca by fastforce
    then have "path_to_root l y = pRootR @ tl p3 @ p2" 
      using assms(1) assms(4) path_root_y path_unique by auto
    have "\<not> prefix ?lcp (pRootR @ tl p4)" 
      by (metis "*" Orderings.order_eq_iff prefix1 prefix2 append.assoc append_eq_append_conv assm assms(1) length longest_common_prefix_max_prefix p1_def path_last path_root_ca path_root_lca path_unique prefix_order.dual_order.antisym)
    then show "False" using longest_common_prefix_max_prefix prefix1 prefix2 
      by (metis (no_types, lifting) * Cons_prefix_Cons append.assoc append_same_eq assm length list.sel(3) p1_def path.cases prefix_length_le same_prefix_prefix)
  qed
  then show ?thesis
    using commmon_ancestor
    by blast
qed

subsection \<open>Correctness of \<open>find_newest_on_path\<close>.\<close>

abbreviation "Newest_on_path l a x y newest \<equiv>
\<exists> p . path l y p x \<and> newest = (MAX i \<in> set [1..<length p]. a ! (p ! i))"

lemma find_newest_on_path_dom': 
"find_newest_on_path_dom (l, a, x, y) \<Longrightarrow> x \<noteq> y \<Longrightarrow> find_newest_on_path_dom (l, a, l ! x, y)"
  apply(induction rule: find_newest_on_path.pinduct)
  using find_newest_on_path.domintros by blast

lemma find_newest_on_path_domain:
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "path l y p x"
  shows "find_newest_on_path_dom (l, a, x, y)"
  using assms proof(induction arbitrary: p rule: rep_of_induct)
  case (base i)
  then have "i = y" using path_root 
    by auto
  then show ?case using find_newest_on_path.domintros by auto
next
  case (step i)
  then show ?case
  proof(cases "i = y")
    case True
    then show ?thesis 
      using find_newest_on_path.domintros by blast
  next
    case False
    have path_y: "path l y (butlast p) (last (butlast p))" 
      by (metis False append_butlast_last_id list_e_eq_lel(2) path.cases path_divide1 path_properties step.prems(2))
    have "last (butlast p) = l ! i" using path_penultimate False step(6) 
      by (metis Misc.last_in_set path_y length_butlast length_pos_if_in_set path_not_empty zero_less_diff)
    then have "find_newest_on_path_dom (l, a, l ! i, y)"
      using path_y step by auto
    then show ?thesis 
      using find_newest_on_path.domintros by blast
  qed
qed

theorem find_newest_on_path_correct:
  assumes path: "path l y p x"
    and invar: "ufa_invar l"
    and xy: "x \<noteq> y"
  shows "Newest_on_path l a x y (find_newest_on_path l a x y)"
proof
  from assms path_no_root have no_root: "l ! x \<noteq> x" by simp
  from assms have x: "x < length l" and y: "y < length l" 
    by (auto simp add: path_nodes_lt_length_l)
  with invar path no_root have "find_newest_on_path_dom (l, a, x, y)"
    using find_newest_on_path_domain path_nodes_lt_length_l by auto
  then have "find_newest_on_path l a x y = (MAX i \<in> set [1..<length p]. a ! (p ! i))" 
    using x y assms proof(induction arbitrary: p rule: find_newest_on_path.pinduct)
    case (1 l a x y)
    with path_single have "butlast p \<noteq> []" 
      by (metis butlast.simps(2) list.distinct(1) path.cases)
    with path_divide1 y have path_y_l_x: "path l y (butlast p) (l ! x)" 
      using 1 path_concat2 single 
      by (metis (mono_tags, lifting) length_butlast length_greater_0_conv path_penultimate zero_less_diff)
    show ?case
    proof(cases "l ! (l ! x) \<noteq> l ! x \<and> l ! x \<noteq> y")
      case True
      with 1 True path_y_l_x have ih: "find_newest_on_path l a (l ! x) y = (MAX i \<in> set [1..<length (butlast p)]. a ! ((butlast p) ! i))" 
        using path_nodes_lt_length_l by blast
      have "length (butlast p) > 1" 
        by (metis True last_ConsL length_0_conv less_one linorder_neqE_nat list.sel(1) list_decomp_1 path_properties path_y_l_x)
      then have length_p: "length p > 2" 
        by fastforce
      then have "[1..<length p] = [1..<length p-1] @ [length p-1]" 
        by (metis Suc_1 Suc_lessD Suc_lessE diff_Suc_1 le_less_Suc_eq nat_le_linear upt_Suc_append)
      then have *: "(\<lambda> i . a ! (p ! i)) `(set [1..<length p])= {a ! (p ! (length p-1))} \<union> ((\<lambda> i . a ! (p ! i)) `set [1..<length p-1])" 
        by force
      from length_p have "1 \<in> set [1..<length (butlast p)]"
        by simp
      with * have **: "(MAX i \<in> set [1..<length p] . a ! (p ! i) ) = max (a ! (p ! (length p -1))) (MAX i\<in>set [1..<length p-1]. a ! (p ! i))"
        by auto
      have "p ! (length p - 1) = x" using path_last 1
        by (metis path_properties last_conv_nth)                              
      then have ***: "find_newest_on_path l a x y = max (a ! (p ! (length p - 1))) (MAX i \<in> set [1..<length (butlast p)]. a ! ((butlast p) ! i))"
        using 1 ih find_newest_on_path.psimps by presburger
      have "(\<lambda> i . a ! (p ! i)) ` (set [1..<length p-1]) = (\<lambda> i . a ! ((butlast p) ! i)) `(set [1..<length p-1])"
        by (simp add: nth_butlast)
      then show ?thesis 
        using ** *** by force
    next
      case False
      have "l ! (l ! x) = l ! x \<Longrightarrow> l ! x = y" 
        using path_y_l_x path_root by auto
      with False have parent: "l ! x = y" by blast
      then have "find_newest_on_path l a (l ! x) y = None"
        using find_newest_on_path.psimps find_newest_on_path.domintros by presburger
      with 1 have result: "find_newest_on_path l a x y = a ! x" 
        by (simp add: find_newest_on_path.psimps)
      have "path l (l ! x) [l ! x, x] x"  
        using 1 parent path.step single by auto
      then have path: "p = [l ! x, x]" 
        using 1 parent path_unique by auto
      with result path show ?thesis 
        by simp
    qed
  qed
  then show "path l y p x \<and> find_newest_on_path l a x y  = (MAX i\<in>set [1..<length p]. a ! (p ! i))"
    using path by simp
qed

subsection \<open>Invariant for the Union Find Data Structure\<close>

text \<open>This section introduces an invariant for the union find data structure and proves
several properties of the functions when invoked with valid parameters.\<close>

abbreviation "valid_unions u n \<equiv>
(\<forall> i < length u. fst (u ! i) < n \<and> snd (u ! i) < n)"

text \<open>The validity invariant of the data structure expresses that the data structure derived 
from subsequent union with \<open>ufe_union\<close>, starting from the initial empty data structure. 
It also says that the unions were made with valid variables, aka the numbers are less than 
the length of the union find list.\<close>

abbreviation "ufe_invar ufe \<equiv> 
valid_unions (unions ufe) (length (uf_list ufe)) \<and>
apply_unions (unions ufe) (initial_ufe (length (uf_list ufe))) = ufe"

paragraph \<open>Lemmata about the length of uf_list, au and unions, if the invariant holds.\<close>

lemma ufe_union_length_au:
  "ufe_union ufe1 x y = ufe2 \<Longrightarrow> length (au ufe1) = length (au ufe2)"
  by(induction ufe1 x y rule: ufe_union.induct,auto)

lemma ufe_union_length_uf_list:
  "ufe_union ufe1 x y = ufe2 \<Longrightarrow> length (uf_list ufe1) = length (uf_list ufe2)"
  by(induction ufe1 x y rule: ufe_union.induct,auto)

lemma ufe_union_length_unions_Suc:
  "ufe_union ufe1 x y = ufe2 \<Longrightarrow> rep_of (uf_list ufe1) x \<noteq> rep_of (uf_list ufe1) y \<Longrightarrow> length (unions ufe1) + 1 = length (unions ufe2)"
  by(induction ufe1 x y rule: ufe_union.induct,auto)

lemma apply_unions_length_au:
  "apply_unions u ufe1 = ufe2 \<Longrightarrow> length (au ufe1) = length (au ufe2)"
  apply(induction u ufe1 rule: apply_unions.induct)
   apply simp_all
  apply (metis ufe_union_length_au)
  done

lemma apply_unions_length_uf_list:
  "apply_unions u ufe1 = ufe2 \<Longrightarrow> length (uf_list ufe1) = length (uf_list ufe2)"
  apply(induction u ufe1 rule: apply_unions.induct)
   apply simp_all
  apply (metis ufe_union_length_uf_list)
  done

lemma length_au:
  "ufe_invar ufe \<Longrightarrow> length (au ufe) = length (uf_list ufe)"
  by (metis apply_unions_length_au length_replicate ufe_data_structure.select_convs(3))

lemma ufe_union_length_unions_le:
  assumes "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
  shows  "length u \<le> length (unions (ufe_union ufe x y))"
  apply(cases "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y")
   apply(simp_all add: assms)
  done

lemma apply_unions_length_unions:
  "ufe = apply_unions un ufe0 \<Longrightarrow> length (unions ufe) \<le> length (unions ufe0) + length un"
proof(induction "length un" arbitrary: un ufe)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain xy un' where un':"un = un' @ [xy]"
    by (metis length_Suc_rev_conv)
  let ?ufe = "apply_unions un' ufe0"
  have IH: "length (unions ?ufe) \<le> length (unions ufe0) + length un'"
    using Suc un' by auto
  have *:"apply_unions un ufe0 = apply_unions [xy] ?ufe" 
    by (simp add: un' apply_unions_cons)
  obtain x2 y2 where xy:"xy = (x2,y2)"
    using prod_decode_aux.cases by blast
  then show ?case 
  proof(cases "rep_of (uf_list ?ufe) x2 = rep_of (uf_list ?ufe) y2")
    case True
    then have "ufe_union ?ufe x2 y2 = ?ufe" 
      by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
    then show ?thesis 
      using Suc.prems IH un' xy apply_unions_cons by auto
  next
    case False
    obtain l1 u1 a1 where ufe: "?ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
      using ufe_data_structure.cases by blast
    with False have "rep_of l1 x2 \<noteq> rep_of l1 y2" by auto
    then have "unions (ufe_union ?ufe x2 y2) = u1 @ [(x2,y2)]"
      using ufe by auto 
    with un' xy * show ?thesis 
      by (metis IH Suc.prems add_Suc_right apply_unions.simps(1,2) length_append_singleton not_less_eq_eq ufe ufe_data_structure.select_convs(2))
  qed
qed

lemma length_uf_list_initial: "initial_ufe n = ufe \<Longrightarrow> length (uf_list ufe) = n"
  by auto

paragraph \<open>Lemmata about the preservation of the invariant\<close>

lemma union_ufe_invar:
  assumes "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "ufe_invar ufe"
    and "x < length l"
    and "y < length l"
  shows "ufe_invar (ufe_union ufe x y)"
proof(cases "rep_of l x = rep_of l y")
  case True
  with assms ufe_union1 show ?thesis 
    by simp
next
  case False
  with assms ufe_union2 have unions: "unions (ufe_union ufe x y) = unions ufe @ [(x,y)]"
    by (metis ufe_data_structure.cases ufe_data_structure.select_convs(1,2))
  then have **: "i < length (unions (ufe_union ufe x y)) \<Longrightarrow>
       fst (unions (ufe_union ufe x y) ! i) < length (uf_list (ufe_union ufe x y)) \<and>
       snd (unions (ufe_union ufe x y) ! i) < length (uf_list (ufe_union ufe x y))" for i
  proof(cases "i < length (unions ufe)")
    case True
    then show ?thesis 
      using assms(2) ufe_union_length_uf_list unions by force
  next
    case False
    assume assm: "i < length (unions (ufe_union ufe x y))"
    with assms(1) unions have "length u + 1  = length (unions (ufe_union ufe x y))"
      by auto
    then have "i = length u" 
      using False assm assms(1) by (simp add: discrete)
    then have "fst (unions (ufe_union ufe x y) ! i) = x" 
      and "snd (unions (ufe_union ufe x y) ! i) = y"
      using assms(1) unions by auto
    with assms show ?thesis 
      by (metis ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  qed
  then have "apply_unions (u @ [(x,y)]) (initial_ufe (length l)) = apply_unions [(x, y)] ufe" 
    using apply_unions_cons assms by fastforce
  then have "apply_unions (unions (ufe_union ufe x y)) 
(initial_ufe (length (uf_list (ufe_union ufe x y)))) = ufe_union ufe x y" 
    by (metis apply_unions.simps(1,2) assms(1) ufe_data_structure.select_convs(1,2) ufe_union_length_uf_list unions)
  with ** show ?thesis 
    by simp
qed

theorem apply_unions_ufe_invar:
  assumes "ufe_invar ufe"
    and "valid_unions u (length (uf_list ufe))"
  shows "ufe_invar (apply_unions u ufe)"
  using assms proof(induction "length u" arbitrary: u)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain xy un' where un': "u = un' @ [xy]"
    by (metis length_Suc_rev_conv)
  then obtain x2 y2 where xy: "xy = (x2, y2)"
    using old.prod.exhaust by blast
  have valid_unions: "valid_unions un' (length (uf_list ufe))" 
    by (metis Suc.prems(2) Suc_lessD Suc_mono un' length_append_singleton nth_append_first)
  let ?c = "apply_unions un' ufe"
  have c: "ufe_invar ?c" 
    using Suc un' valid_unions assms(1) by auto
  have "apply_unions u ufe = apply_unions [xy] ?c" 
    by (simp add: un' apply_unions_cons)
  then have *: "apply_unions u ufe = ufe_union ?c x2 y2" 
    by (simp add: \<open>xy = (x2, y2)\<close>)
  obtain l1 u1 a1 where ufe: "?c = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  have "x2 < length (uf_list ?c) \<and> y2 < length (uf_list ?c)"
    by (metis Suc.prems(2) un' xy apply_unions_length_uf_list fst_conv length_append_singleton lessI nth_append_length snd_conv)
  with * c union_ufe_invar ufe show ?case 
    by simp
qed

paragraph \<open>\<open>ufe_invar\<close> implies \<open>ufa_invar\<close>.\<close>

lemma ufe_invar_imp_ufa_invar_aux: 
  "ufa_invar (uf_list ufe) \<Longrightarrow> valid_unions u (length (uf_list ufe)) \<Longrightarrow> ufa_invar (uf_list (apply_unions u ufe))"
proof(induction u ufe rule: apply_unions.induct)
  case (1 p)
  then show ?case by auto
next
  case (2 x y u p)
  from 2(3) have x: "x < length (uf_list p)" and y: "y < length (uf_list p)" by force+
  with 2(2) ufa_union_invar ufe_union2_uf_list have *: "rep_of (uf_list p) x \<noteq> rep_of (uf_list p) y 
\<Longrightarrow> ufa_invar (uf_list (ufe_union p x y))"
    by presburger
  from x y 2(2) ufe_union1_uf_list have "rep_of (uf_list p) x = rep_of (uf_list p) y 
\<Longrightarrow> ufa_invar (uf_list (ufe_union p x y))"
    by presburger
  with * 2 ufe_union_length_uf_list have "ufa_invar (uf_list (apply_unions u (ufe_union p x y)))"
    by (metis Suc_less_eq2 length_Cons nth_Cons_Suc)
  then show ?case 
    by simp
qed

lemma ufe_invar_initial: "ufe_invar (initial_ufe n)"
  by simp

theorem ufe_invar_imp_ufa_invar: "ufe_invar ufe \<Longrightarrow> ufa_invar (uf_list ufe)"
  by (metis apply_unions_length_uf_list ufa_init_invar ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar_aux)

paragraph \<open>Induction rule on the union find algorithm.\<close>
lemma apply_unions_induct[consumes 1, case_names initial union]:
  assumes "ufe_invar ufe"
  assumes "P (initial_ufe (length (uf_list ufe)))"
  assumes "\<And>pufe x y. ufe_invar pufe \<Longrightarrow> x < length (uf_list pufe) \<Longrightarrow> y < length (uf_list pufe)
    \<Longrightarrow> P pufe \<Longrightarrow> P (ufe_union pufe x y)"
  shows "P ufe"
  using assms proof(induction "length (unions ufe)" arbitrary: ufe)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain x2 y2 un where u: "unions ufe =  un @ [(x2,y2)]" 
    by (metis length_0_conv neq_Nil_rev_conv replicate_0 replicate_Suc_conv_snoc surjective_pairing)
  with Suc(3) have un_valid: "valid_unions un (length (uf_list ufe))" 
    by (metis length_append_singleton nat_less_le neq_Nil_rev_conv nth_append_first upt_Suc upt_rec)
  obtain pufe where pufe: "pufe = apply_unions un (initial_ufe (length (uf_list ufe)))"
    by simp
  then have pufe2: "ufe_union pufe x2 y2 = ufe" 
    by (metis Suc.prems(1) apply_unions.simps(1,2) apply_unions_cons u)
  then show ?case
  proof(cases "rep_of (uf_list pufe) x2 = rep_of (uf_list pufe) y2")
    case True
    obtain l1 u1 a1 where ufe: "ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
      using ufe_data_structure.cases by blast
    obtain l2 u2 a2 where pufe3: "pufe = \<lparr>uf_list = l2, unions = u2, au = a2\<rparr>" 
      using ufe_data_structure.cases by blast
    with True have "rep_of l2 x2 = rep_of l2 y2" by auto
    with True pufe2 ufe pufe3 have "pufe = ufe_union pufe x2 y2"  
      by simp
    then have "pufe = ufe" 
      by (simp add: pufe2)
    then have ufe2: "u2 = u1" using ufe pufe2 pufe
      by (metis pufe3 ufe_data_structure.ext_inject)
    with pufe apply_unions_length_unions have "length (unions pufe) \<le> length un"
      by (metis ab_semigroup_add_class.add.commute gen_length_code(1) gen_length_def ufe_data_structure.select_convs(2))
    moreover from u ufe2 have "length (unions ufe) = length un + 1"
      by simp
    ultimately have "False" 
      using \<open>pufe = ufe\<close> by auto
    then show ?thesis by simp
  next
    case False
    with Suc(2) u ufe_union_length_uf_list have "x = length (unions pufe)" 
      by (metis Suc_eq_plus1 add_right_cancel pufe2 ufe_union_length_unions_Suc)
    have length_eq: "length (uf_list pufe) = length (uf_list ufe)" 
      using pufe2 ufe_union_length_uf_list by auto
    then have "ufe_invar pufe" 
      using apply_unions_ufe_invar length_uf_list_initial pufe ufe_invar_initial un_valid by presburger
    with Suc have "P pufe" 
      using \<open>x = length (unions pufe)\<close> length_eq by fastforce
    from Suc(3) u have "x2 < length (uf_list pufe)" "y2 < length (uf_list pufe)"
       apply (metis length_eq fst_conv length_Suc_rev_conv lessI nth_append_length)
      by (metis Suc(3) u length_eq snd_conv length_Suc_rev_conv lessI nth_append_length)
    with Suc show ?thesis 
      using \<open>P pufe\<close> \<open>ufe_invar pufe\<close> pufe2 by blast
  qed
qed

paragraph \<open>Properties of some functions when \<open>ufe_invar\<close> holds.\<close>

lemma no_redundant_unions:
  assumes invar: "ufe_invar a"
    and unions_a: "unions a = p @ [(x, y)] @ t"
    and l: "l = apply_unions p (initial_ufe (length (uf_list a)))"
  shows "rep_of (uf_list l) x \<noteq> rep_of (uf_list l) y"
proof
  assume same_rep: "rep_of (uf_list l) x = rep_of (uf_list l) y"
  obtain l1 u1 a1 where "l = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with same_rep have "ufe_union l x y = l"
    by auto
  then have 1: "apply_unions (p @ [(x,y)]) (initial_ufe (length (uf_list a))) = l" 
    by (metis l apply_unions.simps apply_unions_cons)
  then have "apply_unions (p @ [(x,y)] @ t) (initial_ufe (length (uf_list a))) = a" 
    using invar unions_a by auto
  then have "length (unions a) \<le> length (p  @ t)"
    by (metis 1 l add_cancel_left_left apply_unions_cons length_append apply_unions_length_unions list.size(3) ufe_data_structure.select_convs(2))
  then show "False"
    by (simp add: unions_a)
qed

text \<open>(au ! i = None) iff i is a root.\<close>

lemma au_none_iff_root_initial: 
  assumes initial: "\<lparr>uf_list = l, unions = u, au = a\<rparr> = initial_ufe (length l)" 
    and i: "i < length l"
  shows "a ! i = None \<longleftrightarrow> l ! i = i"
proof-
  from initial have "l = [0..<length l]"
    by blast
  with i have *: "l ! i = i" 
    by (metis add_cancel_left_left nth_upt)
  from initial have "length a = length l" 
    by force
  with i initial have "a ! i = None" 
    by simp
  with i * show ?thesis
    by simp
qed

lemma au_none_iff_root_union:
  assumes "a ! i = None \<longleftrightarrow> l ! i = i"
    and "i < length l"
    and "x < length l"
    and "y < length l"
    and "ufe_invar ufe"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
  shows "(au (ufe_union ufe x y)) ! i = None \<longleftrightarrow> (uf_list (ufe_union ufe x y)) ! i = i"
proof
  assume prem: "au (ufe_union ufe x y) ! i = None"
  with assms(6) have i: "rep_of l x \<noteq> rep_of l y \<Longrightarrow> a[rep_of l x := Some (length u)] ! i = None"
    by simp
  from assms rep_of_less_length_l ufe_invar_imp_ufa_invar have "rep_of l x < length l" 
    by (metis ufe_data_structure.select_convs(1))
  from length_au assms have "length a = length l" 
    by (metis ufe_data_structure.select_convs(1,3))
  then have "a[rep_of l x := Some (length u)] ! rep_of l x = Some (length u)"
    by (simp add: length_au assms \<open>rep_of l x < length l\<close>)
  with i have "rep_of l x \<noteq> rep_of l y \<Longrightarrow> rep_of l x \<noteq> i"
    by auto
  then show "uf_list (ufe_union ufe x y) ! i = i"
    using prem assms(1,6) i by auto
next 
  assume prem:"uf_list (ufe_union ufe x y) ! i = i"
  with assms ufe_union2_uf_list have "rep_of l x \<noteq> rep_of l y \<Longrightarrow> i \<noteq> rep_of l x" 
    by force
  with assms ufe_union1 show "au (ufe_union ufe x y) ! i = None" 
    by (metis nth_list_update_neq nth_list_update_neq prem ufe_data_structure.select_convs(1,3) ufe_union.simps)
qed

lemma au_none_iff_root:
  assumes "ufe_invar ufe"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
    and "i < length l"
  shows "a ! i = None \<longleftrightarrow> l ! i = i"
  using assms proof(induction arbitrary: l u a rule: apply_unions_induct)
  case initial 
  then show ?case by auto
next
  case (union pufe x y)
  obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with union have "a1 ! i = None \<longleftrightarrow> l1 ! i = i"
    by (metis (full_types) ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  have "length l = length l1" 
    by (metis pufe ufe_data_structure.select_convs(1) ufe_union_length_uf_list union.prems(1))
  with union pufe au_none_iff_root_union ufe_union_length_uf_list ufe_data_structure.select_convs(1-3)
  show ?case by metis
qed

lemma au_Some_if_not_root:
  assumes "ufe_invar ufe"
    and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>" 
    and "i < length l"
    and "l ! i \<noteq> i"
  obtains k where "a ! i = Some k"
proof-
  from assms au_none_iff_root have "a ! i \<noteq> None" 
    by blast
  then obtain k where "a ! i = Some k" 
    by auto
  then show ?thesis 
    by (simp add: that)
qed

paragraph \<open>Lemmata about invariants wrt. \<open>ufe_union\<close>.\<close>

lemma rep_of_ufa_union_invar:
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "x2 < length l"
    and "y2 < length l"
    and "rep_of l x = rep_of l y"
  shows "rep_of (ufa_union l x2 y2) x = rep_of (ufa_union l x2 y2) y"
  using assms ufa_union_aux by simp

lemma rep_of_ufe_union_invar:
  assumes "ufe_invar ufe"
    and "x < length (uf_list ufe)"
    and "y < length (uf_list ufe)"
    and "x2 < length (uf_list ufe)"
    and "y2 < length (uf_list ufe)"
    and "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y"
  shows "rep_of (uf_list (ufe_union ufe x2 y2)) x = rep_of (uf_list (ufe_union ufe x2 y2)) y"
proof-
  obtain l1 u1 a1 where ufe: "ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with assms(1) ufe_invar_imp_ufa_invar have "ufa_invar l1" 
    by (metis ufe_data_structure.select_convs(1))
  with assms rep_of_ufa_union_invar 
  have "rep_of (ufa_union l1 x2 y2) x = rep_of (ufa_union l1 x2 y2) y" 
    by (metis ufe ufe_data_structure.select_convs(1))
  then show ?thesis 
    using assms(6) ufe by auto
qed

lemma au_ufe_union_Some_invar:
  "ufe_invar ufe \<Longrightarrow> (au ufe) ! i = Some k 
    \<Longrightarrow> x < length (uf_list ufe) \<Longrightarrow> y < length (uf_list ufe)
    \<Longrightarrow> (au (ufe_union ufe x y)) ! i = Some k"
proof(cases "rep_of (uf_list ufe) x = rep_of (uf_list ufe) y")
  case True
  then have *: "au (ufe_union ufe x y) = au ufe" 
    by (metis (full_types) old.unit.exhaust ufe_data_structure.surjective ufe_union1)
  assume "(au ufe) ! i = Some k"
  with * show ?thesis 
    by simp
next
  case False
  assume "(au ufe) ! i = Some k" and invar: "ufe_invar ufe"
    and x: "x < length (uf_list ufe)" and y: "y < length (uf_list ufe)"
  obtain l1 u1 a1 where ufe:"ufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
    using ufe_data_structure.cases by blast
  with False have *:
"au (ufe_union \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> x y) = a1[rep_of l1 x := Some (length u1)]" 
    by auto
  then show ?thesis
  proof(cases "i = rep_of l1 x")
    case True
    from invar ufe_invar_imp_ufa_invar have "ufa_invar l1" 
      by (metis ufe ufe_data_structure.select_convs(1))
    with rep_of_root x have "l1 ! rep_of l1 x = rep_of l1 x" 
      by (metis ufe ufe_data_structure.select_convs(1))
    from True ufe have "i < length l1" 
      using \<open>ufa_invar l1\<close> rep_of_less_length_l x by auto
    with au_none_iff_root have "au ufe!i = None" 
      using True \<open>l1 ! rep_of l1 x = rep_of l1 x\<close> invar ufe by auto
    then have "False" 
      by (simp add: \<open>au ufe ! i = Some k\<close>)
    then show ?thesis by simp
  next
    case False
    with * have "au (ufe_union \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> x y) ! i = a1 ! i" 
      by simp
    then show ?thesis 
      using \<open>au ufe ! i = Some k\<close> ufe by fastforce
  qed
qed

lemma no_root_ufe_union_invar:
  assumes invar: "ufe_invar ufe"
    and ufe: "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and no_root: "l ! i \<noteq> i" and x: "x < length l" and y: "y < length l"
  shows "(uf_list (ufe_union ufe x y)) ! i = l ! i"
proof(cases "rep_of l x = rep_of l y")
  case True
  then have *: "uf_list (ufe_union ufe x y) = l" 
    using assms(2) by auto
  with * show ?thesis 
    by simp
next
  case False
  with False have *:
    "uf_list (ufe_union \<lparr>uf_list = l, unions = u, au = a\<rparr> x y) = l[rep_of l x := rep_of l y]" 
    by auto
  then show ?thesis
  proof(cases "i = rep_of l x")
    case True
    from invar ufe_invar_imp_ufa_invar have "ufa_invar l" 
      by (metis ufe ufe_data_structure.select_convs(1))
    with rep_of_root x have "l ! rep_of l x = rep_of l x" 
      by simp
    then show ?thesis 
      using True no_root ufe by fastforce
  next
    case False
    then show ?thesis 
      by (simp add: ufe)
  qed
qed

lemma path_to_root_ufa_union1:
  assumes "ufa_invar l" and  "x < length l"
    and "rep_of l x \<noteq> rep_of l x2"
    and "x2 < length l" and "y2 < length l"
  shows "path_to_root (ufa_union l x2 y2) x = path_to_root l x"
  using assms proof(induction rule: rep_of_induct)
  case (base i)
  then show ?case 
    by (metis length_list_update path_no_cycle path_to_root_correct rep_of_refl ufa_union_aux ufa_union_invar)
next
  case (step i)
  then have "rep_of l (l ! i) \<noteq> rep_of l x2" 
    using rep_of_idx by presburger
  with step have *: "path_to_root (ufa_union l x2 y2) (l ! i) = path_to_root l (l ! i)" by auto
  have "path_to_root_dom (l, i)" 
    using path_to_root_domain step.hyps(1) step.hyps(2) ufa_invarD(1) by auto
  with step * show ?case 
    by (metis length_list_update nth_list_update_neq path_to_root.psimps path_to_root_domain rep_of_idem ufa_invarD(1) ufa_union_invar)
qed

lemma path_to_root_ufa_union2:
  assumes "ufa_invar l" and  "x < length l"
    and "rep_of l x = rep_of l x2"
    and "x2 < length l" and "y2 < length l"
    and "rep_of l x2 \<noteq> rep_of l y2"
  shows "path_to_root (ufa_union l x2 y2) x = [rep_of l y2] @ path_to_root l x"
  using assms proof(induction rule: rep_of_induct)
  case (base i)
  then have base_path:"path_to_root l i = [i]"
    by (metis path_no_cycle path_to_root_correct rep_of_refl)
  from base have union: "ufa_union l x2 y2 ! i = rep_of l y2"
    by (simp add: rep_of_refl)
  with base have "path_to_root (ufa_union l x2 y2) i = path_to_root (ufa_union l x2 y2) ((ufa_union l x2 y2)!i)@[i]"
    by (metis length_list_update path_snoc path_to_root_correct path_unique rep_of_bound rep_of_idx rep_of_refl ufa_union_invar)
  with base base_path union show ?case 
    by (metis append_same_eq length_list_update path_no_cycle path_to_root_correct rep_of_idx rep_of_less_length_l ufa_union_aux ufa_union_invar)   
next
  case (step i)
  let ?new_l = "ufa_union l x2 y2"
  let ?path_root_i = "path_to_root ?new_l i"
  let ?path_root_l_i = "path_to_root ?new_l (?new_l ! i)"
  from step have *: "rep_of l (l ! i) = rep_of l x2" 
    by (metis rep_of_step)
  have 1: "path ?new_l (rep_of ?new_l i) ?path_root_i i"
    by (simp add: path_to_root_correct step ufa_union_invar)
  from step have 2: "path ?new_l (rep_of ?new_l i) (?path_root_l_i @ [i]) i"
    by (metis "1" path_nodes_lt_length_l path_snoc path_to_root_correct rep_of_idx ufa_invarD(2) ufa_union_invar ufa_union_root)
  from 1 2 path_unique step have "?path_root_i = ?path_root_l_i @ [i]" 
    using ufa_union_invar by blast
  with step show ?case 
    by (metis Cons_eq_appendI * empty_append_eq_id nth_list_update_neq path_snoc path_to_root_correct path_unique rep_of_min ufa_invarD(2))
qed

lemma lowest_common_ancestor_ufa_union_invar:
  assumes "ufa_invar l" and "rep_of l x = rep_of l y"
    and "x < length l" and "y < length l" 
    and "x2 < length l" and "y2 < length l"
  shows "lowest_common_ancestor (ufa_union l x2 y2) x y = lowest_common_ancestor l x y"
proof(cases "rep_of l x2 = rep_of l x")
  case True
  then show ?thesis 
  proof(cases "rep_of l x2 = rep_of l y2")
    case True
    then show ?thesis 
      by (metis assms(1,5) list_update_id rep_of_root)
  next
    case False
    then have "path_to_root (ufa_union l x2 y2) y = [rep_of l y2] @ path_to_root l y"
      using assms path_to_root_ufa_union2 True by auto
    moreover have "path_to_root (ufa_union l x2 y2) x = [rep_of l y2] @ path_to_root l x"
      using assms path_to_root_ufa_union2 True False by auto 
    ultimately 
    have *: "longest_common_prefix (path_to_root (ufa_union l x2 y2) x) (path_to_root (ufa_union l x2 y2) y)
            = [rep_of l y2] @ longest_common_prefix (path_to_root l x) (path_to_root l y)"
      by simp
    from path_to_root_correct have hd_x: "hd (path_to_root l x) = rep_of l x" 
      using assms(1) assms(3) path_hd by blast
    moreover from path_to_root_correct have hd_y: "hd (path_to_root l y) = rep_of l x" 
      using assms(1) assms(4) path_not_empty by (metis assms(2) path_hd)
    ultimately 
    have "hd (longest_common_prefix (path_to_root l x) (path_to_root l y)) = rep_of l x" 
      by (metis list.collapse list.distinct(1) longest_common_prefix.simps)
    with assms path_to_root_correct hd_x hd_y * show ?thesis 
      by (metis last_appendR list.sel(1) longest_common_prefix.simps(1) lowest_common_ancestor.simps neq_Nil_conv path_not_empty)
  qed
next
  case False
  then show ?thesis 
    using assms path_to_root_ufa_union1 by auto
qed

lemma lowest_common_ancestor_ufe_union_invar:
  assumes "ufe = \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and "ufe_invar ufe" and "rep_of l x = rep_of l y"
    and "x < length l" and "y < length l" 
    and "x2 < length l" and "y2 < length l"
  shows "lowest_common_ancestor (uf_list (ufe_union ufe x2 y2)) x y = lowest_common_ancestor l x y"
proof-
  from assms(1,2) have "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  then show ?thesis 
    using assms lowest_common_ancestor_ufa_union_invar by auto
qed

lemma find_newest_on_path_dom_ufe_union:
  assumes "path l y p x" 
    and "ufe_invar ufe" and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x < length l"
    and "y < length l"
    and "x2 < length l"
    and "y2 < length l"
  shows "path (uf_list (ufe_union ufe x2 y2)) y p x"
  using assms proof(induction arbitrary: ufe a u rule: path.induct)
  case (single n l3)
  then have "path (uf_list (ufe_union ufe x2 y2)) n [n] n" 
    by (metis path.single ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  with single show ?case by auto
next
  case (step r l3 u3 p3 v)
  then have p:"path (uf_list (ufe_union ufe x2 y2)) u3 p3 v"
    using path_nodes_lt_length_l by blast
  with step have *: "(uf_list (ufe_union ufe x2 y2)) ! u3 = l3 ! u3" 
    by (metis nth_list_update_neq rep_of_min ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar ufe_union1_uf_list ufe_union2_uf_list)
  with step have "r < length (uf_list (ufe_union ufe x2 y2))" 
    by (metis ufe_data_structure.select_convs(1) ufe_union_length_uf_list)
  with p path.step have "path (uf_list (ufe_union ufe x2 y2)) r (r # p3) v" 
    using * step.hyps(2) step.hyps(3) by auto
  with step show ?case by simp
qed

lemma find_newest_on_path_ufe_union_invar:
  assumes "path l y p x" 
    and "ufe_invar ufe" and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x < length l" and "y < length l" 
    and "x2 < length l" and "y2 < length l"
  shows "find_newest_on_path (uf_list (ufe_union ufe x2 y2)) (au (ufe_union ufe x2 y2)) x y = find_newest_on_path l a x y"
proof-
  from assms have *:"ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  then have "find_newest_on_path_dom(l, a, x, y)" 
    using assms find_newest_on_path_domain by auto
  then show ?thesis
    using assms * proof(induction arbitrary: ufe p rule: find_newest_on_path.pinduct)
    case (1 l3 a3 x3 y3)
    let ?l2 = "uf_list (ufe_union ufe x2 y2)"
      and ?a2 = "au (ufe_union ufe x2 y2)"
    from 1 find_newest_on_path_dom_ufe_union have path: "path ?l2 y3 p x3" 
      by (metis (no_types, lifting))
    with 1 find_newest_on_path_domain have dom:"find_newest_on_path_dom (?l2, ?a2, x3, y3)" 
      by (metis path_nodes_lt_length_l ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar union_ufe_invar)
    then show ?case 
    proof(cases "x3 = y3")
      case True
      with 1 dom show ?thesis 
        using find_newest_on_path.domintros find_newest_on_path.psimps by presburger
    next
      case False
      with 1(3) path_root have "l3 ! x3 \<noteq> x3" by blast
      with au_Some_if_not_root obtain k where "a3 ! x3 = Some k" 
        using "1.prems" by blast
      with 1 have *:"a3 ! x3 = (au (ufe_union ufe x2 y2)) ! x3" 
        by (metis au_ufe_union_Some_invar ufe_data_structure.select_convs(1) ufe_data_structure.select_convs(3))
      have "?l2 ! x3 = (uf_list (ufe_union ufe x2 y2)) ! x3" 
        by (simp add: "1.prems"(2))
      have "path l3 y3 (butlast p) (l3 ! x3)"
        using "1.prems"(1) False path_butlast by auto
      with 1 have **:"find_newest_on_path ?l2 ?a2 (l3 ! x3) y3 = find_newest_on_path l3 a3 (l3 ! x3) y3"
        using False path_nodes_lt_length_l by blast
      have "find_newest_on_path ?l2 ?a2 x3 y3 = max (?a2 ! x3) (find_newest_on_path ?l2 ?a2 (?l2 ! x3) y3)"
        by (simp add: False dom find_newest_on_path.psimps)
      with 1 False dom find_newest_on_path.psimps * show ?thesis 
        by (metis ** no_root_ufe_union_invar)
    qed
  qed
qed

lemma unions_ufe_union_invar:
  assumes "ufe_invar ufe" and "ufe = \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "i < length u" and "x2 < length l" and "y2 < length l"
  shows "u ! i = (unions (ufe_union ufe x2 y2)) ! i"
proof(cases "rep_of l x2 = rep_of l y2")
  case True
  then show ?thesis 
    using assms by auto
next
  case False
  with assms have "unions (ufe_union ufe x2 y2) = u @ [(x2,y2)]" 
    by fastforce
  with assms show ?thesis 
    by simp
qed

lemma path_ufe_union_invar: 
  assumes "path (uf_list ufe) a p b"
    and "ufe_invar ufe"
    and "x2 < length (uf_list ufe)" and "y2 < length (uf_list ufe)"
  shows "path (uf_list (ufe_union ufe x2 y2)) a p b"
  using assms proof(induction "(uf_list ufe)" a p b rule: path.induct)
  case (single n)
  then show ?case 
    using path.single ufe_union_length_uf_list by presburger
next
  case (step r u p v)
  then have "uf_list (ufe_union ufe x2 y2) ! u = r" 
    by (metis nth_list_update_neq rep_of_root ufe_invar_imp_ufa_invar ufe_union_uf_list)
  with step show ?case 
    using path.step ufe_union_length_uf_list by presburger
qed

paragraph \<open>Lemmata about validity of au and find_newest_on_path\<close>

lemma au_Some_valid:
  assumes "ufe_invar ufe"
    and "i < length (au ufe)"
    and "au ufe ! i = Some x"
  shows "x < length (unions ufe)"
proof-
  from assms(1) have "apply_unions (unions ufe) (initial_ufe (length (uf_list ufe))) = ufe"
    by simp
  with assms show ?thesis
  proof(induction arbitrary: x rule: apply_unions_induct)
    case initial
    then show ?case by auto
  next
    case (union pufe x2 y)
    then show ?case 
    proof(cases "au pufe ! i")
      case None
      then show ?thesis 
      proof(cases "rep_of (uf_list pufe) x2 = rep_of (uf_list pufe) y")
        case True
        have "au (ufe_union pufe x2 y) = au pufe"
          by (metis (full_types) True old.unit.exhaust ufe_data_structure.surjective ufe_union1)
        with None have "au (ufe_union pufe x2 y)! i = None"
          by simp
        with union have "False" by auto
        then show ?thesis by simp
      next
        case False
        obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
          using ufe_data_structure.cases by blast
        with False have rep_of_neq: "rep_of l1 x2 \<noteq> rep_of l1 y"
          by simp
        with pufe have au:
          "au (ufe_union pufe x2 y) = a1[rep_of l1 x2 := Some (length u1)]"
          by simp
        with None pufe have i: "i = rep_of l1 x2" 
          by (metis not_None_eq nth_list_update_neq ufe_data_structure.select_convs(3) union.prems(2))
        from pufe have "unions (ufe_union pufe x2 y) = u1 @ [(x2,y)]" 
          by (simp add: rep_of_neq)
        with union show ?thesis 
          by (simp add: i nth_list_update' pufe rep_of_neq)
      qed
    next
      case (Some a)
      with union have *: "a < length (unions pufe)"
        by (metis Some ufe_union_length_au)
      with ufe_union_length_unions_le * have length_a: "a < length (unions (ufe_union pufe x2 y))"
        apply(cases "rep_of (uf_list pufe) x2 = rep_of (uf_list pufe) y")
        using ufe_union2_unions ufe_union1_unions by auto
      from au_ufe_union_Some_invar have "a = x" 
        using Some union by auto
      then show ?thesis 
        using length_a by blast
    qed
  qed
qed

lemma au_valid:
  assumes "ufe_invar ufe"
    and "i < length (au ufe)"
  shows "au ufe ! i < Some (length (unions ufe))"
  apply(cases "au ufe ! i")
  using assms au_Some_valid by auto

lemma find_newest_on_path_Some:
  assumes path: "path l y p x"
    and invar: "ufe_invar \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and xy: "x \<noteq> y"
  obtains k where "find_newest_on_path l a x y = Some k \<and> k < length un"
proof-
  assume a: "\<And>k. find_newest_on_path l a x y = Some k \<and> k < length un \<Longrightarrow> thesis"
  from invar have 1: "ufa_invar l" 
    by (metis ufe_data_structure.select_convs(1) ufe_invar_imp_ufa_invar)
  from path have 2: "x < length l" 
    by (simp add: path_nodes_lt_length_l)
  from path xy path_no_root have no_root: "l ! x \<noteq> x" 
    by auto
  show ?thesis
    using 1 2 assms no_root a proof(induction arbitrary: p thesis rule: rep_of_induct)
    case (base i)
    then show ?case by auto
  next
    case (step v)
    then have "v < length l" 
      using path_nodes_lt_length_l by presburger
    with au_none_iff_root have *: "a ! v \<noteq> None"
      using step by auto
    with * step apply_unions_length_au au_Some_valid have valid_au: "the (a ! v) < length un"
      by (metis \<open>v < length l\<close> option.exhaust_sel ufe_data_structure.select_convs(1-3) length_replicate)    
    then show ?case
    proof(cases "y = l ! v")
      case True
      from step have dom:"find_newest_on_path_dom (l, a, (l ! v), y)" 
        using True find_newest_on_path.domintros 
        by presburger
      then have "find_newest_on_path l a (l ! v) y = None" 
        using step True find_newest_on_path.psimps 
        by metis
      then have result: "find_newest_on_path l a v y = a ! v"
        using True dom find_newest_on_path.domintros find_newest_on_path.psimps step.prems(3) 
        by fastforce
      from step * show ?thesis 
        using True valid_au result 
        by fastforce
    next
      case False
      from step have path_y_l_v: "path l y (butlast p) (l ! v) " 
        using path_butlast by blast
      with step path_no_root False have "l ! (l ! v) \<noteq> l ! v" 
        by presburger
      with path_y_l_v step False obtain k where 
        IH: "find_newest_on_path l a (l ! v) y = Some k \<and> k < length un" 
        by blast
      from step have dom: "find_newest_on_path_dom (l, a, (l ! v), y)"
        using  find_newest_on_path.domintros 
        by (metis find_newest_on_path_domain find_newest_on_path_dom' path_nodes_lt_length_l)
      from \<open>v \<noteq> y\<close> max_def have "find_newest_on_path l a v y = find_newest_on_path l a (l ! v) y \<or> 
                               find_newest_on_path l a v y = a ! v" 
        by (metis dom find_newest_on_path.domintros find_newest_on_path.psimps)
      then show ?thesis 
        using "*" IH valid_au step.prems(5) by force
    qed
  qed
qed

paragraph \<open>Additional properties of \<open>find_newest_on_path\<close>.\<close>

lemma find_newest_on_path_if_Some:
  assumes "find_newest_on_path_dom (l, a, x, y)"
    and "find_newest_on_path l a x y = Some i"
    and "x < length l"
    and  "ufa_invar l"
  shows "l ! x \<noteq> x \<and> x \<noteq> y"
  using assms proof(induction arbitrary: i rule: find_newest_on_path.pinduct)
  case (1 l a x y)
  then show ?case 
  proof(cases "x = y")
    case True
    have "False" 
      using 1 True find_newest_on_path.psimps by auto
    then show ?thesis by simp
  next
    case False
    have "l ! x < length l" 
      by (simp add: 1 ufa_invarD(2))
    have "max (a ! x) (find_newest_on_path l a (l!x) y) = Some i" 
      using 1 False find_newest_on_path.psimps by force
    then have "find_newest_on_path l a (l ! x) y = Some i \<or> a ! x = Some i" 
      by (metis max_def)
    then show ?thesis 
    proof
      show ?thesis 
        using 1 False path_root by force
    next
      assume ax: "a ! x = Some i"
      then show ?thesis 
        using 1 False \<open>l ! x < length l\<close> by auto
    qed
  qed
qed

lemma find_newest_on_path_if_None:
  assumes path: "path l y p x"
    and invar: "ufe_invar \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and None: "find_newest_on_path l a x y = None"
  shows "x = y"
proof-
  have "\<nexists> k. find_newest_on_path l a x y = Some k \<and> k < length un"
    by (simp add: None)
  with find_newest_on_path_Some show ?thesis 
    by (metis invar path)
qed

lemma find_newest_on_path_valid:
  assumes path: "path l y p x"
    and invar: "ufe_invar \<lparr>uf_list = l, unions = un, au = a\<rparr>"
  shows "find_newest_on_path l a x y < Some (length un)"
proof(cases "x = y")
  case True
  then have "find_newest_on_path_dom (l, a, x, y)" 
    using find_newest_on_path.domintros by blast
  with find_newest_on_path_if_Some have "find_newest_on_path l a x y = None" 
    using True find_newest_on_path.psimps by auto
  then show ?thesis by simp
next
  case False
  with assms find_newest_on_path_Some obtain k where "find_newest_on_path l a x y = Some k" and "k < length un"
    by metis
  then show ?thesis by simp
qed

lemma find_newest_x_neq_None_or_find_newest_y_neq_None:
  assumes "x \<noteq> y"
    and "ufe_invar  \<lparr>uf_list = l, unions = un, au = a\<rparr>"
    and "x < length l"
    and "y < length l"
    and "rep_of l x = rep_of l y"
  shows "find_newest_on_path l a y (lowest_common_ancestor l x y) \<noteq> None
          \<or> find_newest_on_path l a x (lowest_common_ancestor l x y) \<noteq> None"
proof(rule ccontr)
  from ufe_invar_imp_ufa_invar have "ufa_invar l" 
    by (metis assms(2) ufe_data_structure.select_convs(1))
  with lowest_common_ancestor_correct assms ufe_invar_imp_ufa_invar obtain pLcaX pLcaY 
    where pLcaX: "path l (lowest_common_ancestor l x y) pLcaX x" and pLcaY:"path l (lowest_common_ancestor l x y) pLcaY y"
    by presburger
  then have dom_y: "find_newest_on_path_dom(l, a, y, (lowest_common_ancestor l x y))"
    and dom_x: "find_newest_on_path_dom(l, a, x, (lowest_common_ancestor l x y))"
    using \<open>ufa_invar l\<close> find_newest_on_path_domain path_nodes_lt_length_l by auto
  assume assm:"\<not> (find_newest_on_path l a y (lowest_common_ancestor l x y) \<noteq> None \<or>
                find_newest_on_path l a x (lowest_common_ancestor l x y) \<noteq> None)"
  then have "find_newest_on_path l a x (lowest_common_ancestor l x y) = None" by simp
  with dom_x assms pLcaX
    find_newest_on_path_if_None have x: "x = lowest_common_ancestor l x y" 
    by blast
  with dom_y assms pLcaY
    find_newest_on_path_if_None have "y = lowest_common_ancestor l x y" 
    using assm by blast
  then show "False" 
    using x assms(1) by linarith
qed

end