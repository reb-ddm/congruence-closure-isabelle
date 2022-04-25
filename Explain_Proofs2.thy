section \<open>Correctness proofs for Explain\<close>
theory Explain_Proofs2
  imports Explain_Proofs
begin 


paragraph \<open>Invariant: the edges near the root are newer.\<close>

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
  have i:"i < length (uf_list pufe)" 
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


paragraph \<open>The order of the parameters in explain can be switched.\<close>


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
      using lowest_common_ancestor.domintros by presburger
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
      using lowest_common_ancestor.domintros by presburger
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

lemma explain_symmetric:
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
      using lowest_common_ancestor.domintros by presburger
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
      using lowest_common_ancestor.domintros by presburger
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
print_statement explain.pinduct

lemma explain_cases_simple[consumes 3, case_names symmetric base case_x]:
  assumes "ufe_invar \<lparr>uf_list = l, unions = u, au = a\<rparr>"
    and "x < length l" and "y < length l"
    and "\<And> x y . P y x \<Longrightarrow> P x y"
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
  shows "P x y"
proof-
  define lca' newest_index_x' newest_index_y' axbx' ayby' 
    where defs1: "lca' = lowest_common_ancestor l y x"
      "newest_index_x' = find_newest_on_path l a y lca'"
      "newest_index_y' = find_newest_on_path l a x lca'"
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
    with assms defs  show ?thesis 
      by (metis explain_symmetric_domain ufe_data_structure.select_convs(1))
  next
    case b
    with assms defs  show ?thesis 
      by (metis explain_index_neq)
  next
    case c
    with assms defs  show ?thesis 
      by (metis lowest_common_ancestor.domintros lowest_common_ancestor_symmetric ufe_data_structure.select_convs(1))
  qed
qed
end