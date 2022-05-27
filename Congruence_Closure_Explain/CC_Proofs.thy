theory CC_Proofs
  imports Congruence_Closure
begin

subsection \<open>Termination and correctness of \<open>add_edge\<close>\<close>

text \<open>In order to show that the termination invariant holds after adding an edge or a label to the proof forest,
we need to show a few invariants after function update\<close>

lemma rep_of_fun_upd: 
  assumes "ufa_invar l" "path l (rep_of l li) p\<^sub>1 li" "i \<notin> set p\<^sub>1" 
  shows "rep_of l li = rep_of (l[i := y]) li"
proof-
  have li: "li < length l" 
    using assms(2) path_nodes_lt_length_l by auto
  show ?thesis
    using assms(1) li assms(2-) proof(induction arbitrary: p\<^sub>1 rule: rep_of_induct)
    case (base li)
    then show ?case 
      by (metis list.set_intros(1) nth_list_update_neq path_no_cycle rep_of_refl)
  next
    case (step li)
    then have path_to_parent: "path l (rep_of l (l ! li)) (butlast p\<^sub>1) (l ! li)" 
      by (metis path_butlast rep_of_idx rep_of_root)
    then have rep_of_parent: "rep_of l (l ! li) = rep_of (l[i := y]) (l ! li)" 
      by (metis in_set_butlastD step.IH step.prems(2))
    from step have "li \<noteq> i" 
      by (metis path_to_parent in_set_conv_decomp path_snoc path_unique rep_of_step ufa_invarD(2))
    with step(1,2) path_to_root_correct have "path l (rep_of l li) (path_to_root l li) li" 
      by simp
    then have "path (l[i := y]) (rep_of l li) (path_to_root l li) li" 
      using path_fun_upd path_unique step by (metis in_set_tlD)
    with step have "path (l[i := y]) (rep_of l li) (butlast (path_to_root l li)) (l ! li)" 
      by (metis \<open>li \<noteq> i\<close> nth_list_update_neq path_butlast rep_of_root)
    have "l[i := y] ! (rep_of l li) = (rep_of l li)" 
      by (metis list.set_intros(1) nth_list_update_neq path.simps rep_of_root step.hyps(1) step.hyps(2) step.prems(1) step.prems(2))
    with path_root_rep_of_dom have "rep_of_dom (l[i := y],l ! li)" 
      using \<open>path (l[i := y]) (rep_of l li) (butlast (path_to_root l li)) (l ! li)\<close> by blast
    then have "rep_of_dom (l[i := y], li)" 
      by (metis \<open>li \<noteq> i\<close> nth_list_update_neq rep_of.domintros)
    then have "rep_of l li = rep_of l (l ! li)" "rep_of (l[i := y]) li = rep_of (l[i := y]) (l ! li)" 
       apply (simp add: rep_of_idx step.hyps(1) step.hyps(2)) 
      by (metis \<open>li \<noteq> i\<close> \<open>rep_of_dom (l[i := y], li)\<close> nth_list_update_neq rep_of_idx2)
    with rep_of_parent show ?case 
      by presburger
  qed
qed

lemma rep_of_fun_upd': 
  assumes "ufa_invar l" "rep_of l li \<noteq> rep_of l i" "li < length l"
  shows "rep_of l li = rep_of (l[i := y]) li"
proof-
  from path_to_root_correct assms 
  have "path l (rep_of l li) (path_to_root l li) li" 
    "i \<notin> set (path_to_root l li)" apply simp 
    by (metis assms in_set_conv_nth nodes_path_rep_of(2) path_to_root_correct)
  with rep_of_fun_upd assms(1) show ?thesis 
    by blast
qed

lemma ufa_invar_fun_upd: 
  assumes "ufa_invar l" "path l (rep_of l y) py y" "i \<notin> set py"
  shows "ufa_invar (CONST list_update l i y)"
  unfolding ufa_invar_def
proof(standard, standard, standard)
  fix ia
  assume ia_valid: "ia < length (l[i := y])"
  have y: "y < length l" 
    using assms(2) path_nodes_lt_length_l by auto
  with assms ia_valid show "l[i := y] ! ia < length (l[i := y])"
    by (metis length_list_update nth_list_update' ufa_invarD(2))
  have path_root: "path l (rep_of l ia) (path_to_root l ia) ia" 
    using ia_valid assms(1) path_to_root_correct by auto
  show "rep_of_dom (l[i := y], ia)"
  proof(cases "i \<in> set (path_to_root l ia)")
    case False
      \<comment> \<open>The path to the root of ia still exists after the function update.\<close>
    with path_fun_upd path_root have "path (l[i := y]) (rep_of l ia) (path_to_root l ia) ia" 
      by (metis in_set_tlD)
    with path_root have "path (l[i := y]) (rep_of (l[i := y]) ia) (path_to_root l ia) ia" 
      using False assms(1) rep_of_fun_upd by auto
    from rep_of_root have "(l[i := y]) ! (rep_of (l[i := y]) ia) = (rep_of (l[i := y]) ia)" 
      by (metis False \<open>path (l[i := y]) (rep_of (l[i := y]) ia) (path_to_root l ia) ia\<close> assms(1) ia_valid length_list_update list.inject list.set_intros(1) local.path_root nth_list_update_neq path.simps)
    with path_root_rep_of_dom show ?thesis 
      using \<open>path (l[i := y]) (rep_of (l[i := y]) ia) (path_to_root l ia) ia\<close> by blast
  next
    case True
      \<comment> \<open>After the function update, there is a path from ia to i, and an edge from i to y.
           The assumption that there is a path from y to rep_of y is important in order to avoid
           cycles in the tree structure. Those three paths can be merged together,
           and then the lemma \<open>path_root_rep_of_dom\<close> applies.\<close>
    then obtain root_i i_ia where root_i: "path_to_root l ia = root_i @ [i] @ i_ia" 
      by (metis Cons_eq_append_conv append_Nil in_set_conv_decomp_first)
    with path_root path_divide2 have paths: "path l i (i#i_ia) ia" "path l (rep_of l ia) (root_i @ [i]) i" 
       apply (metis Cons_eq_appendI append_self_conv2 list.distinct(1) list.sel(1))
      by (metis Nil_is_append_conv hd_append list.distinct(1) list.sel(1) local.path_root path_divide2 root_i)
    with paths path_divide2[of l i "[i]" i_ia ia] have "i_ia \<noteq> [] \<Longrightarrow> path l (hd i_ia) i_ia ia" 
      by fastforce
    with path_remove_left have "i \<notin> set i_ia" 
      using assms(1) paths(1) by blast
    with path_fun_upd have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) (hd i_ia) i_ia ia"
      by (metis \<open>i_ia \<noteq> [] \<Longrightarrow> path l (hd i_ia) i_ia ia\<close> in_set_tlD)
    have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) i [i, hd i_ia] (hd i_ia)" 
      using path_nodes_lt_length_l paths(1) single 
      by (smt (verit, best) \<open>i \<notin> set i_ia\<close> append_Cons_eq_iff length_list_update nth_list_update_neq path.simps path_hd)
    with path_concat1 have p_l_upd_i_ia: "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) i (i # i_ia) ia" 
      by (metis \<open>i \<notin> set i_ia\<close> list.sel(3) path_fun_upd paths(1))
    from assms path_fun_upd in_set_tlD have path_rep_y: "path (l[i := y]) (rep_of l y) py y" 
      by metis
    from assms y have "path (l[i := y]) y [y, i] i" 
      by (metis \<open>path (l[i := y]) (rep_of l y) py y\<close> hd_in_set length_list_update nth_list_update_eq path.simps path_hd path_no_root paths(1))
    with p_l_upd_i_ia path_concat1 have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) y ([y, i] @ i_ia) ia" 
      by fastforce
    with path_concat1 path_rep_y have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) (rep_of l y) (py @ [i] @ i_ia) ia" 
      by fastforce
    with y assms path_root_rep_of_dom have "i_ia \<noteq> [] \<Longrightarrow> rep_of_dom (l[i := y], ia)" 
      by (metis hd_in_set list.distinct(1) nth_list_update_neq path.simps path_hd rep_of_root)
    with path_concat1 path_rep_y have "i_ia = [] \<Longrightarrow> path (l[i := y]) (rep_of l y) (py @ [i]) i" 
      using \<open>path (l[i := y]) y [y, i] i\<close> 
      by fastforce
    with y assms show ?thesis 
      by (metis \<open>i_ia \<noteq> [] \<Longrightarrow> rep_of_dom (l[i := y], ia)\<close>  list.set_intros(1) nth_list_update_neq path.simps path_length_1 path_root_rep_of_dom paths(1) rep_of_min)
  qed
qed

lemma ufa_invar_fun_upd': 
  assumes "ufa_invar l" "y < length l" "rep_of l i \<noteq> rep_of l y"
  shows "ufa_invar (CONST list_update l i y)"
proof(rule ufa_invar_fun_upd)
  show "path l (rep_of l y) (path_to_root l y) y" 
    by (simp add: assms(1) assms(2) path_to_root_correct)
  with assms show "i \<notin> set (path_to_root l y)"
    by (metis in_set_conv_nth path_rep_of_neq_not_in_path)
qed (auto simp add: assms)

lemma rep_of_fun_upd_rep_of:
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "i < length l"
    and "rep_of l x \<noteq> rep_of l y"
  shows "rep_of (l[rep_of l x := y]) x = rep_of l y"
proof-
  have path_to_rep_x: "path l (rep_of l x) (path_to_root l x) x" 
    by (simp add: assms(1) assms(2) path_to_root_correct)
  with path_fun_upd have path1: "path (l[rep_of l x := y]) (rep_of l x) (path_to_root l x) x"
    by (metis assms(1) list.sel(3) path.simps path_remove_left)
  from assms have path2: "path (l[rep_of l x := y]) y [y, rep_of l x] (rep_of l x)"
    by (metis path_to_rep_x length_list_update nth_list_update_eq path.step path_rep_eq rep_of_less_length_l single)
  have path_to_rep_y: "path l (rep_of l y) (path_to_root l y) y" 
    by (simp add: assms(1) assms(3) path_to_root_correct)
  have "rep_of l (rep_of l x) = rep_of l x" 
    using assms(1) path_rep_eq path_to_rep_x by blast
  with assms have "rep_of l x \<notin> set (path_to_root l y)" 
    by (metis path_to_rep_y in_set_conv_nth path_rep_of_neq_not_in_path)
  then have path3: "path (l[rep_of l x := y]) (rep_of l y) (path_to_root l y) y" 
    by (metis in_set_tlD path_fun_upd path_to_rep_y)
  from path1 path2 path3 assms path_rep_eq show ?thesis 
    by (metis \<open>rep_of l (rep_of l x) = rep_of l x\<close> rep_of_fun_upd' ufa_invar_fun_upd')
qed

lemma add_edge_domain: 
  assumes "ufa_invar l" "y < length l" "y' < length l" "rep_of l y \<noteq> rep_of l y'"
  shows "add_edge_dom (l, y, y')"
proof-
  have path: "path l (rep_of l y) (path_to_root l y) y"
    by (simp add: assms(1) assms(2) path_to_root_correct)
  show ?thesis
    using path assms proof(induction "length (path_to_root l y)" arbitrary: l y' y)
    case 0
    with path_not_empty show ?case by auto
  next
    case IH: (Suc a)
    then show ?case 
    proof(cases a)
      case 0
      then have "path_to_root l y = [y]" 
        using IH path_unique_if_length_eq single by fastforce
      with IH have "l ! y = y" 
        by (metis path_length_1 rep_of_root)
      then show ?thesis 
        using add_edge.domintros by blast
    next
      case (Suc n)
      then have "length (path_to_root l y) > 1" 
        using IH.hyps(2) by linarith
      then have path_root_divided: "path_to_root l y = rep_of l y # (tl(butlast(path_to_root l y))) @ [y]" 
        using IH.prems(1) path_hd_and_last by blast
      with IH have "l ! y \<noteq> y" 
        by (metis append_is_Nil_conv list_tail_coinc not_Cons_self2 path_no_cycle path_root)

      with IH have "path l (rep_of l y) (rep_of l y # (tl(butlast(path_to_root l y)))) (l ! y)"
        by (metis butlast_eq_cons_conv path_butlast path_root_divided rep_of_min)
      have "y \<notin> set (rep_of l y # (tl(butlast(path_to_root l y))))" 
        by (metis IH.prems(1) IH.prems(2) butlast_eq_cons_conv path_remove_right path_root_divided)
      then have "path (l[y := y']) (rep_of l y) (rep_of l y # (tl(butlast(path_to_root l y)))) (l ! y)"
        by (simp add: \<open>path l (rep_of l y) (rep_of l y # tl (butlast (path_to_root l y))) (l ! y)\<close> path_fun_upd)
      have "rep_of l y = rep_of (l[y := y']) (l ! y)" 
        by (metis IH.prems(2) IH.prems(3) \<open>path l (rep_of l y) (rep_of l y # tl (butlast (path_to_root l y))) (l ! y)\<close> \<open>y \<notin> set (rep_of l y # tl (butlast (path_to_root l y)))\<close> rep_of_fun_upd rep_of_step)

      have "path l (rep_of l y') (path_to_root l y') y'" 
        by (simp add: IH.prems(2) IH.prems(4) path_to_root_correct)
      have "y \<notin> set (path_to_root l y')" 
        by (metis IH.prems(2) IH.prems(5) \<open>path l (rep_of l y') (path_to_root l y') y'\<close> in_set_conv_nth nodes_path_rep_of(2))
      from ufa_invar_fun_upd[of l y' _ y] have "ufa_invar (l[y := y'])" 
        using IH.prems(2) IH.prems(4) \<open>path l (rep_of l y') (path_to_root l y') y'\<close> \<open>y \<notin> set (path_to_root l y')\<close> by blast
      then have "path (l[y := y']) (rep_of (l[y := y']) (l ! y)) (path_to_root (l[y := y']) (l ! y)) (l ! y)" 
        using \<open>path (l[y := y']) (rep_of l y) (rep_of l y # tl (butlast (path_to_root l y))) (l ! y)\<close> path_nodes_lt_length_l path_to_root_correct by blast
      have "l ! y < length (l[y := y'])" 
        using \<open>path (l[y := y']) (rep_of (l[y := y']) (l ! y)) (path_to_root (l[y := y']) (l ! y)) (l ! y)\<close> path_nodes_lt_length_l by blast

      have "a = length (path_to_root (l[y := y']) (l ! y)) "
        by (metis IH.hyps(2) \<open>path (l[y := y']) (rep_of (l[y := y']) (l ! y)) (path_to_root (l[y := y']) (l ! y)) (l ! y)\<close> \<open>path (l[y := y']) (rep_of l y) (rep_of l y # tl (butlast (path_to_root l y))) (l ! y)\<close> \<open>rep_of l y = rep_of (l[y := y']) (l ! y)\<close> \<open>ufa_invar (l[y := y'])\<close> length_Cons length_append_singleton old.nat.inject path_root_divided path_unique)

      with IH(1)[of "(l[y := y'])" "l ! y" y] have "add_edge_dom (l[y := y'], l ! y, y)"
        by (metis IH.prems(2) IH.prems(3) IH.prems(5) \<open>l ! y < length (l[y := y'])\<close> \<open>path (l[y := y']) (rep_of (l[y := y']) (l ! y)) (path_to_root (l[y := y']) (l ! y)) (l ! y)\<close> \<open>path l (rep_of l y') (path_to_root l y') y'\<close> \<open>rep_of l y = rep_of (l[y := y']) (l ! y)\<close> \<open>ufa_invar (l[y := y'])\<close> \<open>y \<notin> set (path_to_root l y')\<close> length_list_update nth_list_update_eq rep_of_fun_upd rep_of_idx)
      then show ?thesis 
        using add_edge.domintros by blast
    qed
  qed
qed

lemma add_edge_ufa_invar_invar: 
  assumes "ufa_invar l" 
    "e' < length l" "e < length l" 
    "rep_of l e \<noteq> rep_of l e'"
  shows "ufa_invar (add_edge l e e')"
proof-
  have dom: "add_edge_dom (l, e, e')" 
    by (simp add: add_edge_domain assms)
  from dom assms show ?thesis
    using assms proof(induction l e e' rule: add_edge.pinduct)
    case (1 pf e e')
    from 1 have path_root: "path pf (rep_of pf e') (path_to_root pf e') e'" 
      by (simp add: path_to_root_correct)
    with path_rep_of_neq_disjoint 1 have e_notin_path_root: "e \<notin> set (path_to_root pf e')" 
      by (metis in_set_conv_nth nodes_path_rep_of(2))
    with ufa_invar_fun_upd have ufa_invar_upd: "ufa_invar (pf[e := e'])" 
      using 1 path_root by blast
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      from ufa_invar_upd show ?thesis 
        by (simp add: "1.hyps" True add_edge.psimps)
    next
      case False
      have lengths: "e < length (pf[e := e'])" "pf ! e < length (pf[e := e'])" 
        by (auto simp add: "1.prems" ufa_invarD(2))
      have "rep_of (pf[e := e']) e = rep_of (pf[e := e']) e'" 
        by (metis "1.prems"(3) lengths(1) nth_list_update_eq rep_of_idx ufa_invar_upd)
      also have "... = rep_of pf e'" 
        using "1.prems"(1) e_notin_path_root path_root rep_of_fun_upd by auto
      have path_e_root: "path pf (rep_of pf e) (path_to_root pf e) e" 
        by (simp add: "1.prems" path_to_root_correct)
      with "1.prems" have path_pf_e: "path pf (rep_of pf e) (butlast (path_to_root pf e)) (pf ! e)" 
        by (metis False path_butlast rep_of_root)
      then have "last (path_to_root pf e) = e" 
        using path_e_root path_last by auto
      with path_remove_right have "e \<notin> set (butlast (path_to_root pf e))" 
        using "1.prems"(1) path_e_root by auto
      with rep_of_fun_upd 1 have "rep_of (pf[e := e']) (pf ! e) = rep_of pf e" 
        by (metis path_pf_e rep_of_step)
      then have "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        by (simp add: "1.prems"(4) \<open>rep_of (pf[e := e']) e' = rep_of pf e'\<close> calculation)
      then have "ufa_invar (add_edge (pf[e := e']) (pf ! e) e)" 
        by (metis "1.IH" lengths ufa_invar_upd)
      then show ?thesis 
        by (simp add: "1.hyps" False add_edge.psimps)
    qed
  qed
qed

lemma add_edge_list_unchanged: 
  assumes "ufa_invar l"
    "path l (rep_of l li) p\<^sub>1 li" "x < length l"
    "i \<notin> set p\<^sub>1" "rep_of l li \<noteq> rep_of l x"
  shows "l ! i = add_edge l li x ! i"
proof-
  from assms have dom: "add_edge_dom (l, li, x)" 
    by (simp add: add_edge_domain path_nodes_lt_length_l)
  from dom assms show ?thesis 
  proof(induction arbitrary: p\<^sub>1 rule: add_edge.pinduct)
    case (1 pf e e')
    then have invar: "ufa_invar (add_edge pf e e')" 
      using add_edge_ufa_invar_invar path_nodes_lt_length_l by blast
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then have add_edge: "add_edge pf e e' = pf[e := e']" 
        by (simp add: "1.hyps" add_edge.psimps)
      from 1 have "i \<noteq> e" 
        by (metis True list.set_intros(1) path_no_cycle path_nodes_lt_length_l rep_of_refl)
      then show ?thesis 
        by (simp add: add_edge)
    next
      case False
      then have add_edge: "add_edge pf e e' = add_edge (pf[e := e']) (pf ! e) e" 
        by (simp add: "1.hyps" add_edge.psimps)
      from ufa_invar_fun_upd' 1 have invar: "ufa_invar (pf[e := e'])" 
        by blast
      from 1 have "last p\<^sub>1 = e" 
        using path_last by blast
      with 1 have "i \<noteq> e" 
        by (metis Misc.last_in_set path_not_empty)
      from 1 have path_to_parent: "path pf (rep_of pf (pf ! e)) (butlast p\<^sub>1) (pf ! e)"
        by (metis False path_butlast path_nodes_lt_length_l rep_of_min rep_of_step)
      with 1 have "path (pf[e := e']) (rep_of (pf[e := e']) (pf ! e)) (butlast p\<^sub>1) (pf ! e)"
        using path_fun_upd path_remove_right rep_of_fun_upd in_set_tlD by metis
      have "rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)" 
        using "1.prems" path_to_parent path_remove_right rep_of_fun_upd by auto
      from invar path_to_root_correct 
      have "path (pf[e := e']) (rep_of (pf[e := e']) e) (path_to_root (pf[e := e']) e) e" 
        using "1.prems" path_nodes_lt_length_l by auto
      then have "path (pf[e := e']) (rep_of (pf[e := e']) e') (butlast (path_to_root (pf[e := e']) e)) e'" 
        using "1.prems" path_nodes_lt_length_l 
        by (metis invar nth_list_update_eq path_butlast rep_of_idx rep_of_root)
      then have "e \<notin> set (butlast (path_to_root (pf[e := e']) e))" 
        using \<open>path (pf[e := e']) (rep_of (pf[e := e']) e) (path_to_root (pf[e := e']) e) e\<close> invar path_remove_right by presburger
      have "rep_of (pf[e := e']) e' = rep_of pf e'" 
        by (metis \<open>e \<notin> set (butlast (path_to_root (pf[e := e']) e))\<close> \<open>path (pf[e := e']) (rep_of (pf[e := e']) e') (butlast (path_to_root (pf[e := e']) e)) e'\<close> invar list_update_id list_update_overwrite rep_of_fun_upd)
      have "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        by (metis "1.prems"(1) "1.prems"(2) "1.prems"(5) \<open>rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)\<close> \<open>rep_of (pf[e := e']) e' = rep_of pf e'\<close> invar length_list_update nth_list_update_eq path_nodes_lt_length_l rep_of_idx)
      with 1 invar have "pf[e := e'] ! i = add_edge (pf[e := e']) (pf ! e) e ! i" 
        by (metis \<open>path (pf[e := e']) (rep_of (pf[e := e']) (pf ! e)) (butlast p\<^sub>1) (pf ! e)\<close> \<open>path (pf[e := e']) (rep_of (pf[e := e']) e) (path_to_root (pf[e := e']) e) e\<close> in_set_butlastD path_nodes_lt_length_l)
      then show ?thesis 
        using \<open>i \<noteq> e\<close> add_edge by force
    qed
  qed
qed

lemma path_to_root_fun_upd: 
  assumes "ufa_invar l" "path l (rep_of l li) p\<^sub>1 li" "i \<notin> set p\<^sub>1" "li < length l"
    and invar: "ufa_invar (CONST list_update l i y')"
  shows "path_to_root (l[i := y']) li = path_to_root l li"
proof-
  have "path l (rep_of l li) (path_to_root l li) li" 
    using assms(1) assms(2) path_nodes_lt_length_l path_to_root_correct by auto
  with assms have p1: "path (l[i := y']) (rep_of (l[i := y']) li) (path_to_root l li) li"
    by (metis path_fun_upd path_unique rep_of_fun_upd in_set_tlD)
  have "path (l[i := y']) (rep_of (l[i := y']) li) (path_to_root (l[i := y']) li) li" 
    by (simp add: invar assms(4) path_to_root_correct)
  with p1 path_unique show ?thesis 
    using invar by blast
qed

lemma path_to_root_fun_upd': 
  assumes "ufa_invar l" "rep_of l li \<noteq> rep_of l i" "li < length l"
    and "ufa_invar (CONST list_update l i y')"
  shows "path_to_root (l[i := y']) li = path_to_root l li"
proof(rule path_to_root_fun_upd)
  show "path l (rep_of l li) (path_to_root l li) li"
    by (simp add: assms(1) assms(3) path_to_root_correct)
  with assms show "i \<notin> set (path_to_root l li)"
    by (metis in_set_conv_nth nodes_path_rep_of(2))
qed(simp_all add: assms)

lemma nth_add_edge_e_eq_e': 
  assumes "ufa_invar pf" "e < length pf" "e' < length pf"
    "rep_of pf e \<noteq> rep_of pf e'"
  shows "(add_edge pf e e') ! e = e'"
proof-
  from assms have dom: "add_edge_dom (pf, e, e')" 
    by (simp add: add_edge_domain)
  from dom assms show ?thesis 
  proof(induction rule: add_edge.pinduct)
    case (1 pf e e')
    then have invar: "ufa_invar (add_edge pf e e')" 
      using add_edge_ufa_invar_invar by blast
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then show ?thesis 
        by (simp add: "1.hyps" "1.prems"(2) add_edge.psimps)
    next
      case False
      have invar: "ufa_invar (pf[e := e'])" 
        using "1.prems" ufa_invar_fun_upd' by auto
      have "path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)" 
        by (simp add: "1.prems"(1) "1.prems"(2) \<open>ufa_invar (pf[e := e'])\<close> path_to_root_correct ufa_invarD(2)) 
      with 1(3,4) invar path_remove_child[of "pf" "rep_of (pf[e := e']) (pf ! e)" "path_to_root (pf[e := e']) (pf ! e)" e]
      have "e \<notin> set (path_to_root pf (pf ! e))" 
        using False path_remove_child by blast
      have "path (pf[e := e']) (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)" 
        by (metis in_set_tlD \<open>e \<notin> set (path_to_root pf (pf ! e))\<close> \<open>path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)\<close> path_fun_upd)
      with "1.prems" add_edge_list_unchanged[of "pf[e := e']" "pf ! e" _ e e] have "add_edge (pf[e := e']) (pf ! e) e ! e = (pf[e := e']) ! e"
        by (metis \<open>e \<notin> set (path_to_root pf (pf ! e))\<close> \<open>path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)\<close> invar length_list_update list_update_overwrite nth_list_update_eq rep_of_fun_upd rep_of_idx ufa_compress_aux(2))
      with 1 show ?thesis 
        by (metis add_edge.psimps nth_list_update_eq)
    qed
  qed
qed

text \<open>\<open>add_edge\<close> reverses all the edges for e to its root, and then adds an edge from e to e'. \<close>
lemma add_edge_correctness: 
  assumes "ufa_invar pf" "e < length pf" "e' < length pf"
    "rep_of pf e \<noteq> rep_of pf e'"
  shows "path (add_edge pf e e') e' ([e'] @ rev (path_to_root pf e)) (rep_of pf e)"
proof-
  from assms have dom: "add_edge_dom (pf, e, e')" 
    by (simp add: add_edge_domain)
  from dom assms show ?thesis 
  proof(induction rule: add_edge.pinduct)
    case (1 pf e e')
    then have invar: "ufa_invar (add_edge pf e e')" 
      using add_edge_ufa_invar_invar by blast
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then have add_edge: "add_edge pf e e' = pf[e := e']" 
        by (simp add: "1.hyps" add_edge.psimps)
      have "rep_of pf e = e" 
        by (simp add: True rep_of_refl)
      with True 1 have "path_to_root pf e = [e]" 
        by (metis \<open>rep_of pf e = e\<close> path_to_root_correct path_unique single)
      then have "rev (path_to_root pf e) = [e]" by simp
      then have "path (add_edge pf e e') (rep_of pf e) (rev (path_to_root pf e)) e"
        by (simp add: "1.prems"(2) \<open>rep_of pf e = e\<close> add_edge single)
      then have "path (add_edge pf e e') e' [e', e] e" 
        using add_edge invar 1
        by (metis \<open>rep_of pf e = e\<close> \<open>rev (path_to_root pf e) = [e]\<close> nth_list_update_eq path.step path_nodes_lt_length_l ufa_invarD(2))
      then show ?thesis 
        by (simp add: \<open>rep_of pf e = e\<close> \<open>rev (path_to_root pf e) = [e]\<close>)
    next
      case False
      then have add_edge: "add_edge pf e e' = add_edge (pf[e := e']) (pf ! e) e" 
        by (simp add: "1.hyps" add_edge.psimps)
      from 1 have "rep_of (pf[e := e']) e = rep_of (pf[e := e']) e'" 
        by (metis length_list_update nth_list_update_eq rep_of_idx ufa_invar_fun_upd')
      have path_e': "path pf (rep_of pf e') (path_to_root pf e') e'" "e \<notin> set (path_to_root pf e')" 
         apply (simp add: "1.prems" path_to_root_correct)
        by (metis "1.prems" in_set_conv_nth path_rep_of_neq_not_in_path path_to_root_correct)
      have path_pf_e: "path pf (rep_of pf (pf ! e)) (butlast (path_to_root pf e)) (pf ! e)" "e \<notin> set (butlast (path_to_root pf e))" 
         apply (metis "1.prems" False path_butlast path_to_root_correct rep_of_min rep_of_step)
        by (metis "1.prems" path_remove_right path_to_root_correct)
      with rep_of_fun_upd path_e' 1 have "rep_of (pf[e := e']) e' = rep_of pf e'" "rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)" 
        by auto
      then have "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        by (simp add: 1 \<open>rep_of (pf[e := e']) e = rep_of (pf[e := e']) e'\<close> rep_of_idx)
      with 1 have path_add_edge: "path (add_edge (pf[e := e']) (pf ! e) e) e ([e] @ rev (path_to_root (pf[e := e']) (pf ! e)))
     (rep_of (pf[e := e']) (pf ! e))" 
        by (metis length_list_update ufa_invarD(2) ufa_invar_fun_upd')
      have "path pf (rep_of pf e) (path_to_root pf e) e" 
        by (simp add: "1.prems" path_to_root_correct)
      then have "last (path_to_root pf e) = e" 
        using path_last by auto
      have "(add_edge pf e e') ! e = e'" 
        by (simp add: "1.prems" nth_add_edge_e_eq_e')
      from "1.prems" have *: "path_to_root pf  (pf ! e) @ [e] = path_to_root pf e" 
        by (metis False append_butlast_last_id butlast.simps(1) last_path path_pf_e(1) path_to_root_correct path_unique ufa_invarD(2))
      with path_pf_e "1.prems"(1) path_to_root_fun_upd have "path_to_root (pf[e := e']) (pf ! e) = path_to_root pf (pf ! e)" 
        by (metis path_e' path_nodes_lt_length_l ufa_invar_fun_upd)
      with * have **: "tl(rev (path_to_root pf e)) = rev (path_to_root (pf[e := e']) (pf ! e))" 
        by (metis butlast_snoc rev_butlast_is_tl_rev)
      have "hd(rev (path_to_root pf e)) = e" 
        by (simp add: \<open>last (path_to_root pf e) = e\<close> hd_rev)
      with "1.prems" path_add_edge add_edge  ** show ?thesis 
        by (metis "*" Cons_eq_appendI False \<open>add_edge pf e e' ! e = e'\<close> \<open>path_to_root (pf[e := e']) (pf ! e) = path_to_root pf (pf ! e)\<close> \<open>rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)\<close> append_Nil2 butlast.simps(2) empty_append_eq_id invar last.simps list_tail_coinc path.step path_no_cycle path_nodes_lt_length_l rep_of_step rev.simps(1) rev.simps(2) rev_append rev_singleton_conv snoc_eq_iff_butlast ufa_invarD(2))
    qed
  qed
qed

subsection \<open>Termination and correctness of \<open>add_label\<close>\<close>

text \<open>The termination of add_label only depends on pf and y.\<close>
lemma add_label_dom_pf_y: "add_label_dom (pfl, pf, y, x) \<Longrightarrow> add_label_dom (pfl', pf, y, x')"
proof(induction arbitrary: pfl' x' rule: add_label.pinduct)
  case (1 pfl pf e lbl)
  then show ?case proof(cases "pf ! e = e")
    case True
    with add_label.domintros show ?thesis by blast
  next
    case False
    have "add_label_dom (pfl'[e := Some x'], pf, pf ! e, the (pfl' ! e))"
      by (simp add: "1.IH" False)
    with add_label.domintros show ?thesis by blast
  qed
qed

lemma rep_of_dom_iff_add_label_dom: "rep_of_dom (pf, y) \<longleftrightarrow> add_label_dom (pfl, pf, y, y')"
proof
  show "rep_of_dom (pf, y) \<Longrightarrow> add_label_dom (pfl, pf, y, y')"
  proof(induction rule: rep_of.pinduct)
    case (1 l i)
    then show ?case proof(cases "l ! i = i")
      case True
      then show ?thesis 
        using add_label.domintros by blast
    next
      case False
      then have "add_label_dom (pfl, l, l ! i, y')" 
        by (simp add: "1.IH")
      then have "add_label_dom (pfl[i := Some y'], l, l ! i, the (pfl ! i))" 
        using add_label_dom_pf_y by blast
      then show ?thesis using add_label.domintros by blast
    qed
  qed
next
  show "add_label_dom (pfl, pf, y, y') \<Longrightarrow> rep_of_dom (pf, y)"
  proof(induction rule: add_label.pinduct)
    case (1 pfl pf e lbl)
    then show ?case apply(cases "pf ! e = e")
      using rep_of.domintros by blast+
  qed
qed

lemma add_label_domain: 
  assumes "ufa_invar pf" "y < length pf"
  shows "add_label_dom (pfl, pf, y, y')"
  using assms rep_of_dom_iff_add_label_dom 
  by (simp add: ufa_invar_def)

subsection \<open>Validity and correctness of \<open>set_lookup\<close>\<close>

lemma set_lookup_unchanged:
  assumes "l ! i \<noteq> i \<or> l ! j \<noteq> j" "i < length t" "j < length (t ! i)" "ufa_invar l"
    "\<forall> k < length xs . (\<exists> b\<^sub>1 b\<^sub>2 b . xs ! k = (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and> 
      b\<^sub>1 < length l \<and> b\<^sub>2 < length l \<and> b < length l)"
  shows "set_lookup t xs l ! i ! j = t ! i ! j"
  using assms proof(induction rule: set_lookup.induct)
  case (1 t l)
  then show ?case by simp
next
  case (2 t a\<^sub>1 a\<^sub>2 a xs l)
  then have "a\<^sub>1 < length l" "a\<^sub>2 < length l" "a < length l"
    by fastforce+
  then have "l ! rep_of l a\<^sub>1 = rep_of l a\<^sub>1" "l ! rep_of l a\<^sub>2 = rep_of l a\<^sub>2"
    by (simp_all add: "2.prems"(4) rep_of_root)
  then have "rep_of l a\<^sub>1 \<noteq> i \<or> rep_of l a\<^sub>2 \<noteq> j" 
    using "2.prems"(1) by blast
  from 2 have " \<forall>k<length xs. \<exists>b\<^sub>1 b\<^sub>2 b. xs ! k = F b\<^sub>1 b\<^sub>2 \<approx> b \<and> b\<^sub>1 < length l \<and> b\<^sub>2 < length l \<and> b < length l "
    by (metis in_set_conv_nth list.set_intros(2))
  with 2 have "set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) xs l ! i ! j =
    upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)) ! i ! j" 
    using length_list_update nth_list_update_eq nth_list_update_neq 
    by (metis (no_types, lifting))
  then show ?case 
    by (metis \<open>rep_of l a\<^sub>1 \<noteq> i \<or> rep_of l a\<^sub>2 \<noteq> j\<close> nth_list_update' set_lookup.simps(2))
next
  case (3 t a b xs l)
  then show ?case 
    by (metis bot_nat_0.extremum bot_nat_0.not_eq_extremum equation.distinct(1) impossible_Cons nth_Cons_0)
qed

lemma length_Cons:
  assumes "xs = a # ys"
  shows "length xs > 0" 
  by (simp add: assms)

abbreviation lookup_valid_element :: "equation option list list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
    "lookup_valid_element t l i j \<equiv> t ! i ! j = None \<or> 
(\<exists>a\<^sub>1 a\<^sub>2 aa. t ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> aa) \<and>
  rep_of l a\<^sub>1 = i \<and> rep_of l a\<^sub>2 = j \<and>
  a\<^sub>1 < length l \<and> a\<^sub>2 < length l \<and> aa < length l)"

abbreviation set_lookup_valid_input :: "equation list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "set_lookup_valid_input xs l \<equiv> 
\<forall> i < length xs . (\<exists>a\<^sub>1 a\<^sub>2 a. xs ! i = (F a\<^sub>1 a\<^sub>2 \<approx> a) \<and> a\<^sub>1 < length l \<and> a\<^sub>2 < length l \<and> a < length l)"

abbreviation quadratic_table :: "'a list list \<Rightarrow> bool"
  where
    "quadratic_table xs \<equiv> \<forall> i < length xs . length (xs ! i) = length xs"

lemma set_lookup_valid: 
  assumes "lookup_valid_element t l i j" 
    "l ! i = i" "l ! j = j"
    "set_lookup_valid_input xs l"
    "length t = length l" "ufa_invar l" "quadratic_table t"
  shows "lookup_valid_element (set_lookup t xs l) l i j"
  using assms proof(induction t xs l rule: set_lookup.induct)
  case (1 t l)
  then show ?case 
    by simp
next
  case (2 t a\<^sub>1 a\<^sub>2 a' xs l)
  then show ?case proof(cases "set_lookup t ((F a\<^sub>1 a\<^sub>2 \<approx> a') # xs) l ! i ! j")
    case None
    then show ?thesis by blast
  next
    case (Some k) 
    have a_length: "a\<^sub>1 < length l" "a\<^sub>2 < length l" "a' < length l"
      using "2.prems" by fastforce+
    then have "rep_of l a\<^sub>1 < length t" "rep_of l a\<^sub>2 < length (t ! rep_of l a\<^sub>1)" 
      by (simp_all add: "2.prems" rep_of_less_length_l)
    then have lookup_entry: "lookup_entry (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a'))) l  a\<^sub>1  a\<^sub>2 = Some (F a\<^sub>1 a\<^sub>2 \<approx> a')" 
      by fastforce
    then have "\<not> (lookup_None (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a'))) l) (F a\<^sub>1 a\<^sub>2 \<approx> a')"
      by force
    have **: "set_lookup_valid_input xs l"
      "length (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a'))) = length l" 
      "\<forall>i<length (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a'))).
       length (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a')) ! i) =
       length (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a')))" 
      using 2(5) apply auto[1] using 2(6) apply auto[2] using 2(8)
      by (metis length_list_update nth_list_update_eq nth_list_update_neq)
    then show ?thesis proof(cases "i = rep_of l a\<^sub>1 \<and> j = rep_of l a\<^sub>2")
      case True
      with lookup_entry have *: "upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a')) ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> a')"
        by blast
      with 2 * ** a_length True 
      have IH: "lookup_valid_element (set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a'))) xs l) l i j" 
        by auto
      then show ?thesis by simp
    next
      case False
      then have *: "upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a')) ! i ! j = t ! i ! j" 
        by (metis \<open>rep_of l a\<^sub>1 < length t\<close> nth_list_update_eq nth_list_update_neq)
      with 2 * ** 
      have IH: "lookup_valid_element (set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a'))) xs l) l i j" 
        by presburger
      have "set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a'))) xs l ! i ! j = 
          set_lookup t ((F a\<^sub>1 a\<^sub>2 \<approx> a') # xs) l ! i ! j" by auto
      with IH * show ?thesis by metis
    qed
  qed
next
  case (3 t a2 b2 xs l)
  then have "(\<exists>a\<^sub>1 a\<^sub>2 c. a2 \<approx> b2 = (F a\<^sub>1 a\<^sub>2 \<approx> c))" 
    by auto
  then show ?case by simp
qed

text \<open>if \<open>set_lookup\<close> changes an entry, then this changed entry is valid.\<close>

lemma set_lookup_valid2: 
  assumes "t ! i ! j \<noteq> (set_lookup t xs l) ! i ! j"
    "l ! i = i" "l ! j = j"
    "set_lookup_valid_input xs l"
    "length t = length l" "ufa_invar l" "quadratic_table t"
  shows "lookup_valid_element (set_lookup t xs l) l i j"
using assms proof(induction t xs l rule: set_lookup.induct)
  case (1 t l)
  then show ?case by simp
next
  case (2 t a\<^sub>1 a\<^sub>2 a xs l)
  then show ?case proof(cases "upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)) ! i ! j =
    set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) xs l ! i ! j")
    case True
    then have "upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)) ! i ! j \<noteq> t ! i ! j" 
      by (metis "2.prems"(1) set_lookup.simps(2))
    then have "i = rep_of l a\<^sub>1" "j = rep_of l a\<^sub>2" 
       apply (metis nth_list_update_neq) 
      by (metis "2.prems"(1) True nth_list_update' set_lookup.simps(2))
    then have "(set_lookup t ((F a\<^sub>1 a\<^sub>2 \<approx> a) # xs) l) ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)" 
      by (metis "2.prems"(1) True nth_list_update' set_lookup.simps(2))
    have "a\<^sub>1 < length l \<and> a\<^sub>2 < length l \<and> a < length l" 
      using "2.prems"(4) by auto
    with True show ?thesis 
      using \<open>i = rep_of l a\<^sub>1\<close> \<open>j = rep_of l a\<^sub>2\<close> \<open>set_lookup t ((F a\<^sub>1 a\<^sub>2 \<approx> a) # xs) l ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)\<close> by blast
  next
    case False
    with 2 have "set_lookup_valid_input xs l" 
      by auto
    have "length (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) = length l" 
   "quadratic_table (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)))" 
       apply (simp add: "2.prems"(5))
      by (simp add: "2.prems"(7) nth_list_update')
    with 2 False have "lookup_valid_element
     (set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) xs l) l i j"
      using \<open>set_lookup_valid_input xs l\<close> by fastforce
    then show ?thesis 
      using set_lookup.simps(2) by presburger
  qed
next
  case (3 t a b xs l)
  then have "set_lookup_valid_input xs l" 
    by auto
  with 3 have "lookup_valid_element (set_lookup t xs l) l i j" 
    by auto
  then show ?case by simp
qed


lemma set_lookup_valid_length: 
  assumes "quadratic_table t"
  shows "quadratic_table (set_lookup t xs l)"
  using assms proof(induction t xs l rule: set_lookup.induct)
  case (2 t a\<^sub>1 a\<^sub>2 a xs l)
  then have "quadratic_table (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)))" 
    by (simp add: nth_list_update')
  with 2 show ?case 
    using set_lookup.simps(2) by presburger
qed simp_all

lemma ufa_union_lookup_valid: 
  assumes "lookup_valid_element t l i j" "(ufa_union l a b) ! i = i" "(ufa_union l a b) ! j = j" 
    "a < length l" "b < length l" "ufa_invar l"
  shows "lookup_valid_element t (ufa_union l a b) i j"
proof(cases "t ! i ! j = None")
  case True
  then show ?thesis 
    by blast
next
  case False
  from assms have "l ! i = i" "l ! j = j" 
    using False rep_of_min by blast+
  then show ?thesis 
    by (metis (no_types, lifting) assms length_list_update nth_list_update_eq rep_of_less_length_l ufa_union_aux)
qed


text \<open>A lookup entry is either in the list xs or remains unchanged after \<open>set_lookup xs\<close>
      if it is not in xs. \<close>
lemma lookup_step_unchanged:
  assumes "t ! a' ! b' = k"
  shows "(\<exists> a b c. (F a b \<approx> c) \<in> set xs \<and> rep_of l a = a' \<and> rep_of l b = b') 
\<or> (set_lookup t xs l) ! a' ! b' = k"
using assms proof(induction t xs l rule: set_lookup.induct)
  case (1 t l)
  then show ?case 
    by simp
next
  case (2 t a\<^sub>1 a\<^sub>2 a\<^sub>3 xs l)
  then show ?case
  proof(cases "upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a\<^sub>3)) ! a' ! b' = k")
    case True
    with 2 show ?thesis by auto
  next
    case False
    with 2 have "rep_of l a\<^sub>1 = a' \<and> rep_of l a\<^sub>2 = b'" 
      using nth_list_update' by metis 
    then show ?thesis 
      by auto
  qed
next
  case (3 t a b xs l)
  then show ?case 
    by auto
qed

text \<open>Two equations \<open>F a\<^sub>1 a\<^sub>2 \<approx> a\<close> and \<open>F b\<^sub>1 b\<^sub>2 \<approx> b\<close> in u_a are either identical or do not have
the same representatives for \<open>a\<^sub>1,b\<^sub>1\<close> and \<open>a\<^sub>2,b\<^sub>2\<close>.
We need this to prove that set_lookup doesn't overwrite any value that it sets in lookup.\<close>
abbreviation no_duplicate_representatives :: "equation list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"no_duplicate_representatives u_a l \<equiv> (\<forall>i < length u_a . (\<forall> j < length u_a. (
u_a ! i = u_a ! j \<or> (
\<exists> a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b. u_a ! i = (F a\<^sub>1 a\<^sub>2 \<approx> a) \<and> u_a ! j = (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and> 
(rep_of l a\<^sub>1 \<noteq> rep_of l b\<^sub>1 \<or> rep_of l a\<^sub>2 \<noteq> rep_of l b\<^sub>2)
)
)))"

lemma no_duplicate_representatives_Cons:
  assumes "no_duplicate_representatives (x#xs) l"
  shows "no_duplicate_representatives xs l"
proof(standard, standard, standard, standard)
  fix i j 
  assume "i < length xs" "j < length xs"
  then have "xs ! i = (x # xs) ! (i + 1)""xs ! j = (x # xs) ! (j + 1)"
"i + 1 < length (x # xs)""j + 1 < length (x # xs)"
    by auto
  with assms show "xs ! i = xs ! j \<or>
           (\<exists>a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b.
               xs ! i = F a\<^sub>1 a\<^sub>2 \<approx> a \<and>
               xs ! j = F b\<^sub>1 b\<^sub>2 \<approx> b \<and> (rep_of l a\<^sub>1 \<noteq> rep_of l b\<^sub>1 \<or> rep_of l a\<^sub>2 \<noteq> rep_of l b\<^sub>2))"
    by presburger
qed

lemma no_duplicates_and_no_duplicate_representatives:
  assumes "F c\<^sub>1 c\<^sub>2 \<approx> c \<notin> set xs" "no_duplicate_representatives ((F c\<^sub>1 c\<^sub>2 \<approx> c) # xs) l"
  shows "~(\<exists> a b c. (F a b \<approx> c) \<in> set xs \<and> rep_of l a = rep_of l c\<^sub>1 \<and> rep_of l b = rep_of l c\<^sub>2)"
proof
  assume "\<exists>a b c. F a b \<approx> c \<in> set xs \<and> rep_of l a = rep_of l c\<^sub>1 \<and> rep_of l b = rep_of l c\<^sub>2"
  then obtain a b d where "F a b \<approx> d \<in> set xs" 
"rep_of l a = rep_of l c\<^sub>1" "rep_of l b = rep_of l c\<^sub>2"
    by blast
  with assms have "F a b \<approx> d \<noteq> F c\<^sub>1 c\<^sub>2 \<approx> c" 
    by fast
  then obtain i where "i < length xs" "xs ! i = F a b \<approx> d"
    by (metis \<open>F a b \<approx> d \<in> set xs\<close> in_set_conv_nth)
  then have "((F c\<^sub>1 c\<^sub>2 \<approx> c) # xs) ! 0 = (F c\<^sub>1 c\<^sub>2 \<approx> c)" "0 < length ((F c\<^sub>1 c\<^sub>2 \<approx> c) # xs)"
 "((F c\<^sub>1 c\<^sub>2 \<approx> c) # xs) ! (i + 1) = F a b \<approx> d" "i + 1 < length ((F c\<^sub>1 c\<^sub>2 \<approx> c) # xs)"
    by auto
  with assms show "False" 
    by (metis \<open>F a b \<approx> d \<noteq> F c\<^sub>1 c\<^sub>2 \<approx> c\<close> \<open>rep_of l a = rep_of l c\<^sub>1\<close> \<open>rep_of l b = rep_of l c\<^sub>2\<close> equation.inject(2))
qed

lemma set_lookup_correct:
  assumes "F c\<^sub>1 c\<^sub>2 \<approx> c \<in> set xs" "no_duplicate_representatives xs l"
"length t = length l" "ufa_invar l" "c\<^sub>1 < length l" "c\<^sub>2 < length l" "rep_of l c\<^sub>2 < length (t ! rep_of l c\<^sub>1)"
  shows "lookup_entry (set_lookup t xs l) l c\<^sub>1 c\<^sub>2 = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
using assms proof(induction t xs l rule: set_lookup.induct)
  case (1 t l)
  then show ?case by simp
next
  case (2 t a\<^sub>1 a\<^sub>2 a xs l)
  then show ?case proof(cases "F c\<^sub>1 c\<^sub>2 \<approx> c \<in> set xs")
    case True
    with 2 have "no_duplicate_representatives xs l" "rep_of l c\<^sub>2
    < length (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)) ! rep_of l c\<^sub>1)"
      using no_duplicate_representatives_Cons 2 apply presburger 
      by (simp add: "2.prems"(7) nth_list_update')
  with 2 True show ?thesis 
    by fastforce
next 
  case False
  then have "F c\<^sub>1 c\<^sub>2 \<approx> c = F a\<^sub>1 a\<^sub>2 \<approx> a" 
    using "2.prems"(1) by auto
  then have a_c: "a\<^sub>1 = c\<^sub>1" "a\<^sub>2 = c\<^sub>2" by auto 
  with 2 have "lookup_entry (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) l c\<^sub>1 c\<^sub>2 = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    by (metis \<open>F c\<^sub>1 c\<^sub>2 \<approx> c = F a\<^sub>1 a\<^sub>2 \<approx> a\<close> nth_list_update_eq rep_of_bound)
  from 2 no_duplicates_and_no_duplicate_representatives a_c False
  have "~(\<exists> a b c. (F a b \<approx> c) \<in> set xs \<and> rep_of l a = rep_of l a\<^sub>1 \<and> rep_of l b = rep_of l a\<^sub>2)"
    by simp
  with lookup_step_unchanged show ?thesis unfolding set_lookup.simps
    using a_c \<open>lookup_entry (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) l c\<^sub>1 c\<^sub>2 = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)\<close> by blast
  qed
next
  case (3 t a b xs l)
  then have "F c\<^sub>1 c\<^sub>2 \<approx> c \<in> set xs" "no_duplicate_representatives xs l"
    apply simp 
    using no_duplicate_representatives_Cons 3(3) by presburger
  with 3 show ?case 
    by fastforce
qed

lemma set_lookup_changed:
  assumes "set_lookup t xs l ! i ! j = Some m" "t ! i ! j = k" "k \<noteq> Some m"
  shows "m \<in> set xs"
using assms proof(induction arbitrary: k rule: set_lookup.induct)
  case (2 t a\<^sub>1 a\<^sub>2 a xs l)
  have "set_lookup (upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a))) xs l ! i ! j = Some m"
    using "2.prems"(1) by auto
  then show ?case 
  proof(cases "upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> a)) ! i ! j = Some m")
    case False
    with 2 have "m \<in> set xs" by force
    then show ?thesis by simp
  next
    case True
    with 2(3,4) have "i = rep_of l a\<^sub>1" "j = rep_of l a\<^sub>2" 
      by (metis nth_list_update')+ 
    with 2 True have "m = F a\<^sub>1 a\<^sub>2 \<approx> a" 
      by (metis nth_list_update' option.inject)
    then show ?thesis 
      by simp
  qed
qed auto

end
