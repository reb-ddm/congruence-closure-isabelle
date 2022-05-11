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

text "In order to show that the termination invariant holds after adding an edge or a label to the proof forest,
we need to show a few invariants after function update"

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
      using path_fun_upd path_unique step.hyps(1) step.prems(1) step.prems(2) by blast
    with step have "path (l[i := y]) (rep_of l li) (butlast (path_to_root l li)) (l!li)" 
      by (metis \<open>path l (rep_of l li) (path_to_root l li) li\<close> in_set_butlastD path_fun_upd path_to_parent path_unique rep_of_step)
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

lemma ufa_invar_fun_upd: 
  assumes "ufa_invar l" "y < length l" "path l (rep_of l y) py y" "i \<notin> set py"
  shows "ufa_invar (CONST list_update l i y)"
  unfolding ufa_invar_def
proof(standard, standard, standard)
  fix ia
  assume ia_valid: "ia < length (l[i := y])"
  with assms show "l[i := y] ! ia < length (l[i := y])"
    by (metis length_list_update nth_list_update' ufa_invarD(2))
  have path_root: "path l (rep_of l ia) (path_to_root l ia) ia" 
    using ia_valid assms(1) path_to_root_correct by auto
  show "rep_of_dom (l[i := y], ia)"
    proof(cases "i \<in> set (path_to_root l ia)")
      case False
      \<comment> \<open>The path to the root of ia still exists after the function update.\<close>
      with path_fun_upd path_root have "path (l[i := y]) (rep_of l ia) (path_to_root l ia) ia" 
        by blast
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
      then have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) (hd i_ia) i_ia ia" 
        by (simp add: \<open>i_ia \<noteq> [] \<Longrightarrow> path l (hd i_ia) i_ia ia\<close> path_fun_upd)
      have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) i [i, hd i_ia] (hd i_ia)" 
        using path_nodes_lt_length_l paths(1) single 
        by (smt (verit, best) \<open>i \<notin> set i_ia\<close> append_Cons_eq_iff length_list_update nth_list_update_neq path.simps path_hd)
      with path_concat1 have p_l_upd_i_ia: "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) i (i#i_ia) ia" 
        by (smt (verit, ccfv_threshold) \<open>i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) (hd i_ia) i_ia ia\<close> list.sel(1) list.sel(3) not_Cons_self2 path.cases path.step)
      from assms path_fun_upd have path_rep_y: "path (l[i := y]) (rep_of l y) py y" 
        by simp
      from assms have "path (l[i := y]) y [y, i] i" 
        by (metis \<open>path (l[i := y]) (rep_of l y) py y\<close> hd_in_set length_list_update nth_list_update_eq path.simps path_hd path_no_root paths(1))
      with p_l_upd_i_ia path_concat1 have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) y ([y, i] @ i_ia) ia" 
        by fastforce
      with path_concat1 path_rep_y have "i_ia \<noteq> [] \<Longrightarrow> path (l[i := y]) (rep_of l y) (py @ [i] @ i_ia) ia" 
        by fastforce
      with path_root_rep_of_dom have "i_ia \<noteq> [] \<Longrightarrow> rep_of_dom (l[i := y], ia)"
        by (metis assms(1) assms(2) assms(4) hd_in_set list.distinct(1) nth_list_update_neq path.simps path_hd path_rep_y rep_of_root)
       with path_concat1 path_rep_y have "i_ia = [] \<Longrightarrow> path (l[i := y]) (rep_of l y) (py @ [i]) i" 
         using \<open>path (l[i := y]) y [y, i] i\<close> 
         by fastforce
      with assms show ?thesis 
        by (metis \<open>i_ia \<noteq> [] \<Longrightarrow> rep_of_dom (l[i := y], ia)\<close>  list.set_intros(1) nth_list_update_neq path.simps path_length_1 path_root_rep_of_dom paths(1) rep_of_min)
    qed
qed

lemma add_edge_ufa_invar_invar: 
  assumes "add_edge_dom (l, e, e')" "ufa_invar l" 
          "e' < length l" "e < length l" 
          "rep_of l e \<noteq> rep_of l e'"
  shows "ufa_invar (add_edge l e e')"
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

lemma add_edge_fun_upd: 
  assumes "add_edge_dom (l, li, x)" "ufa_invar l"
    "path l (rep_of l li) p\<^sub>1 li" "x < length l"
    "i \<notin> set p\<^sub>1" "rep_of l li \<noteq> rep_of l x"
  shows "add_edge_dom (CONST list_update l i y', li, x)"
  using assms proof(induction l "li" x arbitrary: p\<^sub>1 rule: add_edge.pinduct)
  case (1 l li x)
  then show ?case
  proof(cases "l ! li = li")
    case True
    then show ?thesis 
      by (metis "1.prems" add_edge.domintros list.set_intros(1) nth_list_update_neq path_no_cycle path_nodes_lt_length_l rep_of_refl)
  next
    case False
    have same_rep_before: "rep_of l (l ! li) = rep_of l li" 
      using "1.prems" path_nodes_lt_length_l rep_of_idx by blast
    with 1 False have path_root: "path l (rep_of l (l ! li)) (butlast p\<^sub>1) (l ! li)" 
      using path_butlast by (metis path_nodes_lt_length_l rep_of_root)
    then have same_rep: "rep_of (l[li := x]) (l ! li) = rep_of l (l ! li)" 
      using "1.prems" path_remove_right rep_of_fun_upd by simp
    then have path_root_upd: "path (l[li := x]) (rep_of (l[li := x]) (l ! li)) (butlast p\<^sub>1) (l ! li)" 
      using "1.prems" path_root path_fun_upd path_remove_right by presburger
    have i_notin_path: "i \<notin> set (butlast p\<^sub>1)"
      by (metis "1.prems"(4) in_set_butlastD)
    have path_x_root: "path l (rep_of l x) (path_to_root l x) x" 
      by (simp add: "1.prems" path_to_root_correct)
    with 1 have li_notin_path: "li \<notin> set (path_to_root l x)" 
      by (metis in_set_conv_nth nodes_path_rep_of(2))
    with ufa_invar_fun_upd have invar: "ufa_invar (l[li := x])" 
      using "1.prems" path_x_root by blast
    then have "add_edge_dom (l[li := x, i := y'], l ! li, li)"
      using 1 False i_notin_path path_root_upd 
      by (metis li_notin_path same_rep length_list_update nth_list_update_eq path_nodes_lt_length_l path_x_root rep_of_fun_upd rep_of_idx)
    with 1 show ?thesis 
      by (metis (no_types, lifting) invar add_edge.domintros length_list_update li_notin_path list_update_swap nth_list_update_eq nth_list_update_neq path_nodes_lt_length_l path_x_root rep_of_fun_upd rep_of_idx)
  qed
qed

corollary add_edge_fun_upd_parent: 
  assumes "add_edge_dom (l, l ! i, x)" "ufa_invar l"
          "x < length l" "i < length l" "rep_of l (l ! i) \<noteq> rep_of l x"
          "l ! i \<noteq> i"
    shows "add_edge_dom (l[i := y'], l ! i, x)"
proof-
  from assms have "path l (l ! i) [l ! i, i] i" 
    using path.step single ufa_invarD(2) by auto
  have "path l (rep_of l i) (path_to_root l i) i"
    by (simp add: assms(2) assms(4) path_to_root_correct)
  with assms have "path l (rep_of l i) (butlast (path_to_root l i)) (l ! i)" "i \<notin> set (butlast (path_to_root l i))"
    by (metis path_butlast rep_of_min path_remove_right)+
  with add_edge_fun_upd assms show ?thesis 
    by (metis rep_of_step)
qed

lemma add_edge_dom: "ufa_invar l \<Longrightarrow> y < length l \<Longrightarrow> add_edge_dom (l, y, y')"
proof(induction arbitrary: y' rule: rep_of_induct)
  case (base i)
  then show ?case 
    using add_edge.domintros by blast
next
  case (step i)
  have "add_edge_dom (l[i := y'], l ! i, i)"
    using add_edge_fun_upd_parent step.IH step.hyps ufa_invarD(2) by blast
  then show ?case 
    using add_edge.domintros by blast
qed




end