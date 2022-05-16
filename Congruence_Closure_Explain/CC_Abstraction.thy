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

fun valid_vars_pending :: "pending_equation \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "valid_vars_pending (One (a \<approx> b)) pf n = (valid_vars (a \<approx> b) n)"
  | "valid_vars_pending (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)) pf n = 
        (valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) n \<and> valid_vars (F b\<^sub>1 b\<^sub>2 \<approx> b) n)"
  | "valid_vars_pending _ _ _ = False"

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
abbreviation use_list_invar_correctness :: "congruence_closure \<Rightarrow> bool"
  where
    "use_list_invar_correctness cc \<equiv> (\<forall> i < nr_vars cc . (\<forall> j < length ((use_list cc) ! i) . 
(cc_list cc) ! i = i \<longrightarrow> (\<exists> b\<^sub>1 b\<^sub>2 b .
use_list cc ! i ! j = (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and> 
(i = rep_of (cc_list cc) b\<^sub>1) \<or> i = rep_of (cc_list cc) b\<^sub>2)))"

text \<open>for all pairs of representatives (i, j), Lookup(i, j) is some input equation
\<open>f(a\<^sub>1, a\<^sub>2)=a\<close> such that i and j are the current respective representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close> whenever
such an equation exists. Otherwise, Lookup(i, j) is \<bottom>\<close>
abbreviation lookup_invar_correctness :: "congruence_closure \<Rightarrow> bool"
  where
    "lookup_invar_correctness cc \<equiv> (\<forall> i < nr_vars cc . (\<forall> j < nr_vars cc . 
(cc_list cc) ! i = i \<and> (cc_list cc) ! j = j \<longrightarrow>
lookup cc ! i ! j = None \<or> (\<exists> a\<^sub>1 a\<^sub>2 a . lookup cc ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> a) \<and> 
rep_of (cc_list cc) a\<^sub>1 = i \<and> rep_of (cc_list cc) a\<^sub>2 = j)))"

definition representativeE :: "congruence_closure \<Rightarrow> equation set"
  where
    "representativeE cc = {a \<approx> rep_of (cc_list cc) a |a.  a < nr_vars cc \<and> cc_list cc ! a \<noteq> a}
\<union> {F a' b' \<approx> rep_of (cc_list cc) c | a' b' c c\<^sub>1 c\<^sub>2 . a' < nr_vars cc \<and> b' < nr_vars cc \<and> c < nr_vars cc \<and>
                      cc_list cc ! a' = a' \<and> cc_list cc ! b' = b' \<and> lookup cc ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)}"

text \<open>These invariants are needed for the termination proofs:\<close>

abbreviation proof_forest_invar_termination :: "congruence_closure \<Rightarrow> bool"
  where
    "proof_forest_invar_termination cc \<equiv> ufa_invar (proof_forest cc)"

text \<open>These invariants are needed for the validity proofs:\<close>

abbreviation pending_invar :: "pending_equation list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "pending_invar pe pf n \<equiv> (\<forall> i < length pe . valid_vars_pending (pe ! i) pf n)"

lemma pending_invar_Cons: 
  "pending_invar (pe # xs) pf n \<longleftrightarrow> pending_invar xs pf n \<and> valid_vars_pending pe pf n"
proof
  show "pending_invar (pe # xs) pf n \<Longrightarrow> pending_invar xs pf n \<and> valid_vars_pending pe pf n"
    by fastforce
next 
  show "pending_invar xs pf n \<and> valid_vars_pending pe pf n \<Longrightarrow> pending_invar (pe # xs) pf n"
    by (metis in_set_conv_nth set_ConsD)
qed

lemma pending_left_right_valid: 
  assumes "pending_invar (pe # xs) pf n"
  shows "right pe < n \<and> left pe < n"
proof(cases pe)
  case (One x1)
  have valid: "valid_vars_pending pe pf n" 
    using assms by auto
  with One valid obtain x11 x12 where Constants: "x1 = (x11 \<approx> x12)" 
    by (metis equation.exhaust valid_vars_pending.simps(3))
  with One have "left pe = x11" by simp
  with Constants One valid show ?thesis by auto
next
  case (Two x21 x22)
  have valid: "valid_vars_pending pe pf n" 
    using assms by auto
  with valid obtain x211 x212 x213 x221 x222 x223 
    where Function: "x21 = (F x211 x212 \<approx> x213)"  "x22 = (F x221 x222 \<approx> x223)" 
    by (metis Two equation.exhaust valid_vars_pending.simps(4) valid_vars_pending.simps(5))
  then show ?thesis using Two valid by auto
qed



text \<open>Here the invariants are put together:\<close>

definition use_list_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "use_list_invar cc = use_list_invar_correctness cc"

definition lookup_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "lookup_invar cc \<equiv> lookup_invar_correctness cc"

definition proof_forest_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "proof_forest_invar cc = proof_forest_invar_termination cc"

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

text \<open>The union find data structure and the proof forest have the same equivalence classes. \<close>
abbreviation pf_l_same_eq_classes :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "pf_l_same_eq_classes pf l \<equiv> (\<forall> i < length pf . (\<forall> j < length pf . rep_of l i = rep_of l j 
\<longleftrightarrow> rep_of pf i = rep_of pf j))"

definition inv3 :: "congruence_closure \<Rightarrow> bool"
  where
    "inv3 cc \<equiv> pf_l_same_eq_classes (proof_forest cc) (cc_list cc)"

lemma inv3_divided: 
  assumes "i < length pf" "j < length pf" 
    "inv3 \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "rep_of l i = rep_of l j \<longleftrightarrow> rep_of pf i = rep_of pf j"
  using assms unfolding inv3_def congruence_closure.select_convs by blast

lemma cc_\<alpha>_eq_CC_representativeE: "cc_\<alpha> cc (s \<approx> t) = Congruence_Closure (representativeE cc) (s \<approx> t)"
  sorry

abbreviation cc_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "cc_invar cc \<equiv> use_list_invar cc \<and> lookup_invar cc \<and> proof_forest_invar cc \<and> inv1 cc \<and> inv2 cc \<and> inv3 cc"

lemma cc_invar_initial_cc: "cc_invar (initial_cc n)"
  sorry

section \<open>Termination of \<open>add_edge\<close> and \<open>add_label\<close>\<close>

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

lemma ufa_invar_fun_upd2: 
  assumes "ufa_invar l" "y < length l" "rep_of l i \<noteq> rep_of l y"
  shows "ufa_invar (CONST list_update l i y)"
proof(rule ufa_invar_fun_upd)
  show "path l (rep_of l y) (path_to_root l y) y" 
    by (simp add: assms(1) assms(2) path_to_root_correct)
  with assms show "i \<notin> set (path_to_root l y)"
    by (metis in_set_conv_nth path_rep_of_neq_not_in_path)
qed (auto simp add: assms)

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
      from ufa_invar_fun_upd2 1 have invar: "ufa_invar (pf[e := e'])" 
        by blast
      from 1 have "last p\<^sub>1 = e" 
        using path_last by blast
      with 1 have "i \<noteq> e" 
        by (metis Misc.last_in_set path_not_empty)
      from 1 have path_to_parent: "path pf (rep_of pf (pf ! e)) (butlast p\<^sub>1) (pf ! e)"
        by (metis False path_butlast path_nodes_lt_length_l rep_of_min rep_of_step)
      with 1 have "path (pf[e := e']) (rep_of (pf[e := e']) (pf ! e)) (butlast p\<^sub>1) (pf ! e)"
        using path_fun_upd path_remove_right rep_of_fun_upd by presburger
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
    by (metis path_fun_upd path_unique rep_of_fun_upd)
  have "path (l[i := y']) (rep_of (l[i := y']) li) (path_to_root (l[i := y']) li) li" 
    by (simp add: invar assms(4) path_to_root_correct)
  with p1 path_unique show ?thesis 
    using invar by blast
qed

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
        using "1.prems" ufa_invar_fun_upd2 by auto
      have "path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)" 
        by (simp add: "1.prems"(1) "1.prems"(2) \<open>ufa_invar (pf[e := e'])\<close> path_to_root_correct ufa_invarD(2)) 
      with 1(3,4) invar path_remove_child[of "pf" "rep_of (pf[e := e']) (pf ! e)" "path_to_root (pf[e := e']) (pf ! e)" e]
      have "e \<notin> set (path_to_root pf (pf ! e))" 
        using False path_remove_child by blast
      have "path (pf[e := e']) (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)" 
        by (simp add: \<open>e \<notin> set (path_to_root pf (pf ! e))\<close> \<open>path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)\<close> path_fun_upd)
      with "1.prems" add_edge_list_unchanged[of "pf[e := e']" "pf ! e" _ e e] have "add_edge (pf[e := e']) (pf ! e) e ! e = (pf[e := e']) ! e"
        by (metis \<open>e \<notin> set (path_to_root pf (pf ! e))\<close> \<open>path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)\<close> add_edge_list_unchanged invar length_list_update list_update_overwrite nth_list_update_eq rep_of_fun_upd rep_of_idx ufa_compress_aux(2))
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
        by (metis length_list_update nth_list_update_eq rep_of_idx ufa_invar_fun_upd2)
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
        by (metis length_list_update ufa_invarD(2) ufa_invar_fun_upd2)
      have "path pf (rep_of pf e) (path_to_root pf e) e" 
        by (simp add: "1.prems" path_to_root_correct)
      then have "last (path_to_root pf e) = e" 
        using path_last by auto
      have "(add_edge pf e e') ! e = e'" 
        by (simp add: "1.prems" nth_add_edge_e_eq_e')
      have *: "path_to_root pf  (pf ! e) @ [e] = path_to_root pf e" 
        by (metis "1.prems" False append_butlast_last_id butlast.simps(1) last_path path_pf_e(1) path_to_root_correct path_unique ufa_invarD(2))
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

lemma "rep_of_dom (pf, y) \<longleftrightarrow> add_label_dom (pfl, pf, y, y')"
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
lemma rep_of_fun_upd2:
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "i < length l"
    and "rep_of l x \<noteq> rep_of l y"
  shows "rep_of (l[rep_of l x := y]) x = rep_of l y"
  sorry

lemma hd_tl_list: "length xs > 1 \<Longrightarrow>hd(tl xs) = xs ! 1"
  by (metis One_nat_def drop0 drop_Suc hd_drop_conv_nth)

lemma path_to_root_length: "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> length (path_to_root l x) > 0"
proof-
  assume "ufa_invar l" "x < length l"
  have "path_to_root_dom(l, x)" 
    using \<open>ufa_invar l\<close> \<open>x < length l\<close> path_to_root_domain ufa_invarD(1) by auto
  then show ?thesis
    apply(induction rule: path_to_root.pinduct)
    by (simp add: path_to_root.psimps)
qed

text \<open>If the representative changes after a list update, then it must be equal to 
      the representative of the updated element.\<close>
lemma rep_of_fun_upd3:
  assumes "ufa_invar l" "x < length l" "y < length l""x' < length l" "y' < length l"
    "rep_of l x = rep_of l y" "rep_of (CONST list_update l x' y') x \<noteq> rep_of (CONST list_update l x' y') y"
    "rep_of l y = rep_of (CONST list_update l x' y') y"  "rep_of l x' \<noteq> rep_of l y'"
  shows "rep_of (CONST list_update l x' y') x = rep_of (CONST list_update l x' y') y'"
  using assms proof(induction rule: rep_of_induct)
  case (base i)
  then have "i = x'" 
    by (metis nth_list_update' rep_of_refl)
  from base have "ufa_invar (l[x' := y'])" 
    by (simp add: ufa_invar_fun_upd2)
  with base show ?case 
    by (metis \<open>i = x'\<close> rep_of_fun_upd2 rep_of_refl)
next
  case (step i)
  then show ?case proof(cases "rep_of (l[x' := y']) (l ! i) = rep_of (l[x' := y']) y")
    case True
    with step have "i = x'" 
      by (metis length_list_update nth_list_update_neq rep_of_idx ufa_invar_fun_upd2)
    from step have "ufa_invar (l[x' := y'])" 
      using ufa_invar_fun_upd2 by presburger
    then show ?thesis 
      by (metis \<open>i = x'\<close> length_list_update nth_list_update_eq rep_of_idx step.prems(2))
  next
    case False
    with step have "rep_of (l[x' := y']) (l ! i) = rep_of (l[x' := y']) y'"
      using rep_of_idx by presburger
    with step show ?thesis 
      by (metis length_list_update nth_list_update_eq nth_list_update_neq rep_of_idx ufa_invar_fun_upd2)
  qed
qed

lemma rep_of_add_edge_aux:
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "i < length l"
    and "rep_of l x \<noteq> rep_of l y"
  shows "rep_of (add_edge l x y) i = (if rep_of l i = rep_of l x then rep_of l y else rep_of l i)"
proof-
  from assms have dom: "add_edge_dom (l, x, y)" 
    by (simp add: add_edge_domain)
  with assms have "ufa_invar (add_edge l x y)" 
    by (simp add: add_edge_ufa_invar_invar)
  from dom assms show ?thesis 
  proof(induction rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then have add_edge: "add_edge pf e e' = pf[e := e']" 
        by (simp add: "1.hyps" add_edge.psimps)
      have "rep_of pf e = e" 
        by (simp add: True rep_of_refl)
      then show ?thesis proof(cases "rep_of pf i = e")
        case True
        then show ?thesis 
          using "1.prems" add_edge \<open>rep_of pf e = e\<close> rep_of_fun_upd2 by auto
      next
        case False
        with rep_of_fun_upd' show ?thesis 
          using "1.prems" \<open>rep_of pf e = e\<close> add_edge by force
      qed
    next
      case False
      then have add_edge: "add_edge pf e e' = add_edge (pf[e := e']) (pf ! e) e"
        by (simp add: "1.hyps" add_edge.psimps)
      from False add_edge_correctness "1.prems" 
      have inverted_p: "path (add_edge pf e e') e' ([e'] @ rev (path_to_root pf e)) (rep_of pf e)" 
        by auto
      have invar: "ufa_invar (pf[e := e'])" 
        by (simp add: "1.prems" ufa_invar_fun_upd2)
      have "add_edge pf e e' ! e = e'" 
        by (simp add: "1.prems" nth_add_edge_e_eq_e')
      with "1.prems" have "hd (tl ([e'] @ rev (path_to_root pf e))) = e" 
        by (metis empty_append_eq_id hd_rev list.sel(3) path_last path_to_root_correct snoc_eq_iff_butlast' tl_append2)
      with path_to_root_length "1.prems" have length_path: "length ([e'] @ rev (path_to_root pf e)) > 1 "
        by simp
      with "1.prems" have "([e'] @ rev (path_to_root pf e)) ! 1 = e"
        by (metis \<open>hd (tl ([e'] @ rev (path_to_root pf e))) = e\<close> hd_tl_list)             
      have "ufa_invar (add_edge pf e e')" 
        using 1 add_edge_ufa_invar_invar by auto
      with nodes_path_rep_of inverted_p length_path have "rep_of (add_edge pf e e') e = rep_of (add_edge pf e e') e'"
        using \<open>([e'] @ rev (path_to_root pf e)) ! 1 = e\<close> by fastforce
      from rep_of_fun_upd "1.prems" have rep_of_parent: "rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)" 
        by (metis False path_remove_child path_to_root_correct ufa_invarD(2))
      with "1.prems" have  "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        by (metis invar length_list_update nth_list_update_eq rep_of_fun_upd' rep_of_idx)
      with 1(2)[OF False invar] 1 have IH: "rep_of (add_edge (pf[e := e']) (pf ! e) e) i =
    (if rep_of (pf[e := e']) i = rep_of (pf[e := e']) (pf ! e) then rep_of (pf[e := e']) e
     else rep_of (pf[e := e']) i)" 
        by (metis length_list_update ufa_invarD(2))     
      then show ?thesis 
      proof(cases "rep_of pf i = rep_of pf e")
        case True
        then show ?thesis proof(cases "rep_of (pf[e := e']) i = rep_of (pf[e := e']) (pf ! e)")
          case True
          with "1.prems" show ?thesis 
            by (metis IH add_edge invar length_list_update nth_list_update_eq rep_of_fun_upd' rep_of_idx rep_of_parent)
        next
          case False
          with True rep_of_fun_upd3 "1.prems" have *: "rep_of (pf[e := e']) i = rep_of (pf[e := e']) e" 
            by (metis \<open>rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e\<close> rep_of_parent rep_of_step ufa_invarD(2))
          with "1.prems" have "rep_of (pf[e := e']) e = rep_of (pf[e := e']) e'" 
            by (metis False rep_of_fun_upd3 rep_of_idx rep_of_parent ufa_invarD(2))
          then show ?thesis 
            using "1.prems" IH True * add_edge rep_of_fun_upd' by presburger
        qed   
      next
        case False
        then show ?thesis 
          using "1.prems" add_edge IH rep_of_parent rep_of_fun_upd' rep_of_idx by presburger
      qed
    qed
  qed
qed
lemma rep_of_add_edge_invar: 
  assumes "rep_of l a = rep_of l b" "rep_of l x1 \<noteq> rep_of l x2"
    "ufa_invar l" "a < length l" "b < length l ""x1 < length l ""x2 < length l"
  shows "rep_of (add_edge l x1 x2) a = rep_of (add_edge l x1 x2) b"
proof-
  from assms have dom: "add_edge_dom (l, x1, x2)" 
    by (simp add: add_edge_domain)
  from dom assms show ?thesis 
  proof(induction rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then have "add_edge pf e e' = pf[e := e']" 
        by (simp add: "1.hyps" add_edge.psimps)
      then show ?thesis 
        by (metis "1.prems" rep_of_add_edge_aux)
    next
      case False
      then show ?thesis 
        by (simp add: "1.prems" rep_of_add_edge_aux)
    qed
  qed
qed

lemma add_edge_inv3_invar:  
  assumes  "pf_l_same_eq_classes pf l" "ufa_invar pf" "ufa_invar l"
    "a < length pf" "b < length pf" "a < length l" "b < length l"
    "rep_of l a \<noteq> rep_of l b"
  shows "pf_l_same_eq_classes (add_edge pf a b) (ufa_union l a b)"
proof(standard, standard, standard, standard)
  fix i j 
  assume i_j: "i < length (add_edge pf a b)" "j < length (add_edge pf a b)"
  from assms have "add_edge_dom (pf, a, b)" 
    using add_edge_domain by auto
  then have "length (add_edge pf a b) = length pf" 
    by (simp add: add_edge_preserves_length)
  show "(rep_of (ufa_union l a b) i = rep_of (ufa_union l a b) j) =
           (rep_of (add_edge pf a b) i = rep_of (add_edge pf a b) j)" 
  proof (cases "rep_of l i = rep_of l j")
    case True
    with assms i_j show ?thesis 
      by (metis (no_types, lifting) \<open>length (add_edge pf a b) = length pf\<close> rep_of_add_edge rep_of_ufa_union)
  next
    case False
    from rep_of_ufa_union[OF assms(3,6,7)] rep_of_add_edge[OF assms(2,4,5)] assms i_j show ?thesis 
      sorry
      by (metis (no_types, lifting) \<open>length (add_edge pf a b) = length pf\<close>)
qed


lemma propagate_preserves_length_proof_forest:
  assumes "propagate_dom (a, cc)" "length (proof_forest cc) = n" "length (cc_list cc) = n" "proof_forest_invar cc"
    "pending_invar a (proof_forest cc) n" "inv3 cc"
  shows "length (proof_forest (propagate a cc)) = n"
  using assms proof(induction a cc rule: propagate.pinduct)
  case (1 cc)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 pe xs l u t pf pfl ip) 
  define a where "a = left pe"
  define b where "b = right pe"
  from 2 have *: "length pf = n" "ufa_invar pf" 
    unfolding congruence_closure.select_convs proof_forest_invar_def by auto
  from 2 a_def b_def pending_left_right_valid have a_b: "a < n" "b < n"  
    by auto
  show ?case proof(cases "rep_of l a = rep_of l b")
    case True
    then have "propagate (pe # xs)
         \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
  = propagate xs \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" using a_def b_def propagate_simps
      by (metis "2.hyps" propagate_simp2')
    moreover have "pending_invar xs
     (proof_forest \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) n"
      using "2.prems"(3) pending_invar_Cons by blast
    ultimately show ?thesis using 2 True a_def b_def by metis
next
  case False
  with 2 have "rep_of pf a \<noteq> rep_of pf b" 
    by (metis "*"(1) a_b(1) a_b(2) inv3_divided)
  with add_edge_domain a_b * have dom: "add_edge_dom (pf, a, b)"
    by metis
  with 2 add_edge_preserves_length * have "length (add_edge pf a b) = n"
    by presburger
  from * a_b dom add_edge_ufa_invar_invar have "ufa_invar (add_edge pf a b)" 
    by (simp add: \<open>rep_of pf a \<noteq> rep_of pf b\<close>)
  have " pending_invar (xs @ map (link_to_lookup t) (filter (lookup_Some t) (u ! rep_of l a))) (add_edge pf a b)
     n "sorry
  have "propagate (pe # xs)
         \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
              = propagate (xs @ (map (link_to_lookup t) (filter (lookup_Some t) (u ! rep_of l a))))
              \<lparr>cc_list = ufa_union l a b, 
              use_list = (u[rep_of l a := []])[rep_of l b := (u ! rep_of l b) @ (filter (lookup_None t) (u ! rep_of l a))], 
              lookup = set_lookup t (filter (lookup_None t) (u ! rep_of l a)) l,
              proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a pe, input = ip\<rparr>" 
    using "2.hyps" False a_def b_def propagate_simp3 by blast
  with False 2 propagate_simps show ?thesis unfolding a_def b_def 
  proof_forest_invar_def inv3_def
congruence_closure.select_convs  sorry
qed

  
qed

lemma propagate_preserves_length_pf_labels:
  assumes "propagate_dom (a, cc)" "length (pf_labels cc) = n" "ufa_invar (proof_forest cc)"
  shows "length (pf_labels (propagate a cc)) = n"
  using assms proof(induction rule: propagate.pinduct)
  case (1 cc)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 pe xs l u t pf pfl ip)
  define a where "a = left pe"
  have "a < length pf" sorry
  then have "add_label_dom (pfl, pf, a, pe)"
    sorry
  with 2 add_label_preserves_length a_def propagate.psimps(2) show ?case 
    by (smt (verit) congruence_closure.select_convs(5) )
qed


lemma rep_of_ufa_union:
  assumes  "ufa_invar l" "a < length l" "b < length l"
  shows"rep_of l k = rep_of l a \<Longrightarrow> rep_of (ufa_union l a b) k = rep_of l b" 
"rep_of l k = rep_of l b \<Longrightarrow> rep_of (ufa_union l a b) k = rep_of l b" 
"rep_of l k \<noteq> rep_of l a \<Longrightarrow> rep_of l k \<noteq> rep_of l b \<Longrightarrow> rep_of (ufa_union l a b) k = rep_of l k" 
  sorry

lemma rep_of_add_edge:
  assumes "ufa_invar pf" "a < length pf" "b < length pf"
  shows  "rep_of pf k = rep_of pf a \<Longrightarrow> rep_of (add_edge pf a b) k = rep_of pf b" 
"rep_of pf k = rep_of pf b \<Longrightarrow> rep_of (add_edge pf a b) k = rep_of pf b"
"rep_of pf k \<noteq> rep_of pf a \<Longrightarrow> rep_of l k \<noteq> rep_of l b \<Longrightarrow> rep_of (add_edge pf a b) k = rep_of pf k"
  sorry

end