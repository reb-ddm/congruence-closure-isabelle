section \<open>Explain for Congruence Closure\<close>
theory CC_Explain
  imports CC_Correctness
begin 

subsection \<open>Explain definition\<close>

text \<open>The \<open>"highest node"\<close> is in this case the same as the \<open>rep_of\<close>, because we do not 
      have the optimisation of checking which equivalence class is bigger, 
      we just make the union in the given order. When adding this optimisation,
      a \<open>highest_node\<close> function must be also implemented.\<close>

text \<open>There are three variables changed by the function \<open>explain_along_path\<close>: 

    * The overall output of explain
    * The Union Find list of the additional union find, which is local to the explain function
    * The list of pending proofs, which need to be recursively called with \<open>cc_explain\<close>
      
      These are the three values returned by this function.\<close>

function (domintros) explain_along_path :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    (equation set * nat list * (nat * nat) list)"
  where 
    "explain_along_path cc l a c = 
(if rep_of l a = rep_of l c 
then
  ({}, l, [])
else
  (let b = (proof_forest cc) ! rep_of l a in 
    (
    case the ((pf_labels cc) ! rep_of l a) of 
        One a' \<Rightarrow>  
          (let (output, new_l, pending) = explain_along_path cc (l[rep_of l a := b]) b c
          in ({a'} \<union> output, new_l, pending))
        | Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b') \<Rightarrow> 
          (let (output, new_l, pending) = explain_along_path cc (l[rep_of l a := b]) b c
          in ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, new_l, [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pending))
    )
  )
)"
  by pat_completeness auto

lemma explain_along_path_simp1:
  assumes "rep_of l a = rep_of l c"
  shows "explain_along_path cc l a c = ({}, l, [])"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path.domintros by blast
  then show ?thesis using explain_along_path.psimps 
    by (simp add: assms)
qed

lemma explain_along_path_simp2:
  assumes "rep_of l a \<noteq> rep_of l c"
    "(pf_labels cc) ! rep_of l a = Some (One a')"
    "(output, new_l, pend) = explain_along_path cc (l[rep_of l a := ((proof_forest cc) ! rep_of l a)]) 
     ((proof_forest cc) ! rep_of l a) c"
    "explain_along_path_dom (cc, l, a, c)"
  shows "explain_along_path cc l a c = ({a'} \<union> output, new_l, pend)"
  using explain_along_path.psimps unfolding Let_def
  by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(5))

lemma explain_along_path_simp3:
  assumes "rep_of l a \<noteq> rep_of l c"
    "(pf_labels cc) ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))"
    "explain_along_path cc (l[rep_of l a := ((proof_forest cc) ! rep_of l a)]) 
     ((proof_forest cc) ! rep_of l a) c = (output, new_l, pend)"
    "explain_along_path_dom (cc, l, a, c)"
  shows "explain_along_path cc l a c = ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, 
         new_l, [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend)"
  using explain_along_path.psimps unfolding Let_def
  by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(6) equation.simps(6))

function (domintros) cc_explain_aux :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> (nat * nat) list \<Rightarrow> equation set"
  where
    "cc_explain_aux cc l [] = {}"
  | "cc_explain_aux cc l ((a, b) # xs) =
(if are_congruent cc (a \<approx> b)
then
  (let c = lowest_common_ancestor (proof_forest cc) a b;
    (output1, new_l, pending1) = explain_along_path cc l a c;
    (output2, new_new_l, pending2) = explain_along_path cc new_l b c
  in
    output1 \<union> output2 \<union> cc_explain_aux cc new_new_l (xs @ pending1 @ pending2))
else cc_explain_aux cc l xs)"
  by pat_completeness auto

lemma cc_explain_aux_simp1:
  "cc_explain_aux cc l [] = {}" 
  using cc_explain_aux.domintros cc_explain_aux.psimps by blast

lemma cc_explain_aux_simp2:
  assumes "cc_explain_aux_dom (cc, l, ((a, b) # xs))"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "are_congruent cc (a \<approx> b)"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
  shows "cc_explain_aux cc l ((a, b) # xs) = 
output1 \<union> output2 \<union> cc_explain_aux cc new_new_l (xs @ pending1 @ pending2)" 
  using cc_explain_aux.domintros cc_explain_aux.psimps assms unfolding Let_def 
  by auto

lemma cc_explain_aux_simp3:
  assumes "cc_explain_aux_dom (cc, l, ((a, b) # xs))"
    "\<not> are_congruent cc (a \<approx> b)"
  shows "cc_explain_aux cc l ((a, b) # xs) = cc_explain_aux cc l xs" 
  using cc_explain_aux.domintros cc_explain_aux.psimps assms unfolding Let_def 
  by auto

abbreviation cc_explain :: "congruence_closure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> equation set"
  where
    "cc_explain cc a b \<equiv> cc_explain_aux cc [0..<nr_vars cc] [(a, b)]"

subsection \<open>Invariant for the additional union find in \<open>cc_explain\<close>\<close>

definition explain_list_invar :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "explain_list_invar l pf \<equiv> (\<forall> i < length l. l ! i \<noteq> i \<longrightarrow> l ! i = pf ! i) \<and> 
(length l = length pf) \<and> ufa_invar l"

lemma explain_list_invar_paths: 
  "path l a p b \<Longrightarrow> explain_list_invar l pf \<Longrightarrow> path pf a p b"
proof(induction rule: path.induct)
  case (single n l)
  then show ?case 
    by (simp add: explain_list_invar_def path.single)
next
  case (step r l u p v)
  then show ?case unfolding explain_list_invar_def 
    by (metis path.step path_nodes_lt_length_l)
qed

lemma explain_list_invar_initial:
  "explain_list_invar [0..<length pf] pf"
  unfolding explain_list_invar_def 
  using ufa_init_invar by simp

lemma explain_list_invar_union:
  assumes "explain_list_invar l pf" "a < length l" "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
    "pf ! rep_of l a < length l"
  shows "explain_list_invar (l[rep_of l a := (pf ! rep_of l a)]) pf"
  unfolding explain_list_invar_def 
proof(standard, standard, standard, standard)
  fix i
  assume prems: "i < length (l[rep_of l a := (pf ! rep_of l a)])"
    "(l[rep_of l a := (pf ! rep_of l a)]) ! i \<noteq> i"
  show "(l[rep_of l a := (pf ! rep_of l a)]) ! i = pf ! i"
  proof(cases "i = rep_of l a")
    case True
    have "rep_of l a < length l" 
      using True prems(1) by auto
    with True have "(l[rep_of l a := (pf ! rep_of l a)]) ! i = (pf ! rep_of l a)" 
      by simp
    then show ?thesis 
      by (simp add: True)
  next
    case False
    then show ?thesis using assms(1) prems unfolding explain_list_invar_def by simp
  qed
next 
  show "length (l[rep_of l a := (pf ! rep_of l a)]) = length pf 
\<and> ufa_invar (l[rep_of l a := pf ! rep_of l a]) " 
    using assms ufa_invar_fun_upd' rep_of_idem unfolding explain_list_invar_def by simp 
qed

lemma explain_list_invar_imp_valid_rep:
  assumes "explain_list_invar l pf" "ufa_invar pf"
    "path pf c p a"
    "rep_of l a \<noteq> rep_of l c"
  shows "pf ! rep_of l a \<noteq> rep_of l a \<and> 
        (path pf c ((take (length p - length (path_to_root l a) + 1) p)) (rep_of l a))"
proof-
  define pRA where "pRA = path_to_root l a" 
  then have pRA: "path l (rep_of l a) pRA a" 
    using assms unfolding explain_list_invar_def
    by (metis path_nodes_lt_length_l path_to_root_correct)
  then have pf_pRA: "path pf (rep_of l a) pRA a" 
    using assms(1) explain_list_invar_paths by blast
  then show ?thesis
  proof(cases "length pRA < length p" )
    case True
    let ?pCR = "(take (length p - length pRA) p)"
    let ?pRA' = "(drop (length p - length pRA) p)"
    have length_pRA': "length ?pRA' = length pRA" using True by simp
    have p_div: "?pCR @ ?pRA' = p" by simp
    have pRA'_neq_Nil: "?pRA' \<noteq> []" 
    proof
      assume "?pRA' = []" 
      then have "length p - length pRA \<ge> length p"
        by simp
      then have "length pRA = 0" 
        using length_pRA' by auto
      then show "False" using pf_pRA path_not_empty by blast
    qed
    then have paths: "path pf c (?pCR @ [hd ?pRA']) (hd ?pRA')"
      "path pf (hd ?pRA') ?pRA' a"
      using assms unfolding explain_list_invar_def
      using p_div assms(4) path_divide2 by metis+
    have "(?pCR @ [hd ?pRA']) = take (length p - length pRA + 1) p"
      by (metis pRA'_neq_Nil ab_semigroup_add_class.add.commute append_Nil2 append_eq_conv_conj diff_less_Suc less_SucE plus_1_eq_Suc take_hd_drop)
    then show ?thesis
      using assms pRA pRA_def paths unfolding explain_list_invar_def
      by (metis length_pRA' pRA path_rep_eq path_root path_unique_if_length_eq pf_pRA)
  next
    case False
      \<comment> \<open>Impossible, because rep_of l a \<noteq> rep_of l c\<close>
    let ?pRC = "(take (length pRA - length p) pRA)"
    let ?p' = "(drop (length pRA - length p) pRA)"
    have pra: "?pRC @ ?p' = pRA" by auto
    have p'_neq_Nil: "?p' \<noteq> []" 
    proof
      assume "drop (length pRA - length p) pRA = []"
      then have "(length pRA - length p) \<ge> length pRA" 
        by force
      then have "length p = 0" 
        using False by linarith
      then show "False" using path_not_empty assms unfolding explain_list_invar_def by auto
    qed
    with False have paths: "path pf (rep_of l a) (?pRC @ [hd ?p']) (hd ?p')"
      "path pf (hd ?p') ?p' a"
      using path_divide2 pf_pRA pra by metis+
    from False have "length pRA \<ge> length p" 
      by simp
    with False have "length ?p' = length p" 
      by (metis diff_diff_cancel length_drop)
    then have hd_p': "(hd ?p') = c" 
      using assms paths path_unique_if_length_eq by blast
    then have "?p' = p" 
      using assms paths assms(3) assms(4) path_unique by blast
    then have "rep_of l c = rep_of l a" 
      using assms unfolding explain_list_invar_def
      by (metis p'_neq_Nil hd_p' pRA path_divide2 path_rep_eq pra)
    then have "False" 
      using assms unfolding explain_list_invar_def by auto
    then show ?thesis by simp
  qed
qed

lemma rep_of_a_and_parent_rep_neq:
  assumes 
    "explain_list_invar l pf" "ufa_invar pf"
    "pf ! rep_of l a \<noteq> rep_of l a \<and> path pf c pRAC (rep_of l a)" 
  shows "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
proof
  assume "rep_of l a = rep_of l (pf ! rep_of l a)"
  then obtain pt where"path l (rep_of l a) pt (pf ! rep_of l a)"
    by (metis assms explain_list_invar_def path_nodes_lt_length_l path_to_root_correct ufa_invarD(2))
  then have p1: "path pf (rep_of l a) pt (pf ! rep_of l a)" 
    using assms explain_list_invar_paths by blast
  have p2: "path pf (pf ! rep_of l a) [(pf ! rep_of l a),(rep_of l a)] (rep_of l a)" 
    by (meson \<open>path pf (rep_of l a) pt (pf ! rep_of l a)\<close> assms path.simps ufa_invarD(2))
  from p1 p2 assms show "False" 
    by (metis list.set_intros(1) path.cases path_remove_child)
qed

theorem explain_list_invar_explain_along_path:
  assumes 
    "explain_along_path_dom (\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>, l, a, c)"
    "explain_list_invar l pf" "a < length l" "ufa_invar pf"
    "path pf c p a"
    "pf_labels_invar \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "explain_list_invar (
        fst (snd (explain_along_path \<lparr>cc_list = cc_l, use_list = u, lookup = t, 
        pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> l a c))) pf"
  using assms proof(induction "\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    l a c arbitrary: p rule: explain_along_path.pinduct)
  case (1 l a c)
  then show ?case proof(cases "rep_of l a = rep_of l c")
    case True
    then show ?thesis 
      by (simp add: "1.prems"(1) explain_along_path_simp1)
  next
    case False
    let ?cc = "\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>"
    let ?union = "(l[rep_of l a := (pf ! rep_of l a)])"
    from "1.prems" have invar: "ufa_invar l" "length l = length pf"
      unfolding explain_list_invar_def by blast+
    from False obtain output' new_l' pend' where recursive_step: "explain_along_path ?cc
     ?union (pf ! rep_of l a) c = (output', new_l', pend')"
      using prod_cases3 by blast
    obtain pRAC where pRAC: "pf ! rep_of l a \<noteq> rep_of l a \<and> path pf c pRAC (rep_of l a)" 
      using "1.prems" False assms(2) explain_list_invar_imp_valid_rep by blast
    from "1.prems" have "path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)"
      by (metis rep_of_bound rep_of_idem single invar(1))
    with "1.prems" have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)" 
      by (metis False pRAC path_butlast rep_of_idem invar(1))
    obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
(pfl ! rep_of l a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! rep_of l a \<and> bb = rep_of l a \<or> aa = rep_of l a \<and> bb = pf ! rep_of l a)
        "using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
      by (meson pRAC path_nodes_lt_length_l)
    from "1.prems" have explain_list_invar: "explain_list_invar (l[rep_of l a := pf ! rep_of l a]) pf" 
      by (metis invar(2) explain_list_invar_union pRAC pRAC' path_nodes_lt_length_l rep_of_a_and_parent_rep_neq)
    have rep_neq: "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
      using pRAC "1.prems" False rep_of_a_and_parent_rep_neq invar by blast
    then have valid: "(pf ! rep_of l a) < length pf" 
      using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar invar
      by (metis rep_of_bound)
    show ?thesis proof(cases "the (pfl ! rep_of l a)")
      case (One a')
      from valid_eq have *: "pfl ! rep_of l a = Some (One a')" 
        using One by auto
      with recursive_step 1(2)[OF False] have IH: 
        "explain_list_invar new_l' pf" 
        using "1.prems" One valid explain_list_invar pRAC' invar by force
      then have "explain_list_invar new_l' pf" 
        by (simp add: recursive_step)
      moreover have result: "explain_along_path ?cc l a c = ({a'} \<union> output', new_l', pend')" 
        using 1 explain_along_path_simp2[OF False] One False * recursive_step by simp
      then show ?thesis 
        using IH recursive_step by auto
    next
      case (Two x21 x22)
      then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where *: "(pfl ! rep_of l a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
        by (metis option.sel pending_equation.distinct(1) valid_eq) 
      with recursive_step 1(3)[OF False] have IH: 
        "explain_list_invar new_l' pf" 
        using * pRAC' "1.prems" 
        by (simp add: invar explain_list_invar valid(1))
      have result: "explain_along_path ?cc l a c = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', new_l', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
        using False congruence_closure.select_convs * recursive_step 1(1,8) explain_along_path_simp3
        by auto
      then show ?thesis 
        using IH recursive_step by auto
    qed
  qed
qed

subsection \<open>Termination of \<open>explain_along_path\<close>\<close>

theorem explain_along_path_domain:
  assumes "cc_invar cc" 
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
  shows "explain_along_path_dom (cc, l, a, c)" 
  using assms proof(induction "length p" arbitrary: p l a rule: less_induct)
  case less
  then show ?case proof(cases "length p > 1")
    case False
    then have "c = a" 
      by (metis hd_Nil_eq_last hd_path last_ConsL last_path length_0_conv less.prems(3) less_one linorder_neqE_nat list.sel(1) list_decomp_1)
    then show ?thesis using explain_along_path.domintros by blast
  next
    case True
    then show ?thesis proof(cases "rep_of l a = rep_of l c")
      case True
      then show ?thesis using explain_along_path.domintros by blast
    next
      case False 
      then obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
      let ?union = "(l[rep_of l a := (pf ! rep_of l a)])"
      have invar: "ufa_invar pf"
        using "less.prems" unfolding proof_forest_invar_def cc congruence_closure.select_convs by blast
      define pRAC where "pRAC = take (length p - length (path_to_root l a) + 1) p"
      then have pRAC: "pf ! rep_of l a \<noteq> rep_of l a \<and> path pf c pRAC (rep_of l a)"
        using "less.prems" False explain_list_invar_imp_valid_rep invar unfolding cc congruence_closure.select_convs
        by blast
      have "length pRAC \<le> length p" using pRAC_def by simp
      then have length: "length (butlast pRAC) < length p" using True by fastforce
      have path_rep: "path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)"
        using "less.prems" unfolding cc congruence_closure.select_convs
        using explain_list_invar_def pRAC path_length_1 path_nodes_lt_length_l rep_of_idem by auto
      then have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)" 
        using "less.prems" unfolding cc congruence_closure.select_convs
        by (metis False pRAC path_butlast path_length_1)
      from "less.prems" invar have explain_list_invar: 
        "explain_list_invar (l[rep_of l a := pf ! rep_of l a]) (proof_forest cc)" 
        unfolding cc congruence_closure.select_convs 
        by (metis (no_types, lifting) explain_list_invar_def explain_list_invar_union pRAC pRAC' path_nodes_lt_length_l rep_of_a_and_parent_rep_neq)
      with less(1,2) length pRAC' cc have recursive_dom:
        "explain_along_path_dom (cc, (l[rep_of l a := (pf ! rep_of l a)]), (pf ! rep_of l a), c)"
        by fastforce
      show ?thesis using cc recursive_dom explain_along_path.domintros
        by (metis congruence_closure.select_convs(5))
    qed
  qed
qed


subsection \<open>Termination of \<open>cc_explain\<close>\<close>

text \<open>The number of equivalence classes does not increase with \<open>explain_along_path\<close>\<close>

lemma list_upd_eq_classes:
  assumes "a \<noteq> b" "l ! a = a" "a < length l"
  shows "nr_eq_classes (l[a := b]) < nr_eq_classes l" 
proof-
  have *: "i \<noteq> a \<Longrightarrow> i \<in> root_set l \<longleftrightarrow> i \<in> root_set (l[a := b])" for i 
    by force
  have **: "finite (root_set l)" 
    by simp
  from assms have "a \<in> root_set l"  "a \<notin> root_set (l[a := b])"
    by auto
  with * assms have "root_set (l[a := b]) \<subset> root_set l" by blast
  with ** show ?thesis 
    unfolding nr_eq_classes_def 
    by (meson psubset_card_mono)
qed

lemma explain_along_path_eq_classes':
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "rep_of l a \<noteq> rep_of l c"
  shows "nr_eq_classes (fst (snd (explain_along_path cc l a c))) < nr_eq_classes l"
proof-
  have "explain_along_path_dom (cc, l, a, c)" 
    using assms explain_along_path_domain by simp
  then show ?thesis
    using assms proof(induction arbitrary: p rule: explain_along_path.pinduct)
    case (1 cc l a c)
    then have invar: "ufa_invar l" "length l = length (proof_forest cc)"
      unfolding explain_list_invar_def by blast+ 
    then show ?case                
    proof(cases "rep_of l a = rep_of l c")
      case False
      then obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
      let ?union = "(l[rep_of l a := (pf ! rep_of l a)])"
      from False obtain output' new_l' pend' where recursive_step: "explain_along_path cc
     ?union (pf ! rep_of l a) c = (output', new_l', pend')"
        using prod_cases3 by blast
      have invar: "ufa_invar pf"
        using "1.prems" unfolding proof_forest_invar_def cc congruence_closure.select_convs by blast
      then obtain pRAC where pRAC: "pf ! rep_of l a \<noteq> rep_of l a \<and> path pf c pRAC (rep_of l a)" 
        using "1.prems" False explain_list_invar_imp_valid_rep unfolding cc congruence_closure.select_convs
        by blast
      have path_rep: "path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)"
        using "1.prems" unfolding cc congruence_closure.select_convs
        using explain_list_invar_def pRAC path_length_1 path_nodes_lt_length_l rep_of_idem by auto
      then have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)" 
        using "1.prems" unfolding cc congruence_closure.select_convs
        by (metis False pRAC path_butlast path_length_1)
      obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
          (pfl ! rep_of l a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! rep_of l a \<and> bb = rep_of l a \<or> aa = rep_of l a \<and> bb = pf ! rep_of l a)"
        using "1.prems" unfolding cc pf_labels_invar_def congruence_closure.select_convs
        by (meson pRAC path_nodes_lt_length_l)
      from "1.prems" invar have explain_list_invar: 
        "explain_list_invar (l[rep_of l a := pf ! rep_of l a]) (proof_forest cc)" 
        unfolding cc congruence_closure.select_convs 
        by (metis (no_types, lifting) explain_list_invar_def explain_list_invar_union pRAC pRAC' path_nodes_lt_length_l rep_of_a_and_parent_rep_neq)
      have rep_neq: "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
        using pRAC "1.prems" False rep_of_a_and_parent_rep_neq unfolding cc congruence_closure.select_convs 
        using invar by blast
      then have valid: "(pf ! rep_of l a) < length pf" "ufa_invar (l[rep_of l a := (pf ! rep_of l a)])"
        using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar unfolding cc congruence_closure.select_convs 
        using pRAC' apply blast using ufa_invar_fun_upd' "1.prems" unfolding cc congruence_closure.select_convs 
        using path_rep explain_list_invar_def pRAC' path_length_1 path_nodes_lt_length_l rep_neq by auto
      have "rep_of l a \<noteq> (proof_forest cc) ! (rep_of l a)" using cc pRAC by auto
      then have step: "nr_eq_classes (l[rep_of l a := (proof_forest cc) ! (rep_of l a)]) < nr_eq_classes l" 
        using list_upd_eq_classes 
        by (metis (no_types, lifting) "1.prems"(2) "1.prems"(3) explain_list_invar_def path_nodes_lt_length_l rep_of_bound rep_of_min)
      show ?thesis proof(cases "the (pfl ! rep_of l a)")
        case (One a')
        from valid_eq have *: "pfl ! rep_of l a = Some (One a')" 
          using One by auto
        have result: "explain_along_path cc l a c = ({a'} \<union> output', new_l', pend')" 
          using 1 explain_along_path_simp2[OF False] One False * recursive_step cc by simp 
        have "pf ! rep_of l a \<noteq> rep_of l a" "rep_of l a < length l"
          using pRAC path_rep path_nodes_lt_length_l by blast+
        have "(fst (snd (explain_along_path cc (l[rep_of l a := pf ! rep_of l a]) (pf ! rep_of l a) c))) = new_l'"
          by (simp add: recursive_step)
        with recursive_step cc pRAC'
        have *: "rep_of ?union (pf ! rep_of l a) \<noteq> rep_of ?union c \<Longrightarrow>
nr_eq_classes new_l' < nr_eq_classes ?union" 
          using 1(2)[OF False _ _ 1(4) explain_list_invar] False One "1.prems" valid 
          by (metis congruence_closure.select_convs(5) congruence_closure.select_convs(6))
        have "rep_of ?union (pf ! rep_of l a) = rep_of ?union c \<Longrightarrow>
 new_l'= ?union" using explain_along_path.psimps 
          using explain_along_path_simp1 recursive_step by force
        with cc result step * show ?thesis 
          using order_less_trans by auto
      next
        case (Two x21 x22)
        then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where *: "(pfl ! rep_of l a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
          by (metis option.sel pending_equation.distinct(1) valid_eq) 
        have result: "explain_along_path cc l a c = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', new_l', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
          using False  * recursive_step 1 explain_along_path_simp3
          unfolding cc congruence_closure.select_convs by simp
        then have a': "a' = rep_of l a \<and> b' = pf ! rep_of l a
\<or> a' = pf ! rep_of l a \<and> b' = rep_of l a" 
          using valid_eq * by auto
        have "pf ! rep_of l a \<noteq> rep_of l a" 
          by (simp add: pRAC)
        have "(fst (snd (explain_along_path cc (l[rep_of l a := pf ! rep_of l a]) (pf ! rep_of l a) c))) = new_l'"
          by (simp add: recursive_step)
        with recursive_step cc pRAC'
        have *: "rep_of ?union (pf ! rep_of l a) \<noteq> rep_of ?union c \<Longrightarrow>
nr_eq_classes new_l' < nr_eq_classes ?union" 
          using 1(3)[OF False _ _ _ _ 1(4) explain_list_invar] False Two "1.prems" valid *
          unfolding cc congruence_closure.select_convs 
          by simp
        have "rep_of ?union (pf ! rep_of l a) = rep_of ?union c \<Longrightarrow>
 new_l'= ?union" using explain_along_path.psimps 
          using explain_along_path_simp1 recursive_step by force
        with cc result step * show ?thesis using order_less_trans by auto
      qed
    qed (simp add: "1.prems")
  qed
qed

lemma explain_along_path_eq_classes:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
  shows "nr_eq_classes (fst (snd (explain_along_path cc l a c))) \<le> nr_eq_classes l"
proof-
  have "explain_along_path_dom (cc, l, a, c)" 
    using assms explain_along_path_domain by simp
  then show ?thesis
    using assms proof(induction arbitrary: p rule: explain_along_path.pinduct)
    case (1 cc l a c)
    then show ?case using explain_along_path_eq_classes' explain_along_path_simp1 
      by (metis Orderings.order_eq_iff fst_conv order.strict_implies_order snd_conv)
  qed
qed

text \<open>If the pending list is not empty after \<open>explain_along_path\<close>, then
the number of equivalence classes must have increased. \<close>

lemma explain_along_path_eq_classes_if_pending_not_empty:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "snd (snd (explain_along_path cc l a c)) \<noteq> []"
  shows "nr_eq_classes (fst (snd (explain_along_path cc l a c))) < nr_eq_classes l"
proof-
  have "explain_along_path_dom (cc, l, a, c)" 
    using assms explain_along_path_domain by simp
  then show ?thesis
    using assms proof(induction arbitrary: p rule: explain_along_path.pinduct)
    case (1 cc l a c)
    show ?case 
    proof(cases "rep_of l a = rep_of l c")
      case False
      then show ?thesis using explain_along_path_eq_classes' 1 
        by blast
    next
      case True
      then have "snd (snd (explain_along_path cc l a c)) = []" 
        using explain_along_path_simp1 by simp
      then show ?thesis 
        by (simp add: "1.prems"(4))
    qed 
  qed
qed

lemma explain_along_path_pending_in_bounds:
  assumes "cc_invar cc" 
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
  shows "\<forall> (k, j) \<in> set (snd (snd (explain_along_path cc l a c))).
k < nr_vars cc \<and> j < nr_vars cc"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path_domain by simp
  then show ?thesis
    using assms proof(induction arbitrary: p rule: explain_along_path.pinduct)
    case (1 cc l a c)
    then have invar: "ufa_invar l" "length l = length (proof_forest cc)"
      unfolding explain_list_invar_def by blast+ 
    then show ?case 
    proof(cases "rep_of l a = rep_of l c")
      case False
      then obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
      let ?union = "(l[rep_of l a := (pf ! rep_of l a)])"
      from False obtain output' new_l' pend' where recursive_step: "explain_along_path cc
     ?union (pf ! rep_of l a) c = (output', new_l', pend')"
        using prod_cases3 by blast
      have invar: "ufa_invar pf"
        using "1.prems" unfolding proof_forest_invar_def cc congruence_closure.select_convs by blast
      then obtain pRAC where pRAC: "pf ! rep_of l a \<noteq> rep_of l a \<and> path pf c pRAC (rep_of l a)" 
        using "1.prems" False explain_list_invar_imp_valid_rep unfolding cc congruence_closure.select_convs
        by blast
      have "path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)"
        using "1.prems" unfolding cc congruence_closure.select_convs
        using explain_list_invar_def pRAC path_length_1 path_nodes_lt_length_l rep_of_idem by auto
      then have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)" 
        using "1.prems" unfolding cc congruence_closure.select_convs
        by (metis False pRAC path_butlast path_length_1)
      obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
(pfl ! rep_of l a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! rep_of l a \<and> bb = rep_of l a \<or> aa = rep_of l a \<and> bb = pf ! rep_of l a)
        "using "1.prems" unfolding cc pf_labels_invar_def congruence_closure.select_convs
        by (meson pRAC path_nodes_lt_length_l)
      from "1.prems" invar have explain_list_invar: "explain_list_invar (l[rep_of l a := pf ! rep_of l a]) (proof_forest cc)" 
        unfolding cc congruence_closure.select_convs 
        by (metis (no_types, lifting) explain_list_invar_def explain_list_invar_union pRAC pRAC' path_nodes_lt_length_l rep_of_a_and_parent_rep_neq)
      have rep_neq: "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
        using pRAC "1.prems" False rep_of_a_and_parent_rep_neq unfolding cc congruence_closure.select_convs 
        using invar by blast
      then have valid: "(pf ! rep_of l a) < length pf" "ufa_invar (l[rep_of l a := (pf ! rep_of l a)])"
        using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar unfolding cc congruence_closure.select_convs 
        using pRAC' apply blast      using ufa_invar_fun_upd' "1.prems" unfolding cc congruence_closure.select_convs 
        using \<open>path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)\<close> explain_list_invar_def pRAC' path_length_1 path_nodes_lt_length_l rep_neq by auto
      show ?thesis proof(cases "the (pfl ! rep_of l a)")
        case (One a')
        from valid_eq have *: "pfl ! rep_of l a = Some (One a')" 
          using One by auto
        have result: "explain_along_path cc l a c = ({a'} \<union> output', new_l', pend')" 
          using 1 explain_along_path_simp2[OF False] One False * recursive_step cc by simp 
        have "pf ! rep_of l a \<noteq> rep_of l a" 
          by (simp add: pRAC)
        from 1(2)[OF False] One "1.prems" recursive_step cc explain_list_invar pRAC' valid have 
          " \<forall>a\<in>set (snd (snd (explain_along_path cc (l[rep_of l a := pf ! rep_of l a]) (pf ! rep_of l a) c))).
       case a of (k, j) \<Rightarrow> k < nr_vars cc \<and> j < nr_vars cc" 
          by simp
        with cc result show ?thesis 
          using recursive_step by auto
      next
        case (Two x21 x22)
        then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where *: "(pfl ! rep_of l a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
          by (metis option.sel pending_equation.distinct(1) valid_eq) 
        have result: "explain_along_path cc l a c = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', new_l', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
          using False  * recursive_step 1 explain_along_path_simp3
          unfolding cc congruence_closure.select_convs by simp
        then have a': "a' = rep_of l a \<and> b' = pf ! rep_of l a
\<or> a' = pf ! rep_of l a \<and> b' = rep_of l a" 
          using valid_eq * by auto
        have "pf ! rep_of l a \<noteq> rep_of l a" 
          by (simp add: pRAC)
        from * Two "1.prems" explain_list_invar pRAC
        have "valid_vars_pending (the (pfl ! rep_of l a)) cc_l"
          unfolding pf_labels_invar_def cc congruence_closure.select_convs 
          by (metis path_nodes_lt_length_l)
        with Two * have new_valid: "a\<^sub>1 < length cc_l" "a\<^sub>2 < length cc_l" "b\<^sub>1 < length cc_l" "b\<^sub>2 < length cc_l"  
          by auto
        from 1(3)[OF False] Two * "1.prems" recursive_step cc explain_list_invar pRAC' valid have 
          "\<forall>a\<in>set (snd (snd (explain_along_path cc (l[rep_of l a := pf ! rep_of l a]) (pf ! rep_of l a) c))).
       case a of (k, j) \<Rightarrow> k < nr_vars cc \<and> j < nr_vars cc" 
          unfolding cc congruence_closure.select_convs by simp
        with result cc recursive_step new_valid show ?thesis
          by auto
      qed
    qed (simp add: explain_along_path_simp1)
  qed
qed 

theorem cc_explain_aux_domain:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
  shows "cc_explain_aux_dom (cc, l, xs)"
  using assms proof(induction "nr_eq_classes l" arbitrary: l xs rule: less_induct)
  case less
  show ?case using less(2-) less(1) proof(induction xs arbitrary: l)
    \<comment> \<open>There is an induction 1 on the number of equivalence classes 
and an induction 2 on the length of xs.\<close>
    case Nil
      \<comment> \<open>If xs is empty, the function terminates immediately\<close>
    then show ?case using cc_explain_aux.domintros 
      by blast
  next
    case (Cons k xs')
      \<comment> \<open>We define the variables the same was as in \<open>cc_explain_aux\<close>\<close>
    obtain a b c output1 new_l pending1 output2 new_new_l pending2 where 
      defs: "(a, b) = k" 
      "c = lowest_common_ancestor (proof_forest cc) a b"
      "(output1, new_l, pending1) = explain_along_path cc l a c"
      "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
      by (metis surj_pair)

    have **: "\<forall>a\<in>set xs'. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc" 
      using Cons by simp
    then show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case False
        \<comment> \<open>Second case of the function: the recursive call terminates by induction hypothesis 2\<close>
      have "cc_explain_aux_dom (cc, l, xs')" 
        using Cons(1)[OF Cons(2,3)] ** Cons.prems(4) by blast
      then show ?thesis using cc_explain_aux.domintros defs(1) False by blast
    next
      case True2: True

\<comment> \<open>First case of the function: we do a case distinction on whether the call to 
\<open>explain_along_path\<close> added equations to pending.

If it did add equations to pending, then the union-find was definitely updated, 
therefore the number of equivalence classes decreased. We can use induction hypothesis 1.

If not then then we can use induction hypothesis 2.\<close>

\<comment> \<open>These calculations are just needed to show that \<open>explain_list_invar\<close> is invariant\<close>
      then obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
      then have *: "rep_of cc_l a = rep_of cc_l b" 
        using True2 by auto
      have valid: "a < length cc_l" "b < length cc_l" "length cc_l = length pf" using Cons.prems(3) cc 
          defs(1) apply auto[2] using Cons.prems unfolding inv_same_length_def cc by auto
      then have "rep_of pf a = rep_of pf b" using "less.prems" cc *  
        unfolding inv_same_rep_classes_def cc congruence_closure.select_convs by simp
      then have invar: "ufa_invar pf" 
        using "less.prems" cc unfolding proof_forest_invar_def by simp
      then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b" 
        using lowest_common_ancestor_correct invar valid defs
        by (metis \<open>rep_of pf a = rep_of pf b\<close> cc congruence_closure.select_convs(5))
      have dom1: "explain_along_path_dom (cc, l, a, c)" 
        using "Cons.prems" explain_along_path_domain p by blast
      have lengths: "length l = length cc_l" 
        "length l = length pf" "ufa_invar pf" using "Cons.prems" 
        unfolding inv_same_length_def explain_list_invar_def proof_forest_invar_def cc congruence_closure.select_convs 
        by argo+
      with explain_list_invar_explain_along_path
      have new_l_inv: "explain_list_invar new_l (proof_forest cc)"
        using dom1 Cons.prems valid p unfolding cc proof_forest_invar_def congruence_closure.select_convs
        using cc defs by (metis fst_eqD snd_eqD)
      then have dom2: "explain_along_path_dom (cc, new_l, b, c)"
        using "less.prems"(1) explain_along_path_domain p(2) cc by auto
      from new_l_inv have lengths2: "length l = length new_l" unfolding explain_list_invar_def 
        using lengths(2) cc by simp
      then have new_new_l_inv: "explain_list_invar new_new_l (proof_forest cc)" 
        using explain_list_invar_explain_along_path dom1 dom2 p cc new_l_inv valid "less.prems" lengths lengths2 defs
        by (metis congruence_closure.select_convs(5) fst_eqD snd_eqD)
      have 1: "\<forall>a\<in>set xs'. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
        using less.prems(3) Cons by auto
      have "pending1 = snd(snd(explain_along_path cc l a c))" unfolding defs(3)[symmetric] by simp
      then have 3: "\<forall>a\<in>set pending1. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
        using Cons.prems dom1 p(1) explain_along_path_pending_in_bounds cong case_prodD by blast
      have "pending2 = snd(snd(explain_along_path cc new_l b c))" unfolding defs(4)[symmetric] by simp
      then have 4: "\<forall>a\<in>set pending2. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
        using "less.prems" dom1 p(1) defs explain_along_path_pending_in_bounds[OF "less.prems"(1,2) p(2)] cong 
        using explain_along_path_pending_in_bounds new_l_inv p(2) by auto
      have *: "new_l = fst (snd (explain_along_path cc l a c))"
        "new_new_l = fst (snd (explain_along_path cc new_l b c))" 
        using defs(3,4)[symmetric] by auto

\<comment> \<open>Now we can do the case distinction and use the two lemmas \<open>explain_along_path_eq_classes\<close>
and \<open>explain_along_path_eq_classes_if_pending_not_empty\<close>\<close>
      have new_eq_classes': "nr_eq_classes new_l \<le> nr_eq_classes l" 
        using explain_along_path_eq_classes Cons.prems(2) less.prems(1) p(1) * by blast
      with * have new_eq_classes: "nr_eq_classes new_new_l \<le> nr_eq_classes new_l" 
        using explain_along_path_eq_classes less.prems(1) new_l_inv p(2) by blast

      then show ?thesis proof(cases "pending1 @ pending2 = []")
        case True
        then have domain: "cc_explain_aux_dom (cc, new_new_l, xs')" 
          using new_eq_classes Cons(1)[OF Cons(2) new_new_l_inv  ** ] Cons.prems(4) dual_order.trans new_eq_classes'
          by simp
        from True2 True have "xs' @ pending1 @ pending2 = xs'" by blast
        then show ?thesis using cc_explain_aux.domintros defs True2 domain
          by (metis Pair_inject lowest_common_ancestor.simps)

      next
        case False
        then have cong: "are_congruent cc (a \<approx> b)" using defs Cons True2 by auto
        have **: "pending1 = snd (snd (explain_along_path cc l a c))"
          "pending2 = snd (snd (explain_along_path cc new_l b c))" 
          using defs(3,4)[symmetric] by auto
        have pending_neq_Nil: "pending1 \<noteq> [] \<or> pending2 \<noteq> []" 
          using False by blast

        then have "nr_eq_classes new_l < nr_eq_classes l \<or> nr_eq_classes new_new_l < nr_eq_classes new_l"
          apply(standard) 
          using explain_along_path_eq_classes_if_pending_not_empty * ** Cons.prems(2) less.prems(1) p(1) apply blast
          using explain_along_path_eq_classes_if_pending_not_empty less.prems(1) new_l_inv p(2) * ** by blast
        then have eq_classes: "nr_eq_classes new_new_l < nr_eq_classes l" 
          by (meson dual_order.strict_trans1 dual_order.strict_trans2 new_eq_classes new_eq_classes')

        have "\<forall>a\<in>set (xs' @ pending1 @ pending2). case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc" 
          using 1 3 4 by fastforce
        then have "\<forall>(a, b)\<in>set (xs' @ pending1 @ pending2). a < nr_vars cc \<and> b < nr_vars cc" 
          by blast
        with less(1) eq_classes Cons.prems(1) new_new_l_inv cc
        have "cc_explain_aux_dom (cc, new_new_l, (xs' @ pending1 @ pending2))" 
          using Cons.prems(4) by blast
        then show ?thesis using cc_explain_aux.domintros defs False cong 
          by (metis Pair_inject lowest_common_ancestor.simps)
      qed
    qed
  qed
qed

subsection \<open>Invariants for the validity of \<open>explain\<close>\<close>

text \<open>We introduce new invariant of the \<open>congruence_closure\<close> in order to prove the correctness
and validity of explain.\<close> 

text \<open>These invars simply state that all the equations in the proof forest, the lookup table, 
the use list and the pending list are in input.\<close>

fun pending_eq_in_set :: "pending_equation \<Rightarrow> equation set \<Rightarrow> bool"
  where
    "pending_eq_in_set (One a) ip = (a \<in> ip)"
  | "pending_eq_in_set (Two a b) ip = (a \<in> ip \<and> b \<in> ip)"

abbreviation pf_labels_validity_invar :: "pending_equation option list \<Rightarrow> equation set \<Rightarrow> bool"
  where
    "pf_labels_validity_invar pfl ip \<equiv> (\<forall> eq \<in> set pfl . 
    eq \<noteq> None \<longrightarrow> pending_eq_in_set (the eq) ip)"

abbreviation lookup_validity_invar :: "equation option list list \<Rightarrow> equation set \<Rightarrow> bool"
  where
    "lookup_validity_invar t ip \<equiv> (\<forall> row \<in> set t . ( \<forall> eq \<in> set row.
    eq \<noteq> None \<longrightarrow> (the eq) \<in> ip
  )
)"

abbreviation use_list_validity_invar :: "equation list list \<Rightarrow> equation set \<Rightarrow> bool"
  where
    "use_list_validity_invar u ip \<equiv> (\<forall> row \<in> set u . ( \<forall> eq \<in> set row.
    eq \<in> ip
  )
)"

abbreviation pending_validity_invar :: "pending_equation list \<Rightarrow> equation set \<Rightarrow> bool"
  where
    "pending_validity_invar pe ip \<equiv> (\<forall> eq \<in> set pe.
    pending_eq_in_set eq ip)"

definition validity_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "validity_invar cc \<equiv> ((pf_labels_validity_invar (pf_labels cc) (input cc)
      \<and> lookup_validity_invar (lookup cc) (input cc)) 
      \<and> use_list_validity_invar (use_list cc) (input cc))
      \<and> pending_validity_invar (pending cc) (input cc)"


subsection \<open>Invariant proof\<close>

subsubsection \<open>The invariants remain invariant after the loop of propagate\<close>

lemma validity_invar_loop:
  assumes "validity_invar cc" "rep_b < length l" "inv_same_length cc (nr_vars cc)"
    "quadratic_table (lookup cc)" "\<forall> eq \<in> set u_a . eq \<in> (input cc)"
    "(\<forall> j < length u_a . use_list_valid_element (u_a ! j) (cc_list cc) rep_b)"
    "cc_list_invar cc"
  shows "validity_invar (propagate_loop rep_b u_a cc)" 
  using assms proof(induction rep_b u_a cc rule: propagate_loop.induct)
  case (1 rep_b u1 urest l u t pe pf pfl ip)
  let ?loop1 = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = link_to_lookup t l u1 # pe,
              proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    and ?loop2 = "\<lparr>cc_list = l, use_list = u[rep_b := u1 # u ! rep_b], lookup = update_lookup t l u1,
              pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  have u1_in_ip: "u1 \<in> ip" 
    using "1.prems"(5,6) by fastforce
  from 1 have *: "\<forall>j<length urest. use_list_valid_element (urest ! j) l rep_b"
    by auto
  from "1.prems" obtain a\<^sub>1 a\<^sub>2 aa where u1': "u1 = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l" "rep_of l a\<^sub>1 = rep_b \<or> rep_of l a\<^sub>2 = rep_b"
    unfolding congruence_closure.select_convs
    by (metis in_set_conv_nth list.set_intros(1))
  show ?case
  proof(cases "lookup_Some t l u1")
    case True
    with u1' obtain eq where "lookup_entry t l a\<^sub>1 a\<^sub>2 = Some eq"
      by fastforce
    have "rep_of l a\<^sub>1 < length t" "rep_of l a\<^sub>2 < length (t ! rep_of l a\<^sub>2)"
      using "1.prems" unfolding cc_list_invar_def congruence_closure.select_convs  
      by (simp add: inv_same_length_def rep_of_bound u1'(2,3))+
    from "1.prems" have "eq \<in> ip" unfolding validity_invar_def congruence_closure.select_convs 
      unfolding cc_list_invar_def congruence_closure.select_convs inv_same_length_def
      by (metis (no_types, lifting) \<open>lookup_entry t l a\<^sub>1 a\<^sub>2 = Some eq\<close> \<open>rep_of l a\<^sub>1 < length t\<close> nth_mem option.distinct(1) option.sel rep_of_bound u1'(3))
    have "pending_eq_in_set (link_to_lookup t l u1) ip" 
      using \<open>eq \<in> ip\<close> \<open>lookup_entry t l a\<^sub>1 a\<^sub>2 = Some eq\<close> u1'(1) u1_in_ip by fastforce
    with "1.prems" have v: "validity_invar ?loop1" 
      unfolding validity_invar_def by simp
    with "1.prems" have i: "inv_same_length ?loop1 (nr_vars ?loop1)" 
      unfolding inv_same_length_def by simp
    then show ?thesis 
      using 1 True "*" i v cc_list_invar_def by auto
  next
    case False
    from "1.prems" u1_in_ip have use_list: "use_list_validity_invar (use_list ?loop2) (input ?loop2)" 
      unfolding validity_invar_def congruence_closure.select_convs 
      by (metis in_set_upd_cases list.inject list.set_cases nth_mem)
    from "1.prems"(1) u1_in_ip have "lookup_validity_invar (lookup ?loop2) (input ?loop2)"
      unfolding validity_invar_def congruence_closure.select_convs u1' update_lookup.simps
      by (metis in_set_upd_cases nth_mem option.sel)
    with "1.prems" use_list have v: "validity_invar ?loop2" 
      unfolding validity_invar_def by simp
    with "1.prems" have i: "inv_same_length ?loop2 (nr_vars ?loop2)" 
      unfolding inv_same_length_def congruence_closure.select_convs 
      by (simp add: update_lookup_preserves_length)
    have "quadratic_table (lookup ?loop2)" 
      using "1.prems" unfolding congruence_closure.select_convs u1' update_lookup.simps
      by (simp add: nth_list_update')
    then show ?thesis 
      using 1 False i v cc_list_invar_def * by auto
  qed
qed simp

subsubsection \<open>The invariant remains invariant after propagate\<close>

paragraph \<open>Invariant before entering the \<open>propagate_loop\<close>\<close>

lemma pf_labels_validity_invar_add_label:
  assumes "ufa_invar pf" "a < length pf" "length pf = length pfl"
    "pf_labels_validity_invar pfl ip" "pending_eq_in_set eq ip"
    "(\<forall> n < length pf. pf ! n \<noteq> n \<longrightarrow> pfl ! n \<noteq> None)"
  shows "pf_labels_validity_invar (add_label pfl pf a eq) ip"
proof-
  have dom: "add_label_dom (pfl, pf, a, eq)" 
    by (simp add: add_label_domain assms(1) assms(2))
  show  "pf_labels_validity_invar (add_label pfl pf a eq) ip"
    using dom assms proof(induction rule: add_label.pinduct)
    case (1 pfl pf e lbl)
    then show ?case proof(cases "pf ! e = e")
      case True
      with 1 show ?thesis 
        by (metis add_label.psimps in_set_upd_cases option.collapse option.inject)
    next
      case False
      have "pfl ! e \<noteq> None" "e < length pfl" 
        using "1.prems"(2,3,6) False by auto
      then have new_lbl: "pending_eq_in_set (the (pfl ! e)) ip" 
        using "1.prems"(4) nth_mem by blast
      have "\<forall>n<length pf. pf ! n \<noteq> n \<longrightarrow> pfl[e := Some lbl] ! n \<noteq> None" 
        by (metis "1.prems"(6) \<open>e < length pfl\<close> nth_list_update option.distinct(1))
      with 1 new_lbl show ?thesis 
        by (metis add_label.psimps in_set_upd_eq length_list_update option.sel ufa_invarD(2))
    qed
  qed
qed

lemma validity_invar_mini_step:
  assumes "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" (is "validity_invar ?base")  
    "inv_same_length \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr> (length l)"
    "quadratic_table t" "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l"  "rep_of l a \<noteq> rep_of l b" "a = left eq" "b = right eq"
    "ufa_invar pf" "a < length l" "b < length l"
    "inv_same_rep_classes \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "pf_labels_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
  shows "validity_invar \<lparr>cc_list = ufa_union l a b,
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>" (is "validity_invar ?step")
  unfolding validity_invar_def
proof(rule conjI)+
  have 1: "\<forall>n<length pf. pf ! n \<noteq> n \<longrightarrow> pfl ! n \<noteq> None" 
    using assms unfolding pf_labels_invar_def by auto
  have 2: "pending_eq_in_set eq ip" 
    using assms unfolding validity_invar_def by force
  have "length l = length pf" "length l = length pfl" 
    using assms unfolding inv_same_length_def by auto
  then show "pf_labels_validity_invar (pf_labels ?step) (input ?step)"
    using 1 2 assms pf_labels_validity_invar_add_label 
    unfolding validity_invar_def congruence_closure.select_convs by presburger
  show "lookup_validity_invar (lookup ?step) (input ?step)" 
    using assms unfolding validity_invar_def congruence_closure.select_convs by linarith
  show "use_list_validity_invar (use_list ?step) (input ?step)" 
    using assms unfolding validity_invar_def congruence_closure.select_convs 
    by (metis in_set_conv_nth length_list_update list.discI list.set_cases nth_list_update_eq nth_list_update_neq nth_mem)
  show "pending_validity_invar (pending ?step) (input ?step)" 
    using assms unfolding validity_invar_def congruence_closure.select_convs 
    by fastforce
qed

paragraph \<open>Invariant after one step of propagate\<close>

lemma validity_invar_step:
  assumes "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "inv_same_length \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr> (length l)"
    "quadratic_table t" "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l"  "rep_of l a \<noteq> rep_of l b" "a = left eq" "b = right eq"
    "ufa_invar pf" "a < length l" "b < length l"
    "inv_same_rep_classes \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "pf_labels_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
  shows "validity_invar (propagate_step l u t pe pf pfl ip a b eq)"
proof-
  let ?mini_step = "\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
  have 1: "validity_invar ?mini_step" 
    using validity_invar_mini_step assms by blast
  have 2: "rep_of l b < length (ufa_union l a b)" 
    by (simp add: assms(5,11) rep_of_bound)
  have 3: "inv_same_length ?mini_step (nr_vars ?mini_step)"
    using inv_same_length_mini_step assms by auto
  have 4: "rep_of l a < length u" 
    using assms rep_of_less_length_l unfolding inv_same_length_def by auto
  then have 5: "\<forall>eq\<in>set (u ! rep_of l a). eq \<in> input ?mini_step" using assms unfolding validity_invar_def 
    by auto
  have 6: "\<forall>j<length (u ! rep_of l a).
       \<exists>b\<^sub>1 b\<^sub>2 bb.
          (u ! rep_of l a) ! j = (F b\<^sub>1 b\<^sub>2 \<approx> bb) \<and>
          (rep_of l b = rep_of (cc_list ?mini_step) b\<^sub>1 \<or> rep_of l b = rep_of (cc_list ?mini_step) b\<^sub>2) \<and>
          b\<^sub>1 < nr_vars ?mini_step \<and> b\<^sub>2 < nr_vars ?mini_step \<and> bb < nr_vars ?mini_step"
    using use_list_invar_impl_valid_input_propagate_loop assms unfolding congruence_closure.select_convs 
    by blast
  have "cc_list_invar ?mini_step" unfolding cc_list_invar_def 
    by (simp add: assms(10) assms(11) assms(5) ufa_union_invar)
  with validity_invar_loop[OF 1] show ?thesis 
    using 2 3 4 5 6 assms(3) unfolding congruence_closure.select_convs by blast
qed

subsubsection \<open>Invariant after propagate\<close>

lemma validity_invar_propagate: 
  assumes "propagate_dom cc" "cc_invar cc" "validity_invar cc"
  shows "validity_invar (propagate cc)"
  using assms proof(induction cc rule: propagate.pinduct)
  case (2 l u t eq pe pf pfl ip)
  then show ?case 
  proof(cases "rep_of l (left eq) = rep_of l (right eq)")
    case True
    let ?step = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    have "pending_validity_invar (pending ?step) (input ?step)" using 2 unfolding validity_invar_def 
      by (metis congruence_closure.select_convs(4,7) list.set_intros(2))
    then have "validity_invar ?step"
      using "2.prems" True unfolding validity_invar_def by simp
    then show ?thesis using 2
      by (metis True cc_invar_step2 propagate_simps2)
  next
    case False
    let ?step = "(propagate_step l u t pe pf pfl ip (left eq) (right eq) eq)"
    have invar: "ufa_invar l" using "2.prems" unfolding cc_list_invar_def by simp
    have left_right: "left eq < length l" "right eq < length l" 
      using "2.prems" pending_left_right_valid by auto
    have "cc_invar ?step"
      using "2.prems" cc_invar_step invar left_right False by blast
    have "validity_invar ?step"
      using validity_invar_step "2.prems" invar left_right False 
      unfolding lookup_invar_def proof_forest_invar_def by simp
    then show ?thesis using 2(3)
      by (simp add: "2.hyps" False \<open>cc_invar ?step\<close>)
  qed            
qed simp

subsubsection \<open>Invariant after merge\<close>

lemma validity_invar_merge1:
  assumes "valid_vars (a \<approx> b)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>" 
    (is "validity_invar ?base")
  shows "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
      proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"
    (is "validity_invar ?step")
  unfolding validity_invar_def
proof(rule conjI)+
  show "pf_labels_validity_invar (pf_labels ?step) (input ?step)"
    using assms unfolding validity_invar_def 
    by (metis congruence_closure.select_convs(6,7) insert_iff pending_eq_in_set.simps(1) pending_eq_in_set.simps(2) pending_equation.exhaust)
  show "lookup_validity_invar (lookup ?step) (input ?step)"
    using assms unfolding validity_invar_def by auto
  show "use_list_validity_invar (use_list ?step) (input ?step)"
    using assms unfolding validity_invar_def by auto
  show "pending_validity_invar (pending ?step) (input ?step)"
  proof
    fix eq
    assume prems: "eq \<in> set (pending ?step)"
    show "pending_eq_in_set eq (input ?step)"
    proof(cases "eq = One (a \<approx> b)")
      case True
      then show ?thesis 
        by simp
    next
      case False
      then have "eq \<in> set pe" using prems 
        by simp
      then have "pending_eq_in_set eq ip"using assms prems unfolding validity_invar_def 
        by auto
      then show ?thesis 
        by (metis congruence_closure.select_convs(7) insertCI pending_eq_in_set.simps(1) pending_eq_in_set.simps(2) pending_equation.exhaust)
    qed
  qed
qed

lemma validity_invar_merge2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
    "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
  shows "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, 
            pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "validity_invar ?step")
  unfolding validity_invar_def
proof(rule conjI)+
  show "pf_labels_validity_invar (pf_labels ?step) (input ?step)"
    using assms unfolding validity_invar_def 
    by (metis congruence_closure.select_convs(6,7) insert_iff pending_eq_in_set.simps(1) pending_eq_in_set.simps(2) pending_equation.exhaust)
  show "lookup_validity_invar (lookup ?step) (input ?step)"
    using assms unfolding validity_invar_def by auto
  show "use_list_validity_invar (use_list ?step) (input ?step)"
    using assms unfolding validity_invar_def by auto
  show "pending_validity_invar (pending ?step) (input ?step)"
  proof
    fix eq
    assume prems: "eq \<in> set (pending ?step)"
    show "pending_eq_in_set eq (input ?step)"
    proof(cases "eq = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)")
      case True
      from assms have entry_not_none: "(lookup_entry t l a\<^sub>1 a\<^sub>2) \<noteq> None" 
        by (metis is_none_simps(1) lookup_Some.simps(1))
      have valid: "l ! rep_of l a\<^sub>1 = rep_of l a\<^sub>1 \<and> l ! rep_of l a\<^sub>2 = rep_of l a\<^sub>2"
        "rep_of l a\<^sub>1 < length l \<and> rep_of l a\<^sub>2 < length l"
        "length l = length t" "length l = length (t ! rep_of l a\<^sub>1)"
        using assms rep_of_min rep_of_less_length_l unfolding cc_list_invar_def inv_same_length_def lookup_invar_def 
        by auto 
      with entry_not_none have "(the (lookup_entry t l a\<^sub>1 a\<^sub>2)) \<in> input ?step" using assms unfolding validity_invar_def 
        by (metis congruence_closure.select_convs(3,7) insertI2 nth_mem)
      then show ?thesis 
        using True by auto
    next
      case False
      then have "eq \<in> set pe" using prems 
        by simp
      then have "pending_eq_in_set eq ip"using assms prems unfolding validity_invar_def 
        by auto
      then show ?thesis 
        by (metis congruence_closure.select_convs(7) insertCI pending_eq_in_set.simps(1) pending_eq_in_set.simps(2) pending_equation.exhaust)
    qed
  qed
qed

lemma validity_invar_merge3:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "\<not> lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "validity_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "validity_invar ?step")
  unfolding validity_invar_def
proof(rule conjI)+
  show "pf_labels_validity_invar (pf_labels ?step) (input ?step)"
    using assms unfolding validity_invar_def 
    by (metis congruence_closure.select_convs(6,7) insert_iff pending_eq_in_set.simps(1) pending_eq_in_set.simps(2) pending_equation.exhaust)
  show "lookup_validity_invar (lookup ?step) (input ?step)"
  proof(standard, standard, standard)
    fix row eq
    assume prems: "row \<in> set (lookup ?step)" "eq \<in> set row" "eq \<noteq> None"
    show "the eq \<in> input ?step"
    proof(cases "eq = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)")
      case True
      then show ?thesis 
        by simp
    next
      case False
      then show ?thesis proof(cases "row \<in> set (lookup ?base)")
        case True
        then show ?thesis using assms unfolding validity_invar_def 
          by (metis \<open>eq \<in> set row\<close> \<open>eq \<noteq> None\<close> congruence_closure.select_convs(7) insertCI)
      next
        case False': False
        have valid: "rep_of l a\<^sub>1 < length t"
          using assms rep_of_less_length_l unfolding cc_list_invar_def inv_same_length_def by simp
        have "row = (lookup ?step) ! rep_of l a\<^sub>1"  
          using False' prems unfolding update_lookup.simps congruence_closure.select_convs 
          by (metis (no_types, opaque_lifting) in_set_conv_nth nth_list_update_neq update_lookup.simps(1) update_lookup_preserves_length)
        with valid have "row = (t ! rep_of l a\<^sub>1)[rep_of l a\<^sub>2 := Some (F a\<^sub>1 a\<^sub>2 \<approx> a)]"
          using prems unfolding update_lookup.simps congruence_closure.select_convs 
          by simp
        with False prems have *: "eq \<in> set (t ! rep_of l a\<^sub>1)" 
          by (meson in_set_upd_cases)
        have "(t ! rep_of l a\<^sub>1) \<in> set t" 
          by (simp add: valid)
        then show ?thesis 
          using assms prems * unfolding validity_invar_def by simp
      qed
    qed 
  qed
  show "use_list_validity_invar (use_list ?step) (input ?step)"
    using assms unfolding validity_invar_def congruence_closure.select_convs 
    by (smt (verit, ccfv_threshold) in_set_upd_cases insertI1 insertI2 length_list_update list.inject list.set_cases nth_mem)
  show "pending_validity_invar (pending ?step) (input ?step)"
    using assms unfolding validity_invar_def congruence_closure.select_convs 
    by (metis insert_iff pending_eq_in_set.simps(1) pending_eq_in_set.simps(2) pending_equation.exhaust)
qed

theorem validity_invar_merge: 
  assumes "cc_invar cc" "validity_invar cc" "valid_vars eq (nr_vars cc)" 
  shows "validity_invar (merge cc eq)"
  using assms proof(induction cc eq rule: merge.induct)
  case (1 l u t pe pf pfl ip a b)
  then have cc_invar: "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
      proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>" 
    using cc_invar_merge1 by blast
  then have "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
      proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>" 
    using validity_invar_merge1 "1.prems" by blast
  with 1 propagate_domain' show ?case 
    using merge.simps(1) validity_invar_propagate cc_invar 
    by (metis congruence_closure.select_convs(1))
next
  case (2 l u t pe pf pfl ip a\<^sub>1 a\<^sub>2 a)
  then show ?case 
  proof(cases "lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)")
    case True
    then have cc_invar: "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf,
            pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      using cc_invar_merge2 "2.prems" by blast
    then have "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t,
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf,
            pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      using validity_invar_merge2 "2.prems" True by blast
    with True cc_invar 2 propagate_domain' show ?thesis 
      using merge.simps(2) validity_invar_propagate by (metis congruence_closure.select_convs(1))
  next
    case False
    then have "cc_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      using cc_invar_merge3 "2.prems" by blast
    then have "validity_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      using validity_invar_merge3 "2.prems" False by blast
    with False show ?thesis 
      by simp
  qed
qed

subsubsection \<open>Initial cc\<close>

theorem validity_invar_initial_cc: "validity_invar (initial_cc n)"
  unfolding validity_invar_def
  by fastforce

subsection \<open>Validity of \<open>cc_explain\<close>\<close>

lemma explain_along_path_valid:
  assumes "cc_invar cc" "validity_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
  shows "fst (explain_along_path cc l a c) \<subseteq> input cc"
proof-
  have "explain_along_path_dom (cc, l, a, c)" 
    using assms explain_along_path_domain by simp
  then show ?thesis
    using assms proof(induction arbitrary: p rule: explain_along_path.pinduct)
    case (1 cc l a c)
    then have invar: "ufa_invar l" "length l = length (proof_forest cc)"
      unfolding explain_list_invar_def by blast+ 
    then show ?case 
    proof(cases "rep_of l a = rep_of l c")
      case False
      then obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
      let ?union = "(l[rep_of l a := (pf ! rep_of l a)])"
      from False obtain output' new_l' pend' where recursive_step: "explain_along_path cc
     ?union (pf ! rep_of l a) c = (output', new_l', pend')"
        using prod_cases3 by blast
      have invar: "ufa_invar pf"
        using "1.prems" unfolding proof_forest_invar_def cc congruence_closure.select_convs by blast
      then obtain pRAC where pRAC: "pf ! rep_of l a \<noteq> rep_of l a \<and> path pf c pRAC (rep_of l a)" 
        using "1.prems" False explain_list_invar_imp_valid_rep unfolding cc congruence_closure.select_convs
        by blast
      have path_rep: "path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)"
        using "1.prems" unfolding cc congruence_closure.select_convs
        using explain_list_invar_def pRAC path_length_1 path_nodes_lt_length_l rep_of_idem by auto
      then have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)" 
        using "1.prems" unfolding cc congruence_closure.select_convs
        by (metis False pRAC path_butlast path_length_1)
      obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
          (pfl ! rep_of l a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! rep_of l a \<and> bb = rep_of l a \<or> aa = rep_of l a \<and> bb = pf ! rep_of l a)"
        using "1.prems" unfolding cc pf_labels_invar_def congruence_closure.select_convs
        by (meson pRAC path_nodes_lt_length_l)
      from "1.prems" invar have explain_list_invar: 
        "explain_list_invar (l[rep_of l a := pf ! rep_of l a]) (proof_forest cc)" 
        unfolding cc congruence_closure.select_convs 
        by (metis (no_types, lifting) explain_list_invar_def explain_list_invar_union pRAC pRAC' path_nodes_lt_length_l rep_of_a_and_parent_rep_neq)
      have rep_neq: "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
        using pRAC "1.prems" False rep_of_a_and_parent_rep_neq unfolding cc congruence_closure.select_convs 
        using invar by blast
      then have valid: "(pf ! rep_of l a) < length pf" "ufa_invar (l[rep_of l a := (pf ! rep_of l a)])"
        using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar unfolding cc congruence_closure.select_convs 
        using pRAC' apply blast using ufa_invar_fun_upd' "1.prems" unfolding cc congruence_closure.select_convs 
        using path_rep explain_list_invar_def pRAC' path_length_1 path_nodes_lt_length_l rep_neq by auto
      show ?thesis proof(cases "the (pfl ! rep_of l a)")
        case (One a')
        from valid_eq have *: "pfl ! rep_of l a = Some (One a')" 
          using One by auto
        have result: "explain_along_path cc l a c = ({a'} \<union> output', new_l', pend')" 
          using 1 explain_along_path_simp2[OF False] One False * recursive_step cc by simp 
        have "pf ! rep_of l a \<noteq> rep_of l a" "rep_of l a < length l"
          using pRAC path_rep path_nodes_lt_length_l by blast+
        then have a': "a' \<in> ip" using "1.prems" 
          unfolding validity_invar_def cc congruence_closure.select_convs explain_list_invar_def inv_same_length_def using One valid_eq 
          by (metis nth_mem option.discI pending_eq_in_set.simps(1))
        from recursive_step cc explain_list_invar pRAC' have "output' \<subseteq> ip" 
          using 1(2) False One "1.prems" valid by auto
        with a' cc result show ?thesis 
          by auto
      next
        case (Two x21 x22)
        then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where *: "(pfl ! rep_of l a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
          by (metis option.sel pending_equation.distinct(1) valid_eq) 
        have result: "explain_along_path cc l a c = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', new_l', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
          using False  * recursive_step 1 explain_along_path_simp3
          unfolding cc congruence_closure.select_convs by simp
        then have a': "a' = rep_of l a \<and> b' = pf ! rep_of l a
\<or> a' = pf ! rep_of l a \<and> b' = rep_of l a" 
          using valid_eq * by auto
        have "pf ! rep_of l a \<noteq> rep_of l a" 
          by (simp add: pRAC)
        then have a'_b': "(F a\<^sub>1 a\<^sub>2 \<approx> a') \<in> ip" " (F b\<^sub>1 b\<^sub>2 \<approx> b') \<in> ip" 
          using "1.prems" unfolding validity_invar_def 
          by (metis "*" cc congruence_closure.select_convs(5) congruence_closure.select_convs(6) congruence_closure.select_convs(7) inv_same_length_def nth_mem option.collapse option.distinct(1) option.inject pRAC path_nodes_lt_length_l pending_eq_in_set.simps(2))+
        from 1(3)[OF False] * Two "1.prems" explain_list_invar valid pRAC' recursive_step
        have "output' \<subseteq> ip" 
          unfolding cc congruence_closure.select_convs by simp
        with a'_b' result cc show ?thesis 
          by simp
      qed
    qed (simp add: explain_along_path_simp1)
  qed
qed


lemma cc_explain_aux_valid:
  assumes "cc_explain_aux_dom (cc, l, xs)" "cc_invar cc" "validity_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
  shows "cc_explain_aux cc l xs \<subseteq> input cc"
  using assms proof(induction rule: cc_explain_aux.pinduct)
  case (2 cc l a b xs)
  then show ?case proof(cases "are_congruent cc (a \<approx> b)")
    case True
    obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
    then have *: "rep_of cc_l a = rep_of cc_l b" 
      using True by auto
    have valid: "a < length cc_l" "b < length cc_l" "length cc_l = length pf" using "2.prems" cc 
        apply auto[2] using "2.prems" unfolding inv_same_length_def cc by auto
    then have "rep_of pf a = rep_of pf b" using "2.prems" cc *  
      unfolding inv_same_rep_classes_def cc congruence_closure.select_convs by simp
    then have invar: "ufa_invar pf" 
      using "2.prems" cc unfolding proof_forest_invar_def by simp
    define c where "c = lowest_common_ancestor (proof_forest cc) a b"
    then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b" 
      using lowest_common_ancestor_correct invar valid
      by (metis \<open>rep_of pf a = rep_of pf b\<close> cc congruence_closure.select_convs(5))
    obtain output1 new_l pending1 where 
      rec1: "explain_along_path cc l a c = (output1, new_l, pending1)"
      using prod_cases3 by blast
    obtain output2 new_new_l pending2 where 
      rec2: "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
      using prod_cases3 by blast
    have dom1: "explain_along_path_dom (cc, l, a, c)" 
      using "2.prems" explain_along_path_domain p by blast
    have lengths: "length l = length cc_l" 
      "length l = length pf" "ufa_invar pf" using "2.prems" 
      unfolding inv_same_length_def explain_list_invar_def proof_forest_invar_def cc congruence_closure.select_convs 
      by argo+
    with explain_list_invar_explain_along_path
    have new_l_inv: "explain_list_invar new_l (proof_forest cc)"
      using dom1 "2.prems" valid p unfolding cc proof_forest_invar_def congruence_closure.select_convs
      using cc rec1 by (metis fst_eqD snd_eqD)
    then have dom2: "explain_along_path_dom (cc, new_l, b, c)"
      using "2.prems"(1) explain_along_path_domain p(2) cc by auto
    from new_l_inv have lengths2: "length l = length new_l" unfolding explain_list_invar_def 
      using lengths(2) cc by simp
    then have o: "output1 \<subseteq> ip" "output2 \<subseteq> ip" 
      using cc explain_along_path_valid "2.prems" p rec1 dom1 apply fastforce
      using cc explain_along_path_valid "2.prems" p rec2 dom2 new_l_inv 
      by (metis congruence_closure.select_convs(5,7) fst_conv fst_conv)
    then have new_new_l_inv: "explain_list_invar new_new_l pf" 
      using explain_list_invar_explain_along_path dom1 dom2 p cc new_l_inv valid "2.prems" lengths lengths2
      by (metis congruence_closure.select_convs(5) fst_eqD rec2 snd_eqD)
    have 1: "\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
      by (simp add: "2.prems"(4))
    have 3: "\<forall>a\<in>set pending1. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
      using "2.prems" dom1 p(1) rec1 explain_along_path_pending_in_bounds by auto
    have 4: "\<forall>a\<in>set pending2. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
      using p(2) rec2 explain_along_path_pending_in_bounds[OF "2.prems"(1) new_l_inv] by auto
    have "\<forall>a\<in>set (xs @ pending1 @ pending2). case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc" 
      using 1 3 4 by fastforce
    with 2(2)[OF True c_def] rec1 rec2 "2.prems" cc new_new_l_inv
    have IH: "cc_explain_aux cc new_new_l (xs @ pending1 @ pending2) \<subseteq> input cc"
      by simp
    have "cc_explain_aux cc l ((a, b) # xs) = 
          output1 \<union> output2 \<union> cc_explain_aux cc new_new_l (xs @ pending1 @ pending2)"
      using "2.hyps" True c_def cc_explain_aux_simp2 rec1 rec2 by auto
    then show ?thesis 
      using cc o IH by simp
  qed (simp add: cc_explain_aux.psimps 2)
qed (simp add: cc_explain_aux.psimps)

theorem cc_explain_valid:
  assumes "cc_invar cc" "validity_invar cc"
    "valid_vars (a \<approx> b) (nr_vars cc)"
  shows "cc_explain cc a b \<subseteq> input cc"
proof-
  have "length (proof_forest cc) = nr_vars cc" 
    using assms unfolding inv_same_length_def by blast
  then have **: "explain_list_invar [0..<nr_vars cc] (proof_forest cc)" 
    by (metis explain_list_invar_initial)
  have *: "\<forall> (a,b)\<in> set [(a, b)] . a < nr_vars cc \<and> b < nr_vars cc"
    using assms by simp
  have "cc_explain_aux_dom (cc, [0..<nr_vars cc], [(a, b)])" 
    using cc_explain_aux_domain assms ** by simp
  with cc_explain_aux_valid show ?thesis 
    using ** assms * by presburger
qed


end