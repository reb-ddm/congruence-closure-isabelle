theory CC_Explain2
  imports CC_Definition2
begin 

section \<open>Alternative definition of explain\<close>

text \<open>This version of explain is equivalent to the other one, without the optimization 
of the additional proof forest. We can prove, that it also terminates, and that it outputs 
the same equations as the original explain algorithm. \<close>

function (domintros) explain_along_path2 :: "congruence_closure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    (equation set * (nat * nat) list)"
  where 
    "explain_along_path2 cc a c = 
(if a = c 
then
  ({}, [])
else
  (let b = (proof_forest cc) ! a in 
    (
    case the ((pf_labels cc) ! a) of 
        One a' \<Rightarrow>  
          (let (output, pending) = explain_along_path2 cc b c
          in ({a'} \<union> output, pending))
        | Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b') \<Rightarrow> 
          (let (output, pending) = explain_along_path2 cc b c
          in ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pending))
    )
  )
)"
  by pat_completeness auto

lemma explain_along_path2_simp1:
  assumes "a = c"
  shows "explain_along_path2 cc a c = ({}, [])"
proof-
  have "explain_along_path2_dom (cc, a, c)"
    using assms explain_along_path2.domintros by blast
  then show ?thesis using explain_along_path2.psimps 
    by (simp add: assms)
qed

lemma explain_along_path2_simp2:
  assumes "a \<noteq> c"
    "(pf_labels cc) ! a = Some (One a')"
    "(output, pend) = explain_along_path2 cc ((proof_forest cc) ! a) c"
    "explain_along_path2_dom (cc, a, c)"
  shows "explain_along_path2 cc a c = ({a'} \<union> output, pend)"
  using explain_along_path2.psimps unfolding Let_def
  by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(5))

lemma explain_along_path2_simp3:
  assumes "a \<noteq> c"
    "(pf_labels cc) ! a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))"
    "explain_along_path2 cc ((proof_forest cc) ! a) c = (output, pend)"
    "explain_along_path2_dom (cc, a, c)"
  shows "explain_along_path2 cc a c = ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, 
     [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend)"
  using explain_along_path2.psimps unfolding Let_def
  by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(6) equation.simps(6))

function (domintros) cc_explain_aux2:: "congruence_closure \<Rightarrow> (nat * nat) list \<Rightarrow> equation set"
  where
    "cc_explain_aux2 cc [] = {}"
  | "cc_explain_aux2 cc ((a, b) # xs) =
(if are_congruent cc (a \<approx> b)
then
  (let c = lowest_common_ancestor (proof_forest cc) a b;
    (output1, pending1) = explain_along_path2 cc a c;
    (output2, pending2) = explain_along_path2 cc b c
  in
    output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs))
else cc_explain_aux2 cc xs)"
  by pat_completeness auto

lemma cc_explain_aux2_simp1:
  "cc_explain_aux2 cc [] = {}" 
  using cc_explain_aux2.domintros cc_explain_aux2.psimps by blast

lemma cc_explain_aux2_simp2:
  assumes "cc_explain_aux2_dom (cc, ((a, b) # xs))"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "are_congruent cc (a \<approx> b)"
    "(output1, pending1) = explain_along_path2 cc a c"
    "(output2, pending2) = explain_along_path2 cc b c"
  shows "cc_explain_aux2 cc ((a, b) # xs) = 
output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs)" 
  using cc_explain_aux2.domintros cc_explain_aux2.psimps assms unfolding Let_def 
  by auto

lemma cc_explain_aux2_simp3:
  assumes "cc_explain_aux2_dom (cc, ((a, b) # xs))"
    "\<not> are_congruent cc (a \<approx> b)"
  shows "cc_explain_aux2 cc ((a, b) # xs) = cc_explain_aux2 cc xs" 
  using cc_explain_aux2.domintros cc_explain_aux2.psimps assms unfolding Let_def 
  by auto

abbreviation cc_explain2 :: "congruence_closure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> equation set"
  where
    "cc_explain2 cc a b \<equiv> cc_explain_aux2 cc [(a, b)]"


subsection \<open>Termination proof of \<open>cc_explain2\<close>\<close>

subsubsection \<open>Termination of \<open>explain_along_path2\<close>\<close>

lemma explain_along_path2_domain:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
  shows "explain_along_path2_dom (cc, a, c)"
  using assms proof(induction "length p" arbitrary: p a rule: less_induct)
  case less
  then show ?case proof(cases "a = c")
    case True
    then show ?thesis using explain_along_path2.domintros by blast
  next
    case False
    then have "length p > 0" using less unfolding proof_forest_invar_def 
      by (simp add: path_not_empty)
    from False have "length p \<noteq> 1" using less unfolding proof_forest_invar_def 
      by (metis impossible_Cons length_greater_0_conv less_numeral_extra(3) nat_geq_1_eq_neqz path.cases path_length_1)
    then have "length p > 1" 
      using \<open>0 < length p\<close> nat_neq_iff by auto
    then obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
    have invar: "ufa_invar pf"
      using "less.prems" unfolding proof_forest_invar_def cc congruence_closure.select_convs by blast
    then have pRAC': "path pf c (butlast p) (pf ! a)" 
      using "less.prems" unfolding cc congruence_closure.select_convs
      by (metis False path_butlast)
    with less(1,2)  pRAC' cc have recursive_dom:
      "explain_along_path2_dom (cc, (pf ! a), c)" 
      by (metis \<open>0 < length p\<close> congruence_closure.select_convs(5) diff_less length_butlast less_numeral_extra(1))
    show ?thesis using cc recursive_dom explain_along_path2.domintros
      by (metis congruence_closure.select_convs(5))
  qed
qed

subsubsection \<open>Invariant which states, that the timestamps decrease during the execution of 
\<open>cc_explain\<close>\<close>

abbreviation timestamps_decrease_invar
  where 
"timestamps_decrease_invar ti pf pfl \<equiv> 
(\<forall> a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b k c\<^sub>1 c\<^sub>2 pa\<^sub>1 pa\<^sub>2 pb\<^sub>1 pb\<^sub>2 x
. k < length pf \<longrightarrow> pfl ! k = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))
\<longrightarrow> path pf c\<^sub>1 pa\<^sub>1 a\<^sub>1 \<longrightarrow> path pf c\<^sub>1 pb\<^sub>1 b\<^sub>1 \<longrightarrow> path pf c\<^sub>2 pa\<^sub>2 a\<^sub>2 \<longrightarrow> path pf c\<^sub>2 pb\<^sub>2 a\<^sub>2
\<longrightarrow> x \<in> set (tl pa\<^sub>1) \<or> x \<in> set (tl pb\<^sub>1) \<or> x \<in> set (tl pa\<^sub>2) \<or> x \<in> set (tl pb\<^sub>2)
\<longrightarrow> ti ! x < ti ! k)"

definition timestamps_invar
  where
"timestamps_invar cc = timestamps_decrease_invar (timestamps cc) (proof_forest cc) (pf_labels cc)"


theorem cc_explain_aux2_domain:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
  shows "cc_explain_aux2_dom (cc, xs)"
  sorry

subsection \<open>Correctness proof of \<open>cc_explain2\<close>\<close>

lemma explain_along_path2_correctness:
  assumes "explain_along_path2_dom (\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>, a, c)"
    (is "explain_along_path2_dom (?cc, a, c)")
    "ufa_invar pf"
    "a < length pf"
    "c < length pf"
    "explain_along_path2 \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr> a c = (output, pend)"
    "path pf c pAC a"
    "pf_labels_invar \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "(a \<approx> c) \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
  using assms proof(induction "\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    a c arbitrary: pAC "output" pend rule: explain_along_path2.pinduct)
  case (1 a c)
  then show ?case proof(cases "a = c")
    case True
    then show ?thesis 
      by (simp add: Congruence_Closure.reflexive)
  next
    case False
    let ?cc = "\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl,  input = ip\<rparr>"
    from False obtain output' pend' where recursive_step: 
      "explain_along_path2 ?cc (pf ! a) c = (output', pend')"
      by fastforce
    obtain pRAC where pRAC: "pf ! a \<noteq> a \<and> path pf c pRAC a" 
      using "1.prems" False assms(2) explain_list_invar_imp_valid_rep path_root by blast
    with "1.prems"  have pRAC': "path pf c (butlast pRAC) (pf ! a)" 
      using False path_butlast by blast
    obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
(pfl ! a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! a \<and> bb = a \<or> aa = a \<and> bb = pf ! a)
        "using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
      by (meson pRAC path_nodes_lt_length_l)
    have rep_neq: "a \<noteq> (pf ! a)"
      using pRAC "1.prems" False rep_of_a_and_parent_rep_neq by simp
    then have valid: "(pf ! a) < length pf" 
      using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar by blast
        \<comment> \<open>If \<open>(pf ! a) \<approx> c\<close> is in the congruence closure of the recursive call, 
        then it will also be in the congruence closure of the output.\<close>
    have cc_output: "((pf ! a) \<approx> c) \<in>
 Congruence_Closure (output'
\<union> pending_set_explain pend')
\<Longrightarrow> ((pf ! a) \<approx> a) \<in> Congruence_Closure
        (output \<union> pending_set_explain pend) 
\<Longrightarrow> output' \<subseteq> output
\<Longrightarrow> pending_set_explain pend' \<subseteq> pending_set_explain pend 
\<Longrightarrow> ((pf ! a) \<approx> c) \<in> Congruence_Closure
        (output \<union> pending_set_explain pend)"
    proof(rule Congruence_Closure_imp)
      fix eq
      assume prems: "eq \<in> output' \<union> pending_set_explain pend'"
        "((pf ! a) \<approx> a)
         \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
        "output' \<subseteq> output" "pending_set_explain pend' \<subseteq> pending_set_explain pend"        
      then show "eq \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
        by blast
    qed 
    show ?thesis proof(cases "the (pfl ! a)")
      case (One a')
      from valid_eq have *: "pfl ! a = Some (One a')" 
        using One by auto
      with recursive_step 1(2)[OF False] have IH: 
        "(pf ! a \<approx> c) \<in> Congruence_Closure (output' \<union> pending_set_explain pend')" 
        using "1.prems" One pRAC' * valid  by simp
      have result: "(output, pend) = ({a'} \<union> output', pend')" 
        using 1 explain_along_path2_simp2[OF False] One False * recursive_step by simp
      then have a': "a' = (a \<approx> pf ! a) \<or> a' = (pf ! a \<approx> a)" 
        using One valid_eq by auto
      then have "(a \<approx> pf ! a) \<in> Congruence_Closure ({a'} \<union> output')" 
        by blast
      with result have 2: "(a \<approx> pf ! a) \<in> 
Congruence_Closure (output \<union> pending_set_explain pend)"
        using Congruence_Closure_split_rule by (metis (no_types, lifting) Pair_inject sup_commute)
      from result have "output' \<subseteq> output"  "pending_set_explain pend' \<subseteq> pending_set_explain pend"
        by blast+
      with cc_output have 3: "(pf ! a \<approx> c) \<in> Congruence_Closure
        (output \<union> pending_set_explain pend)" 
        using "2" IH by blast
      from 2 3 show ?thesis by blast
    next
      case (Two x21 x22)
      then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where *: "(pfl ! a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
        by (metis option.sel pending_equation.distinct(1) valid_eq) 
      with recursive_step 1(3)[OF False] have IH: 
        "(pf ! a \<approx> c) \<in>
 Congruence_Closure (output'
\<union> pending_set_explain pend')" 
        using * pRAC' valid "1.prems" by auto 
      have result: "(output, pend) = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
        using False congruence_closure.select_convs * recursive_step 1(1,7) explain_along_path2_simp3
        by simp
      then have a': "a' = a \<and> b' = pf ! a
\<or> a' = pf ! a \<and> b' = a" 
        using valid_eq * by auto
      have "(a\<^sub>1 \<approx> b\<^sub>1) \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
        "(a\<^sub>2 \<approx> b\<^sub>2) \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
        "(F a\<^sub>1 a\<^sub>2 \<approx> a') \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
        "(F b\<^sub>1 b\<^sub>2 \<approx> b') \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
        using result by auto
      then have 2: "(a \<approx> (pf ! a)) \<in> 
Congruence_Closure (output \<union> pending_set_explain pend)" 
        using a' monotonic by blast
      with cc_output have "((pf ! a) \<approx> c) \<in> Congruence_Closure
        (output \<union> pending_set_explain pend)"
        using Congruence_Closure_monotonic 2 result IH by auto
      then show ?thesis using 2 by blast
    qed
  qed
qed

lemma explain_along_path2_correctness':
  assumes "cc_invar cc"
    "explain_along_path2 cc a c = (output, pend)"
    "path (proof_forest cc) c pAC a"
  shows "(a \<approx> c) \<in> Congruence_Closure (output \<union> pending_set_explain pend)"
proof-
  obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
  then have "ufa_invar pf"
    "a < length pf"
    "c < length pf" "pf_labels_invar cc"
    using assms unfolding proof_forest_invar_def same_length_invar_def 
       apply (metis congruence_closure.select_convs(5))
    using assms  cc path_nodes_lt_length_l proof_forest_loop propagate_loop.simps(2)
    unfolding proof_forest_invar_def same_length_invar_def 
    by metis+
  then show ?thesis using explain_along_path2_correctness cc assms explain_along_path2_domain
    by (metis congruence_closure.select_convs(5))
qed

lemma explain_along_path2_pending:
  assumes "cc_invar cc"
    "explain_along_path2 cc a c = (output, pend)"
    "path (proof_forest cc) c pAC a"
  shows "\<forall>x \<in> pending_set_explain pend. are_congruent cc x"
proof-
  have "explain_along_path2_dom (cc, a, c)" 
    using explain_along_path2_domain assms by blast
  then show ?thesis 
    using assms proof(induction arbitrary: pend "output" pAC
      rule: explain_along_path2.pinduct)
    case (1 cc a c)
    then show ?case proof(cases "a = c")
      case True
      then have "pend = []" 
        using "1.prems"(2) CC_Explain2.explain_along_path2_simp1 by fastforce
      then show ?thesis by simp
    next
      case False
      define b where "b = proof_forest cc ! a"
      then have p2: "path (proof_forest cc) c (butlast pAC) b"
        using "1.prems"(3) False path_butlast by blast
      obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
          (pf_labels cc ! a = Some (One (aa \<approx> bb)) \<or> 
          pf_labels cc ! a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = proof_forest cc ! a \<and> bb = a \<or> aa = a \<and> bb = proof_forest cc ! a)" 
        using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
        by (metis False b_def path_nodes_lt_length_l path_root)
      have "(pf_labels cc ! a) \<noteq> None" 
        by (metis "1.prems"(1) "1.prems"(3) False b_def option.discI path_nodes_lt_length_l path_root pf_labels_invar_def)
      obtain pend_rec output_rec where
        rec: "explain_along_path2 cc b c = (output_rec, pend_rec)"
        by fastforce
      then show ?thesis
      proof(cases "the (pf_labels cc ! a)")
        case (One x1)
        then have *: "\<forall>a\<in>pending_set_explain pend_rec. are_congruent cc a"
          using 1(2) False One b_def p2 1(4) rec by blast
        then have "pend = pend_rec" 
          using One explain_along_path2_simp2 explain_along_path_domain 
          using "1.hyps" "1.prems"(2) False rec \<open>pf_labels cc ! a \<noteq> None\<close> b_def by force
        then show ?thesis using * 
          by blast
      next
        case (Two x21 x22)
        then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where **: "(pf_labels cc ! a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
          by (metis option.sel pending_equation.distinct(1) valid_eq) 
        then have *: "\<forall>a\<in>pending_set_explain pend_rec. are_congruent cc a"
          using 1(3) False Two b_def p2 1(4) rec 
          by (metis option.sel)
        then have pend: "pend = [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend_rec" 
          using Two explain_along_path2_simp3[OF False **] explain_along_path_domain 
          using "1.hyps" "1.prems"(2) False rec \<open>pf_labels cc ! a \<noteq> None\<close> b_def rec by simp
        have "rep_of (cc_list cc) a\<^sub>1 = rep_of (cc_list cc) b\<^sub>1"
          "rep_of (cc_list cc) a\<^sub>2 = rep_of (cc_list cc) b\<^sub>2"
          using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
           apply (metis "**" False option.sel path_no_root path_nodes_lt_length_l valid_vars_pending.simps(2))
          using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
          by (metis "**" False option.sel path_no_root path_nodes_lt_length_l valid_vars_pending.simps(2))
        then have "are_congruent cc (a\<^sub>1 \<approx> b\<^sub>1)" "are_congruent cc (a\<^sub>2 \<approx> b\<^sub>2)"
          by (metis (full_types) are_congruent.simps(1) congruence_closure.cases congruence_closure.select_convs(1))+
        then show ?thesis 
          using * pend by simp
      qed
    qed
  qed
qed

lemma pending_set_explain_set: 
  "(a, b) \<in> set xs \<longleftrightarrow> (a \<approx> b) \<in> pending_set_explain xs"
proof
  show "(a, b) \<in> set xs \<Longrightarrow> (a \<approx> b) \<in> pending_set_explain xs"
  proof-
    assume "(a, b) \<in> set xs"
  then obtain i where i: "xs ! i = (a, b)" "i < length xs"
    using in_set_conv_nth by metis
  then have "(map (\<lambda>(a, b) . (a \<approx> b)) xs) ! i = (a \<approx> b)"
    by simp
  then have "(a \<approx> b) \<in> set (map (\<lambda>(a, b) . (a \<approx> b)) xs)"
    using i by (metis length_map nth_mem)
  then show ?thesis 
    by force
qed
  show "(a \<approx> b) \<in> pending_set_explain xs \<Longrightarrow> (a, b) \<in> set xs"
  proof-
assume "(a \<approx> b) \<in> pending_set_explain xs"
  then obtain i where i: "(map (\<lambda>(a, b) . (a \<approx> b)) xs) ! i = (a \<approx> b)" 
"i < length (map (\<lambda>(a, b) . (a \<approx> b)) xs)"
    using in_set_conv_nth by (metis pending_set_explain.simps)
  then have "xs ! i = (a, b)"
    by (metis equation.inject(1) length_map nth_map prod.collapse split_beta)
  then have "(a \<approx> b) \<in> set (map (\<lambda>(a, b) . (a \<approx> b)) xs)"
    using i by (metis length_map nth_mem)
  then show ?thesis 
    by force
qed
qed

lemma explain_along_path2_pending':
  assumes "cc_invar cc"
    "explain_along_path2 cc a c = (output, pend)"
    "explain_along_path2 cc b c = (output2, pend2)"
    "path (proof_forest cc) c pAC a"
    "path (proof_forest cc) c pBC b"
  shows "\<forall>(a, b) \<in> set (pend @ pend2). are_congruent cc (a \<approx> b)"
proof
  fix x assume "x \<in> set (pend @ pend2)"
  obtain a' b' where x: "x = (a', b')" 
    using prod_decode_aux.cases by blast
  then have in_pend_set: "(a' \<approx> b') \<in> pending_set_explain (pend @ pend2)"  
    by (metis \<open>x \<in> set (pend @ pend2)\<close> pending_set_explain_set)
  then have "\<forall>x \<in> pending_set_explain (pend @ pend2) . are_congruent cc x"    
    using assms explain_along_path2_pending 
    by fastforce
  then have "are_congruent cc (a' \<approx> b')" 
    using in_pend_set by blast
  then show "case x of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)" 
    by (simp add: x)
qed

lemma explain_along_path2_pending_in_bounds:
  assumes "cc_invar cc"
    "explain_along_path2 cc a c = (output, pend)"
    "path (proof_forest cc) c pAC a"
  shows "\<forall>(a,b)\<in>set pend. a < nr_vars cc \<and> b < nr_vars cc"
proof-
  have "explain_along_path2_dom (cc, a, c)" 
    using explain_along_path2_domain assms by blast
  then show ?thesis 
    using assms proof(induction arbitrary: pend "output" pAC
      rule: explain_along_path2.pinduct)
    case (1 cc a c)
    then show ?case proof(cases "a = c")
      case True
      then have "pend = []" 
        using "1.prems"(2) CC_Explain2.explain_along_path2_simp1 by fastforce
      then show ?thesis by simp
    next
      case False
      define b where "b = proof_forest cc ! a"
      then have p2: "path (proof_forest cc) c (butlast pAC) b"
        using "1.prems"(3) False path_butlast by blast
      obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
          (pf_labels cc ! a = Some (One (aa \<approx> bb)) \<or> 
          pf_labels cc ! a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = proof_forest cc ! a \<and> bb = a \<or> aa = a \<and> bb = proof_forest cc ! a)" 
        using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
        by (metis False b_def path_nodes_lt_length_l path_root)
      have "(pf_labels cc ! a) \<noteq> None" 
        by (metis "1.prems"(1) "1.prems"(3) False b_def option.discI path_nodes_lt_length_l path_root pf_labels_invar_def)
      obtain pend_rec output_rec where
        rec: "explain_along_path2 cc b c = (output_rec, pend_rec)"
        by fastforce
      then show ?thesis
      proof(cases "the (pf_labels cc ! a)")
        case (One x1)
        then have *: "\<forall>(a,b)\<in>set pend_rec. a < nr_vars cc \<and> b < nr_vars cc"
          using 1(2) False One b_def p2 1(4) rec by blast
        then have "pend = pend_rec" 
          using One explain_along_path2_simp2 explain_along_path_domain 
          using "1.hyps" "1.prems"(2) False rec \<open>pf_labels cc ! a \<noteq> None\<close> b_def by force
        then show ?thesis using * 
          by blast
      next
        case (Two x21 x22)
        then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where **: "(pf_labels cc ! a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
          by (metis option.sel pending_equation.distinct(1) valid_eq) 
        then have *: "\<forall>(a,b)\<in>set pend_rec. a < nr_vars cc \<and> b < nr_vars cc"
          using 1(3) False Two b_def p2 1(4) rec 
          by (metis option.sel)
        then have pend: "pend = [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend_rec" 
          using Two explain_along_path2_simp3[OF False **] explain_along_path_domain 
          using "1.hyps" "1.prems"(2) False rec \<open>pf_labels cc ! a \<noteq> None\<close> b_def rec by simp
        then have "a\<^sub>1 < nr_vars cc" "a\<^sub>2 < nr_vars cc" "b\<^sub>1 < nr_vars cc" "b\<^sub>2 < nr_vars cc"
          using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
          by (metis "**" False option.sel path_nodes_lt_length_l path_root valid_vars.simps(2) valid_vars_pending.simps(2))+
        then show ?thesis 
          using * pend by simp
      qed
    qed
  qed
qed

lemma cc_explain_aux2_correctness:
  assumes "cc_invar cc"
    "\<forall>(a, b)\<in>set xs. a < nr_vars cc \<and> b < nr_vars cc"
    "(x, y) \<in> set xs" "are_congruent cc (x \<approx> y)"
  shows "(x \<approx> y) \<in> Congruence_Closure (cc_explain_aux2 cc xs)"
proof-
  have "cc_explain_aux2_dom (cc, xs)"
    sorry
  then show ?thesis 
    using assms proof(induction arbitrary: x y rule: cc_explain_aux2.pinduct)
    case (2 cc a b xs)
    then show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"
      then obtain p1 p2 where p: "path (proof_forest cc) c p1 a"
        "path (proof_forest cc) c p2 b" using assms unfolding proof_forest_invar_def 
        by (metis "2.prems"(1) "2.prems"(2) True case_prod_conv explain_along_path_lowest_common_ancestor list.set_intros(1))
      obtain output1 pending1 output2 pending2 
        where
          eap: "(output1, pending1) = explain_along_path2 cc a c"
          "(output2, pending2) = explain_along_path2 cc b c"
        by (metis old.prod.exhaust)
      have "\<forall>a\<in>set pending1. case a of (a, b) \<Rightarrow> 
a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall>a\<in>set pending2. case a of (a, b) \<Rightarrow> 
a < nr_vars cc \<and> b < nr_vars cc"
        using explain_along_path2_pending_in_bounds eap p
        by (metis "2.prems"(1))+
      then have pend: "\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> 
a < nr_vars cc \<and> b < nr_vars cc" 
        using 2(5) by fastforce
      have pend2: "\<forall>x \<in> pending_set_explain pending1.  
are_congruent cc x" "\<forall>x \<in> pending_set_explain pending2.  
are_congruent cc x" using explain_along_path2_pending eap p
        by (metis "2.prems"(1))+
      have less: "a < nr_vars cc" "b < nr_vars cc" 
        using 2(5) by fastforce+
      then have "c < nr_vars cc"  using "2.prems"(1) unfolding same_length_invar_def 
        by (metis p(2) path_nodes_lt_length_l)
      have recursive: "cc_explain_aux2 cc ((a, b) # xs)
= output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs)"
        by (simp add: "2.hyps" cc_explain_aux2_simp2 True c_def eap(1) eap(2))
      have IH: "\<forall> a b. (a \<approx> b) \<in> pending_set_explain pending1 \<longrightarrow> are_congruent cc (a \<approx> b)
\<longrightarrow> (a \<approx> b) \<in> Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        "\<forall> a b. (a \<approx> b) \<in> pending_set_explain pending2 \<longrightarrow> are_congruent cc (a \<approx> b)
\<longrightarrow> (a \<approx> b) \<in> Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        using 2(2) True c_def eap 2(4-6) pend by auto
      have subsets: "pending_set_explain pending1 \<subseteq> 
Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        "pending_set_explain pending2 \<subseteq> 
Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        using IH pend2 apply auto[1] using IH(2) pend2 by auto
      then show ?thesis using 2 
      proof(cases "(x, y) = (a, b)")
        case True
        have "(a \<approx> c) \<in> Congruence_Closure (output1 \<union> pending_set_explain pending1)"
          "(b \<approx> c) \<in> Congruence_Closure (output2 \<union> pending_set_explain pending2)"
          using explain_along_path2_correctness' p less eap using "2.prems"(1) by auto
        then have "(a \<approx> c) \<in> Congruence_Closure (output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
          "(b \<approx> c) \<in> Congruence_Closure (output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
          using Congruence_Closure_split_rule subsets 
          by (smt (z3) Congruence_Closure_imp Un_commute Un_iff subset_eq)+
        then show ?thesis using recursive 
          by (metis Congruence_Closure.symmetric Congruence_Closure.transitive1 True prod.inject)
      next
        case False
        then have "(x \<approx> y) \<in> Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
          using 2(2)[OF True c_def] eap 2(4,6) pend  
          by (metis "2.prems"(4) "2.prems"(4) Un_iff set_ConsD set_union_code)
        then show ?thesis 
          using Congruence_Closure_union' recursive by auto
      qed
    next
      case False
      then show ?thesis using 2 
        using cc_explain_aux2_simp3 by auto
    qed
  qed simp
qed

theorem cc_explain2_correctness:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc" "valid_vars (a \<approx> b) (nr_vars cc)"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain2 cc a b)"
  using cc_explain_aux2_correctness valid_vars.simps assms 
  by auto


end
