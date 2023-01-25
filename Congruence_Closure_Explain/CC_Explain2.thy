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

subsection \<open>Equivalence proof of \<open>cc_explain2\<close> and \<open>cc_explain\<close>\<close>

subsubsection \<open>Induction rule on \<open>explain_long_path2\<close>\<close>


lemma explain_along_path2_induct[consumes 3, case_names base One Two]:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
    "explain_along_path2 cc a c = (output, pend)"
    "(\<And>cc a c p.
    explain_along_path2_dom (cc, a, c) \<Longrightarrow>
    cc_invar cc \<Longrightarrow>
      path (proof_forest cc) c p a \<Longrightarrow>
        a = c \<Longrightarrow>
        P cc a c {} [] p)" 
    "(\<And>cc a c p1 p2 x x1 x11 x12 output pend.
    explain_along_path2_dom (cc, a, c) \<Longrightarrow>
    cc_invar cc \<Longrightarrow>
      path (proof_forest cc) c p1 a \<Longrightarrow>
      path (proof_forest cc) c p2 x \<Longrightarrow>
      explain_along_path2 cc x c = (output, pend) \<Longrightarrow>
      a \<noteq> c \<Longrightarrow>
      x = proof_forest cc ! a \<Longrightarrow> 
      pf_labels cc ! a = Some (One x1) \<Longrightarrow>
      x11 < nr_vars cc \<Longrightarrow> x12 < nr_vars cc \<Longrightarrow> x1 = (x11 \<approx> x12) \<Longrightarrow>
      x < nr_vars cc \<Longrightarrow>
      P cc x c output pend p2 \<Longrightarrow>
         P cc a c ({x1} \<union> output) pend p1)" 
    "(\<And>cc a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y output pend.
      explain_along_path2_dom (cc, a, c) \<Longrightarrow>
      cc_invar cc \<Longrightarrow>
      path (proof_forest cc) c p1 a \<Longrightarrow>
      path (proof_forest cc) c p2 x \<Longrightarrow>
       explain_along_path2 cc x c = (output, pend) \<Longrightarrow>
       a \<noteq> c \<Longrightarrow>
        x = proof_forest cc ! a \<Longrightarrow>
        pf_labels cc ! a = Some (Two x21 x22) 
      \<Longrightarrow> x21 = (F x\<^sub>1 x\<^sub>2 \<approx> x') \<Longrightarrow> x22 = (F y\<^sub>1 y\<^sub>2 \<approx> y) \<Longrightarrow>
      x < nr_vars cc \<Longrightarrow> x\<^sub>1 < nr_vars cc \<Longrightarrow> x\<^sub>2 < nr_vars cc 
      \<Longrightarrow> x' < nr_vars cc \<Longrightarrow> y\<^sub>1 < nr_vars cc \<Longrightarrow> y\<^sub>2 < nr_vars cc \<Longrightarrow> y < nr_vars cc 
      \<Longrightarrow> P cc x c output pend p2 \<Longrightarrow>
      P cc a c ({(F x\<^sub>1 x\<^sub>2 \<approx> x'), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> output) ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pend) p1)"
  shows "P cc a c output pend p"
proof-
  have "explain_along_path2_dom (cc, a, c)"
    using assms explain_along_path2_domain by fast
  then show ?thesis
    using assms proof(induction 
      arbitrary: "output" pend p
      rule: explain_along_path2.pinduct)
    case (1 cc a c)
    then show ?case 
    proof(cases "a = c")
      case True
      with 1(6) have "output = {}"  "pend = []" using explain_along_path2_simp1
        by simp+
      then show ?thesis using 1(7) 
        using "1.hyps" "1.prems"(1,2) True by blast
    next
      case False
      define x where "x = (proof_forest cc) ! a"
      have path_to_rep: "path (proof_forest cc) c (butlast p) x" 
        using "1.prems" x_def 
        using False path_butlast by auto
      have not_none: "(pf_labels cc) ! a \<noteq> None"   
        using "1.prems" False pf_labels_invar_def path_nodes_lt_length_l 
        by (metis option.distinct(1) path_root)
      then obtain output_rec' pending_rec' 
        where 
          rec': "explain_along_path2 cc x c = (output_rec',  pending_rec')"
        using old.prod.exhaust by blast
      then have "x < nr_vars cc" 
        using "1.prems"(1,2) same_length_invar_def path_nodes_lt_length_l path_to_rep 
        by metis
      show ?thesis
      proof(cases "the ((pf_labels cc) ! a)")
        case (One x1)
        then have Some: "(pf_labels cc) ! a = Some (One x1)"
          using not_none by auto
        then obtain x11 x12 where "x1 = (x11 \<approx> x12)" "x11 < nr_vars cc" "x12 < nr_vars cc" 
          using "1.prems" One not_none unfolding pf_labels_invar_def same_length_invar_def 
          by (metis False \<open>x < nr_vars cc\<close> option.sel path_nodes_lt_length_l path_root pending_equation.distinct(1) pending_equation.inject(1) x_def)
        then have rec: "(output, pend) = ({x1} \<union> output_rec', pending_rec')"
          using "1.hyps" "1.prems" False Some x_def explain_along_path2_simp2 
          by (metis rec')
        have IH: "P cc x c output_rec' pending_rec' (butlast p)" using 1(2) 
          using "1.prems"(1) False One assms(4-6) rec' x_def path_to_rep by blast
        then show ?thesis using 1(8) 
          using "1.hyps" "1.prems"(1,2,3) False Some \<open>x < nr_vars cc\<close> \<open>x1 = (x11 \<approx> x12)\<close> \<open>x11 < nr_vars cc\<close> \<open>x12 < nr_vars cc\<close> local.rec path_to_rep rec' x_def
          by blast
      next
        case (Two x21 x22)
        then obtain x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y where Some: "(pf_labels cc) ! a = 
Some (Two (F x\<^sub>1 x\<^sub>2 \<approx> x') (F y\<^sub>1 y\<^sub>2 \<approx> y))" "x\<^sub>1 < nr_vars cc" "x\<^sub>2 < nr_vars cc" "x' < nr_vars cc"
          "y\<^sub>1 < nr_vars cc" "y\<^sub>2 < nr_vars cc"  "y < nr_vars cc"
          using pf_labels_invar_def "1.prems" False not_none sorry
        then have x21x22: "x21 = (F x\<^sub>1 x\<^sub>2 \<approx> x')" "x22 = (F y\<^sub>1 y\<^sub>2 \<approx> y)" using Two by auto
        have rec: "(output, pend) 
= ({(F x\<^sub>1 x\<^sub>2 \<approx> x'), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> output_rec', [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ pending_rec')"
          using explain_along_path2_simp3 False Some(1) rec' x_def 1(1,6) by auto
        have IH: "P cc x c output_rec' pending_rec' (butlast p)" 
          using 1(3) False x_def Two x21x22 "1.prems"(1) path_to_rep rec' 
          using assms(4-6) by blast
        then show ?thesis  
          using 1(9)[OF 1(1,4,5) path_to_rep rec' False
x_def Some(1) _ _ \<open>x < nr_vars cc\<close> Some(2,3,4,5,6,7) IH] rec 
          by blast
      qed
    qed
  qed
qed

subsubsection \<open>Induction rule on \<open>cc_explain2\<close>\<close>

lemma cc_explain_aux2_induct[consumes 2, case_names base congruent not_congruent]:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "(\<And>cc . cc_explain_aux2_dom (cc, []) \<Longrightarrow>
cc_invar cc 
 \<Longrightarrow> P cc [])" 
    "\<And>cc a b xs c output1 pending1 output2  pending2.
    cc_explain_aux2_dom (cc, (a, b) # xs) \<Longrightarrow>
 cc_invar cc \<Longrightarrow>
(\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc) \<Longrightarrow>
 a < nr_vars cc \<Longrightarrow> b < nr_vars cc \<Longrightarrow>
        are_congruent cc (a \<approx> b) \<Longrightarrow>
       c = lowest_common_ancestor (proof_forest cc) a b \<Longrightarrow>
    (output1, pending1) = explain_along_path2 cc a c \<Longrightarrow>
    (output2, pending2) = explain_along_path2 cc b c
\<Longrightarrow> P cc (pending1 @ pending2 @ xs)
\<Longrightarrow> P cc ((a, b) # xs)" 
    "\<And>cc a b xs.
    cc_explain_aux2_dom (cc, (a, b) # xs) \<Longrightarrow>
cc_invar cc \<Longrightarrow> 
(\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc) \<Longrightarrow>
 a < nr_vars cc \<Longrightarrow> b < nr_vars cc \<Longrightarrow>
(\<not> are_congruent cc (a \<approx> b) \<Longrightarrow> P cc xs
\<Longrightarrow> P cc ((a, b) # xs))"
  shows "P cc xs"
proof-
  have "cc_explain_aux2_dom (cc, xs)" using assms(1-3) cc_explain_aux2_domain 
    by blast
  then show ?thesis using assms proof(induction rule: cc_explain_aux2.pinduct)
    case (2 cc a b xs)
    have in_bounds: "a < nr_vars cc" "b < nr_vars cc" using 2(5) by auto 
    show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"
      obtain output1 new_l pending1 output2 pending2
        where eap: "(output1, pending1) = explain_along_path2 cc a c" 
          "(output2, pending2) = explain_along_path2 cc b c"
        by (metis old.prod.exhaust)
      obtain p1 p2 where p: "path (proof_forest cc) c p1 a"
"path (proof_forest cc) c p2 b" using 2 unfolding proof_forest_invar_def 
        by (metis "2.prems"(1) True c_def explain_along_path_lowest_common_ancestor in_bounds(1) in_bounds(2))
      then have " \<forall>(k, j)\<in>set (pending1). k < nr_vars cc \<and> j < nr_vars cc" 
        " \<forall>(k, j)\<in>set (pending2). k < nr_vars cc \<and> j < nr_vars cc" 
        " \<forall>(k, j)\<in>set (xs). k < nr_vars cc \<and> j < nr_vars cc" 
            using explain_along_path2_pending_in_bounds eap 
              apply (metis "2.prems"(1))
            using 2(5) explain_along_path2_pending_in_bounds eap 
             apply (metis "2.prems"(1) p(2))
            using 2(5) 
            by simp
      then have " \<forall>(k, j)\<in>set (pending1 @ pending2 @ xs). k < nr_vars cc \<and> j < nr_vars cc"
        by auto
      then have "P cc (pending1 @ pending2 @ xs)"
        using 2(2)[OF True c_def] eap 2(3,4,5,6,7,8) 
        by blast
      then show ?thesis using "2.prems"(4)[OF 2(1,4)] 2(1,3,4,5,6) 
        using True c_def eap(1) eap(2) in_bounds(1) in_bounds(2) list.set_intros(2) 
        by metis
    next
      case False
      have "P cc xs" using 2(3)[OF False 2(4)] 2(5,6,7,8) 
        by fastforce
      then show ?thesis using "2.prems"(5)[OF 2(1,4)] using 2(5) False 
        by auto
    qed
  qed blast
qed

subsubsection \<open>Lemma about \<open>cc_explain2\<close> and append\<close>

theorem cc_explain_aux2_app:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ys . a < nr_vars cc \<and> b < nr_vars cc"
  shows "cc_explain_aux2 cc (xs @ ys) = cc_explain_aux2 cc xs \<union> cc_explain_aux2 cc ys"
  using assms proof(induction rule: cc_explain_aux2_induct)
  case (base cc)
  then show ?case using cc_explain_aux2.psimps by auto
next
  case (congruent cc a b xs c output1 pending1 output2 pending2)
  then have "\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc" 
    by auto
  have " \<forall>(a, b)\<in>set (((a,b) # xs) @ ys). a < nr_vars cc \<and> b < nr_vars cc"
    using congruent by auto
  then have dom: "cc_explain_aux2_dom (cc, (((a,b) # xs) @ ys))"
    "cc_explain_aux2_dom (cc, ((a, b) # xs))"
    using cc_explain_aux2_domain congruent by blast+
  have in_bounds: "a < nr_vars cc" "b < nr_vars cc" 
    using congruent unfolding explain_list_invar_def same_length_invar_def by auto
  then have same_rep: "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    using congruent are_congruent_rep_of(2) by presburger
  then obtain p1 p2 where p: "path (proof_forest cc) c p1 a" 
    "path (proof_forest cc) c p2 b"  
    using congruent in_bounds explain_along_path_lowest_common_ancestor
    by metis
  then have bounds1: "\<forall>(a, b)\<in>set pending1. a < nr_vars cc \<and> b < nr_vars cc"
    using explain_along_path2_pending_in_bounds congruent
    by metis
  have "\<forall>(a, b)\<in>set pending2. a < nr_vars cc \<and> b < nr_vars cc"
    using explain_along_path2_pending_in_bounds congruent 
    by (metis p(2))
  then have in_bounds2: "\<forall>a\<in>set (pending1 @ pending2 @ xs).
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall>a\<in>set ys.
       case a of
       (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
    using bounds1 congruent by auto
  have "cc_explain_aux2 cc (((a, b) # xs) @ ys) = 
output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs @ ys)"
    using cc_explain_aux2_simp2 dom congruent
    by auto

  also have "... = output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs) 
\<union> cc_explain_aux2 cc ys"
    using congruent in_bounds2 by auto
  also have "... = cc_explain_aux2 cc ((a, b) # xs) \<union> cc_explain_aux2 cc ys"
    using cc_explain_aux2_simp2 dom(2) congruent
    by simp
  finally show ?case 
    by simp
next
  case (not_congruent cc a b xs)
  then have " \<forall>(a, b)\<in>set (((a,b) # xs) @ ys). a < nr_vars cc \<and> b < nr_vars cc"
    by auto
  then have dom: "cc_explain_aux2_dom (cc, (((a,b) # xs) @ ys))"
    "cc_explain_aux2_dom (cc, ((a, b) # xs))"
    using cc_explain_aux2_domain not_congruent by blast+
  then have "cc_explain_aux2 cc (((a, b) # xs) @ ys) = cc_explain_aux2 cc (xs @ ys)"
    using cc_explain_aux2_simp3 dom 
    by (simp add: not_congruent.hyps(6))
  then show ?case 
    using not_congruent cc_explain_aux2_simp3 dom(2) 
    using \<open>\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc\<close> by presburger
qed

subsubsection \<open>Equivalence of \<open>explain_along_path\<close> and \<open>explain_along_path2\<close>\<close>

lemma explain_along_path_parent_eq:
  assumes "cc_invar cc" 
    "explain_list_invar l (proof_forest cc)" 
    "path (proof_forest cc) c p a"
  shows "explain_along_path cc l a c = explain_along_path cc l (l ! a) c"
proof(cases "l ! a = a")
  case False
  have *: "rep_of l a = rep_of l (l ! a)" 
    using assms(2) assms(3) explain_list_invar_def path_nodes_lt_length_l rep_of_idx by fastforce
  then show ?thesis proof(cases "rep_of l a = rep_of l c")
    case True
    then show ?thesis using * explain_along_path_simp1 
      by simp
  next
    case False': False
    have "l ! a = proof_forest cc ! a" using assms False unfolding explain_list_invar_def  
      using path_nodes_lt_length_l by presburger
    then have p: "path (proof_forest cc) c (butlast p) (l ! a)" 
      using False' assms(3) path_butlast by auto
    have not_none: "pf_labels cc! rep_of l a \<noteq> None" using pf_labels_explain_along_path_case_2 
      using False' assms(1) assms(2) assms(3) explain_list_invar_def path_nodes_lt_length_l by auto
    define b where "b = proof_forest cc ! rep_of l a"
    obtain o_rec l_rec p_rec where rec: "explain_along_path cc (l[rep_of l a := b]) b c
= (o_rec, l_rec, p_rec)"
      using prod_cases3 by blast
    then show ?thesis proof(cases "the ((pf_labels cc) ! rep_of l a)")
      case (One x1)
      have "explain_along_path cc l a c = ({x1} \<union> o_rec, l_rec, p_rec)"
        using explain_along_path_simp2 explain_along_path_domain b_def rec not_none explain_list_invar_def 
        using False' One assms(1) assms(2) assms(3) by force
      moreover have "explain_along_path cc l (l ! a) c = ({x1} \<union> o_rec, l_rec, p_rec)"
        using * explain_along_path_simp2 explain_along_path_domain b_def rec not_none explain_list_invar_def 
        using False' One assms(1) assms(2) p by force
      ultimately show ?thesis using * explain_along_path_simp2 explain_along_path_domain 
        by argo
    next
      case (Two x21 x22)
      then obtain x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y where Some: "(pf_labels cc) ! rep_of l a = 
Some (Two (F x\<^sub>1 x\<^sub>2 \<approx> x') (F y\<^sub>1 y\<^sub>2 \<approx> y))" "x\<^sub>1 < length l" "x\<^sub>2 < length l" "x' < length l"
        "y\<^sub>1 < length l" "y\<^sub>2 < length l"  "y < length l"
        using pf_labels_Two_valid assms False False' by blast
      have "explain_along_path cc l a c = 
({(F x\<^sub>1 x\<^sub>2 \<approx> x'), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> o_rec, l_rec, [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ p_rec)"
        using explain_along_path_simp3 explain_along_path_domain b_def rec not_none explain_list_invar_def 
        using False' Some assms(1) assms(2) assms(3) by force
      moreover have "explain_along_path cc l (l ! a) c = 
({(F x\<^sub>1 x\<^sub>2 \<approx> x'), (F y\<^sub>1 y\<^sub>2 \<approx> y)} \<union> o_rec, l_rec, [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ p_rec)"
        using * explain_along_path_simp3 explain_along_path_domain b_def rec not_none explain_list_invar_def 
        using False' Some assms(1) assms(2) p by force
      ultimately show ?thesis 
        by argo
    qed 
  qed
qed simp

lemma explain_along_path_explain_along_path2_pending_subseq:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
"explain_along_path2 cc a c = (output2, pend2)"
 "explain_list_invar l (proof_forest cc)" 
"explain_along_path cc l a c = (output, new_l, pend)"
shows "subseq pend pend2"
using assms proof(induction arbitrary: l "output" new_l pend rule: explain_along_path2_induct)
  case (base cc a c p)
  then show ?case 
    by (simp add: explain_along_path_simp1)
next
  case (One cc a c p1 p2 x x1 x11 x12 "output2" pend2)
  then show ?case 
  proof(cases "a = rep_of l a")
    case True
    obtain o_rec l_rec p_rec where
 rec: "explain_along_path cc (l[rep_of l a := x]) x c = (o_rec, l_rec, p_rec)"
      using prod_cases3 by blast
    have invar: "explain_list_invar (l[rep_of l a := x]) (proof_forest cc)" 
      using explain_list_invar_step[OF One(14)] One(2,7) proof_forest_invar_def 
      by (metis One.hyps(3) One.prems(1) True explain_list_invar_def path_nodes_lt_length_l)
    have *: "rep_of l a \<noteq> rep_of l c" using explain_list_invar_def One True 
      by (metis path_nodes_lt_length_l path_pf_same_rep path_root proof_forest_invar_def rep_of_root) 
    have "pend = p_rec" 
      using explain_along_path_simp2[OF *] One(2,3,7,8,15) rec 
explain_along_path_domain[OF One(2,14,3)] True by auto
    then show ?thesis 
      using One(13)[OF invar rec] by simp
  next
    case False
    then have "x = l ! a" 
      by (metis (no_types, lifting) One.hyps(3) One.hyps(7) One.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    then show ?thesis 
      using One.IH One.hyps(2,3) One.prems(1,2) explain_along_path_parent_eq by auto
  qed
next
  case (Two cc a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output2" pend2)
  then show ?case 
  proof(cases "a = rep_of l a")
    case True
    obtain o_rec l_rec p_rec where
 rec: "explain_along_path cc (l[rep_of l a := x]) x c = (o_rec, l_rec, p_rec)"
      using prod_cases3 by blast
    have invar: "explain_list_invar (l[rep_of l a := x]) (proof_forest cc)" 
      using explain_list_invar_step[OF Two(19)] Two(2,7) proof_forest_invar_def 
      by (metis Two.hyps(3) Two.prems(1) True explain_list_invar_def path_nodes_lt_length_l)
    have *: "rep_of l a \<noteq> rep_of l c" using explain_list_invar_def Two True 
      by (metis path_nodes_lt_length_l path_pf_same_rep path_root proof_forest_invar_def rep_of_root) 
    have "pend = [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ p_rec" 
      using explain_along_path_simp3[OF *] Two(7-) rec 
explain_along_path_domain[OF Two(2,19,3)] True 
      by auto
    then show ?thesis 
      using Two(18)[OF invar rec] by simp
  next
    case False
    then have "x = l ! a" 
      by (metis (no_types, lifting) Two.hyps(3) Two.hyps(7) Two.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    then show ?thesis 
      using Two.IH Two.hyps(2,3) Two.prems(1,2) explain_along_path_parent_eq 
      by (metis list_emb_append2)
  qed
qed
(*
lemma explain_along_path_explain_along_path2_equivalence:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
"explain_along_path2 cc a c = (output2, pend2)"
"explain_along_path cc l a c = (output, new_l, pend)"
shows "output2 - additional_uf_labels_set l (pf_labels cc) \<subseteq> output"
  sorry

lemma explain_along_path_new_l_labels_in_output:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
shows "additional_uf_labels_set new_l (pf_labels cc) - additional_uf_labels_set l (pf_labels cc) 
= output"
  sorry
*)

subsubsection \<open>Invariant of elements in the additional union find\<close>

text \<open>Invariant of \<open>explain_along_path\<close> that states that the recursive calls of explain are 
present in the total output\<close>

fun pending_equations_list :: "pending_equation option \<Rightarrow> (nat * nat) list"
  where
    "pending_equations_list None = []"
  | "pending_equations_list (Some (One a)) = []"
  | "pending_equations_list (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))) = [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)]"
  | "pending_equations_list (Some (Two a b)) = []"

function (domintros) was_already_in_pending where
"was_already_in_pending cc l [] pend = True"
| "was_already_in_pending cc l ((a, b) # xs) pend =
        ((a, b) \<in> set pend \<or> 
        (let c = lowest_common_ancestor (proof_forest cc) a b;
             (output1, pending1) = explain_along_path2 cc a c;
             (output2, pending2) = explain_along_path2 cc b c
         in (output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend
        )
     )
"
  by pat_completeness auto

(*maybe output of explain_along path 2 \<in> output and pending*)

thm was_already_in_pending.domintros
(*lemma that was_already_in_pending terminates if explain2 terminates*)
lemma explain2_dom_imp_was_already_in_pending_dom:
  assumes "cc_explain_aux2_dom (cc, xs)" "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
"\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
"cc_invar cc"
  shows "was_already_in_pending_dom (cc, l, xs, pend)"
using assms proof(induction rule: cc_explain_aux2.pinduct)
  case (1 cc)
  then show ?case 
    using was_already_in_pending.domintros by force
next
  case (2 cc a b xs)
  then have congruent: "are_congruent cc (a \<approx> b)" 
    by auto
  then have length: "a < length (proof_forest cc)" "b < length (proof_forest cc)"
    using 2(5,6) unfolding same_length_invar_def 
    by auto
  then have "rep_of (cc_list cc) a = rep_of (cc_list cc) b"
    using congruent are_congruent_simp by simp
  then have "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    using 2(6) length unfolding same_eq_classes_invar_def by blast
  define c where "c = lowest_common_ancestor (proof_forest cc) a b"
  then obtain p1 p2 where p: "path (proof_forest cc) c p1 a"
"path (proof_forest cc) c p2 b" using 2(5,6) lowest_common_ancestor_correct congruent
    unfolding proof_forest_invar_def same_length_invar_def 
    by (metis "2.prems"(3) explain_along_path_lowest_common_ancestor length(1) length(2))
  obtain output1 pending1 output2 pending2 where
          defs: "(output1, pending1) = explain_along_path2 cc a c"
             "(output2, pending2) = explain_along_path2 cc b c"
    by (metis old.prod.exhaust)
  then have 1: "\<forall> (a, b) \<in> set pending1 . are_congruent cc (a \<approx> b)"
"\<forall> (a, b) \<in> set pending2 . are_congruent cc (a \<approx> b)"
    using explain_along_path2_pending defs[symmetric] p 2(6) 
    by fastforce+
  have 3: "\<forall> (a, b) \<in> set pending1 . a < nr_vars cc \<and> b < nr_vars cc"
"\<forall> (a, b) \<in> set pending2 . a < nr_vars cc \<and> b < nr_vars cc"
    using explain_along_path2_pending_in_bounds defs[symmetric] p 2(6) 
    by fastforce+
  with 2(3) have 4: "\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)"
"\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
    using 1 2(4,5) 3 by auto
  then have "was_already_in_pending_dom (cc, l, pending1 @ pending2 @ xs, pend)" 
    using 2(2)[OF congruent c_def defs(1) _ defs(2) _ 4 2(6)] by blast
  then show ?case using was_already_in_pending.domintros c_def defs 2(5,6) 
    by (metis Pair_inject lowest_common_ancestor.simps)
qed

theorem was_already_in_pending_domain:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
  shows "was_already_in_pending_dom (cc, l, xs, pend)"
  using assms explain2_dom_imp_was_already_in_pending_dom cc_explain_aux2_domain 
  by blast

text \<open>Invariant\<close>

definition equations_of_l_in_pending_invar where
"equations_of_l_in_pending_invar cc l xs \<equiv>
  (\<forall> n a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b . n < length l \<longrightarrow> l ! n \<noteq> n 
    \<longrightarrow> (pf_labels cc) ! n = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))
    \<longrightarrow> was_already_in_pending cc l [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] xs
  )"

subsubsection \<open>Equivalence of \<open>cc_explain_aux\<close> and \<open>cc_explain_aux2\<close>\<close>

lemma cc_explain_aux_cc_explain_aux2_equivalence:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
    "equations_of_l_in_pending_invar cc l xs"
  shows "cc_explain_aux2 cc xs - additional_uf_labels_set l (pf_labels cc) \<subseteq>
cc_explain_aux cc l xs"
proof
  fix x 
  assume *: "x \<in> cc_explain_aux2 cc xs - additional_uf_labels_set l (pf_labels cc)"
  show "x \<in> cc_explain_aux cc l xs"
    using assms * proof(induction rule: cc_explain_aux_induct)
    case (base cc)
    then show ?case 
      by (simp add: cc_explain_aux2_simp1)
  next
    case (congruent cc l a b xs c output1 new_l pending1 output2 new_new_l pending2)
    have are_congruent: 
      "\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)"
      sorry
    from congruent obtain p1 p2 where path: "path (proof_forest cc) c p1 a"
      "path (proof_forest cc) c p2 b" 
      by (meson explain_along_path_lowest_common_ancestor )
    obtain output12 pending12 output22 pending22 where rec: 
      "explain_along_path2 cc a c = (output12, pending12)"
      "explain_along_path2 cc b c = (output22, pending22)"
      by (meson old.prod.exhaust)
    have "cc_explain_aux2_dom (cc, ((a, b) # xs))" 
      using cc_explain_aux2_domain congruent(2,4,5,6) by simp
    then have cc_explain_aux2: "cc_explain_aux2 cc ((a, b) # xs) = output12 \<union> output22 
\<union> cc_explain_aux2 cc (pending12 @ pending22 @ xs)" 
      using cc_explain_aux2_simp2 congruent.hyps(1,7,8) rec by auto
    have supset: "output12 \<supseteq> output1" "output22 \<supseteq> output2" sorry
    have add_uf_new_l: "additional_uf_labels_set new_new_l (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> output1 \<union> output2" sorry
    have "\<forall>(a, b)\<in>set xs. a < nr_vars cc \<and> b < nr_vars cc" 
      using congruent.hyps(3-5) congruent.prems(2) list_emb_set prod.inject set_ConsD by fastforce
    then have rec': "cc_explain_aux cc l ((a, b) # xs) =
output1 \<union> output2 \<union> cc_explain_aux cc new_new_l (pending1 @ pending2 @ xs)"
      using cc_explain_aux_simp2 congruent.hyps(1,10,7,8,9) by auto
    show ?case proof(cases "x \<in> output12 \<union> output22")
      case True
      have "output12 - output1 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)" 
        "output22 - output2 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)" 
        sorry
      then show ?thesis 
        using rec' supset add_uf_new_l True congruent.prems(3) by auto
    next
      case False
      have *: "x \<in> cc_explain_aux2 cc (pending12 @ pending22 @ xs) -
additional_uf_labels_set l (pf_labels cc)"
        using False cc_explain_aux2 congruent.prems(3) by simp
      have eq_cc_expl: "cc_explain_aux2 cc (pending12 @ pending22 @ xs) -
            additional_uf_labels_set new_new_l (pf_labels cc)
           \<subseteq> cc_explain_aux2 cc (pending1 @ pending2 @ xs) -
            additional_uf_labels_set new_new_l (pf_labels cc)" sorry
      have "equations_of_l_in_pending_invar cc new_new_l (pending1 @ pending2 @ xs)"
        sorry
      with eq_cc_expl show ?thesis 
        using * congruent.IH rec' are_congruent add_uf_new_l by auto
    qed
  next
    case (not_congruent cc l a b xs)
    then show ?case by simp
  qed
qed

theorem cc_explain_cc_explain2_equivalence:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc" "valid_vars (a \<approx> b) (nr_vars cc)"
  shows "cc_explain cc a b \<supseteq> cc_explain2 cc a b"
  sorry

subsection \<open>Correctness proof of \<open>cc_explain\<close>\<close>

theorem cc_explain_correctness:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc" "valid_vars (a \<approx> b) (nr_vars cc)"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain cc a b)"
proof- 
  have *: "(a \<approx> b) \<in> Congruence_Closure (cc_explain2 cc a b)"
  using cc_explain2_correctness cc_explain_cc_explain2_equivalence assms 
  by blast
  then have "cc_explain2 cc a b \<subseteq> cc_explain cc a b" 
    using cc_explain2_correctness cc_explain_cc_explain2_equivalence assms 
    by blast
  then show ?thesis using * 
    by (meson Congruence_Closure_monotonic in_mono)
qed

end
