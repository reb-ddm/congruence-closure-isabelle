theory CC_Explain2_Correctness
  imports CC_Explain2_Termination
begin 



section \<open>Correctness proof of \<open>cc_explain2\<close>\<close>

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

lemma cc_explain_aux2_correctness:
  assumes "cc_invar_t cc_t"
    "\<forall>(a, b)\<in>set xs. a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "(x, y) \<in> set xs" "are_congruent cc (x \<approx> y)"
    "\<forall>(a, b)\<in>set xs. are_congruent cc (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
  shows "(x \<approx> y) \<in> Congruence_Closure (cc_explain_aux2 cc xs)"
proof-
  have "cc_explain_aux2_dom (cc, xs)"
    using cc_explain_aux2_domain assms by blast
  then show ?thesis 
    using assms proof(induction arbitrary: x y rule: cc_explain_aux2.pinduct)
    case (2 cc a b xs)
    have cc: "length (cc_list cc_t) = nr_vars cc" "cc_invar cc" using 2(4)
      unfolding congruence_closure.truncate_def congruence_closure.select_convs 2(9) by auto
    then show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"
      then obtain p1 p2 where p: "path (proof_forest cc) c p1 a"
        "path (proof_forest cc) c p2 b" using assms(2-) cc unfolding proof_forest_invar_def 
        using cc "2.prems"(2) True case_prod_conv explain_along_path_lowest_common_ancestor
        by (metis list.set_intros(1))      
      obtain output1 pending1 output2 pending2 
        where
          eap: "(output1, pending1) = explain_along_path2 cc a c"
          "(output2, pending2) = explain_along_path2 cc b c"
        by (metis old.prod.exhaust)
      have "\<forall>a\<in>set pending1. case a of (a, b) \<Rightarrow> 
 are_congruent cc (a \<approx> b)"
        "\<forall>a\<in>set pending2. case a of (a, b) \<Rightarrow> 
 are_congruent cc (a \<approx> b)"
        using explain_along_path2_pending eap p cc 
        by (metis case_prodI2 pending_set_explain_set)+
      then have pend: "\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> 
 are_congruent cc (a \<approx> b)" 
        using 2(8) cc by fastforce
have "\<forall>a\<in>set pending1. case a of (a, b) \<Rightarrow> 
a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall>a\<in>set pending2. case a of (a, b) \<Rightarrow> 
a < nr_vars cc \<and> b < nr_vars cc"
        using explain_along_path2_pending_in_bounds eap p cc
        by (metis)+
      then have pend2: "\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> 
a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)" 
        using 2(5) cc by fastforce
      have pend3: "\<forall>x \<in> pending_set_explain pending1.  
are_congruent cc x" "\<forall>x \<in> pending_set_explain pending2.  
are_congruent cc x" using explain_along_path2_pending eap p cc
        by (metis)+
      have less: "a < nr_vars cc" "b < nr_vars cc" 
        using 2(5) cc by fastforce+
      then have "c < nr_vars cc"  using cc unfolding same_length_invar_def 
        by (metis p(2) path_nodes_lt_length_l)
      have recursive: "cc_explain_aux2 cc ((a, b) # xs)
= output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs)"
        by (simp add: "2.hyps" cc_explain_aux2_simp2 True c_def eap(1) eap(2))
      have IH: "\<forall> a b. (a \<approx> b) \<in> pending_set_explain pending1 \<longrightarrow> are_congruent cc (a \<approx> b)
\<longrightarrow> (a \<approx> b) \<in> Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        "\<forall> a b. (a \<approx> b) \<in> pending_set_explain pending2 \<longrightarrow> are_congruent cc (a \<approx> b)
\<longrightarrow> (a \<approx> b) \<in> Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        using 2(2) True c_def eap 2(4-9) pend pend2  
        by auto
      have subsets: "pending_set_explain pending1 \<subseteq> 
Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        "pending_set_explain pending2 \<subseteq> 
Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
        using IH pend2 apply auto[1] using IH(2) pend3 by auto
      then show ?thesis using 2 
      proof(cases "(x, y) = (a, b)")
        case True
        have "(a \<approx> c) \<in> Congruence_Closure (output1 \<union> pending_set_explain pending1)"
          "(b \<approx> c) \<in> Congruence_Closure (output2 \<union> pending_set_explain pending2)"
          using explain_along_path2_correctness' p less eap using cc by auto
        then have "(a \<approx> c) \<in> Congruence_Closure (output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
          "(b \<approx> c) \<in> Congruence_Closure (output1 \<union> output2 \<union> cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
          using Congruence_Closure_split_rule subsets 
          by (smt (z3) Congruence_Closure_imp Un_commute Un_iff subset_eq)+
        then show ?thesis using recursive 
          by (metis Congruence_Closure.symmetric Congruence_Closure.transitive1 True prod.inject)
      next
        case False
        then have "(x \<approx> y) \<in> Congruence_Closure (cc_explain_aux2 cc (pending1 @ pending2 @ xs))"
          using 2(2)[OF True c_def] eap 2(4,6,8,9) pend pend2 
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
  assumes "are_congruent cc (a \<approx> b)" "cc_invar_t cc_t" "valid_vars (a \<approx> b) (nr_vars cc)"
"cc = congruence_closure.truncate cc_t"
shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain2 cc a b)"
proof-
 have cc: "length (cc_list cc_t) = nr_vars cc" "cc_invar cc" using assms(2)
   unfolding congruence_closure.truncate_def congruence_closure.select_convs assms(4) by auto
  then have "a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)" 
   using assms valid_vars.simps by simp
  then show ?thesis 
    using cc_explain_aux2_correctness[OF assms(2)] valid_vars.simps assms by auto
qed

end