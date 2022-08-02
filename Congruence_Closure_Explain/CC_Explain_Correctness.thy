section \<open>Correctness proof for Explain\<close>
theory CC_Explain_Correctness
  imports CC_Explain
begin 

subsection \<open>Correctness of \<open>explain_along_path\<close>\<close>

text \<open>This function is needed in order to interpret the pending list of the explain
operation as a set of equations.\<close>
fun pending_set_explain :: "(nat * nat) list \<Rightarrow> equation set"
  where
    "pending_set_explain pend = set (map (\<lambda>(a, b) . (a \<approx> b)) pend)"

lemma pending_set_explain_Cons:
  "pending_set_explain ((a, b) # pend) = {(a \<approx> b)} \<union> pending_set_explain pend"
  by auto

theorem explain_along_path_correctness:
  assumes "explain_along_path_dom (\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>, l, a, c)"
    (is "explain_along_path_dom (?cc, l, a, c)")
    "ufa_invar pf"
    "a < length pf"
    "c < length pf"
    "explain_along_path \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr> l a c = (output, new_l, pend)"
    "path pf c pAC a"
    "pf_labels_invar \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "explain_list_invar l pf"
  shows "(a \<approx> c) \<in> Congruence_Closure (representatives_set l \<union> output 
\<union> pending_set_explain pend)"
  using assms proof(induction "\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    l a c arbitrary: pAC "output" new_l pend rule: explain_along_path.pinduct)
  case (1 l a c)
  then have invar: "ufa_invar l" "length l = length pf"
    unfolding explain_list_invar_def by blast+ 
  then show ?case proof(cases "rep_of l a = rep_of l c")
    case True
    then have "(a \<approx> c) \<in> Congruence_Closure (representatives_set l)"
      using CC_same_rep_representatives_set[of l a c] 1 invar by argo
    then show ?thesis 
      using Congruence_Closure_split_rule by auto
  next
    case False
    let ?cc = "\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl,  input = ip\<rparr>"
    let ?union = "(l[rep_of l a := (pf ! rep_of l a)])"
    from False obtain output' new_l' pend' where recursive_step: "explain_along_path ?cc
     ?union (pf ! rep_of l a) c = (output', new_l', pend')"
      using prod_cases3 by blast
    obtain pRAC where pRAC: "pf ! rep_of l a \<noteq> rep_of l a \<and> path pf c pRAC (rep_of l a)" 
      using "1.prems" False assms(2) explain_list_invar_imp_valid_rep by blast
    from "1.prems" have "path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)"
      by (metis invar rep_of_bound rep_of_idem single)
    with "1.prems"  have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)" 
      by (metis invar False pRAC path_butlast rep_of_idem)
    obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
(pfl ! rep_of l a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! rep_of l a \<and> bb = rep_of l a \<or> aa = rep_of l a \<and> bb = pf ! rep_of l a)
        "using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
      by (meson pRAC path_nodes_lt_length_l)
    from "1.prems" have explain_list_invar: "explain_list_invar (l[rep_of l a := pf ! rep_of l a]) pf" 
      by (metis explain_list_invar_union invar(2) pRAC pRAC' path_nodes_lt_length_l rep_of_a_and_parent_rep_neq)
    have rep_neq: "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
      using pRAC "1.prems" False rep_of_a_and_parent_rep_neq invar by blast
    then have valid: "(pf ! rep_of l a) < length pf" "ufa_invar (l[rep_of l a := (pf ! rep_of l a)])"
      using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar invar apply (metis rep_of_bound)
      using ufa_invar_fun_upd' "1.prems" invar 
      by (metis rep_neq pRAC path_nodes_lt_length_l rep_of_idem ufa_invarD(2))
    have "(a \<approx> (rep_of l a)) \<in> Congruence_Closure (representatives_set l)"
      by (auto simp add: "1.prems" rep_of_iff invar)
    then have 4: "(a \<approx> (rep_of l a)) \<in> Congruence_Closure 
(representatives_set l \<union> output \<union> pending_set_explain pend)"
      using Congruence_Closure_split_rule by auto
        \<comment> \<open>If \<open>(pf ! rep_of l a) \<approx> c\<close> is in the congruence closure of the recursive call, 
        then it will also be in the congruence closure of the output.\<close>
    have cc_output: "((pf ! rep_of l a) \<approx> c) \<in>
 Congruence_Closure (representatives_set ?union \<union> output'
\<union> pending_set_explain pend')
\<Longrightarrow> ((pf ! rep_of l a) \<approx> (rep_of l a)) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend) 
\<Longrightarrow> output' \<subseteq> output
\<Longrightarrow> pending_set_explain pend' \<subseteq> pending_set_explain pend 
\<Longrightarrow> ((pf ! rep_of l a) \<approx> c) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend)"
    proof(rule Congruence_Closure_imp)
      fix eq
      assume prems: "eq \<in> representatives_set ?union \<union> output' \<union> pending_set_explain pend'"
        "((pf ! rep_of l a) \<approx> (rep_of l a))
         \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
        "output' \<subseteq> output" "pending_set_explain pend' \<subseteq> pending_set_explain pend"
      then consider (output_or_pending) "eq \<in> output' \<union> pending_set_explain pend'"
        | (rep_set) k where "eq = (k \<approx> rep_of ?union k)" "k < length ?union" "?union ! k \<noteq> k"
        by blast                      
      then show "eq \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
      proof(cases)
        case output_or_pending
        then show ?thesis
          using prems by blast
      next
        case rep_set
        then obtain pathRK where pathRK: "path ?union (rep_of ?union k) pathRK k"
          using valid(2) path_to_root_correct 
          using rep_set(2) by blast
        then show ?thesis proof(cases "rep_of l a = rep_of l k")
          case True
            \<comment> \<open>If they are in rep_set: in l: \<open>rep_of l a\<close> has the same rep as \<open>a\<close>,
                and \<open>pf ! rep_of l a\<close> has the same rep as \<open>rep_of ?union k\<close>, and 
                \<open>rep_of l a\<close> and \<open>a\<close> are congruent by assumption.\<close>
          then have "rep_of l (pf ! rep_of l a) = rep_of ?union k"
            using "1.prems" rep_set(2) rep_of_fun_upd valid(1) 
            using rep_neq rep_of_fun_upd_rep_of invar by force
          with "1.prems" invar have
            *: "((pf ! rep_of l a) \<approx> (rep_of ?union k))
\<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
            by (metis (no_types, lifting) Congruence_Closure.symmetric Congruence_Closure_split_rule a_eq_rep_of_a_in_CC_representatives_set(2) valid(1))
          then have
            "(k \<approx> (rep_of l a))
\<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
            by (metis (no_types, lifting) symmetric Congruence_Closure_split_rule True a_eq_rep_of_a_in_CC_representatives_set(2) length_list_update rep_set(2))
          with * show ?thesis 
            using prems by (metis (no_types, lifting) symmetric transitive1 rep_set(1))
        next
          case False
          with "1.prems" have "rep_of ?union k = rep_of l k" 
            using rep_of_fun_upd' rep_of_idem rep_set(2) invar by auto
          then show ?thesis 
            using symmetric Congruence_Closure_split_rule a_eq_rep_of_a_in_CC_representatives_set(2) rep_set by force
        qed 
      qed 
    qed
    show ?thesis proof(cases "the (pfl ! rep_of l a)")
      case (One a')
      from valid_eq have *: "pfl ! rep_of l a = Some (One a')" 
        using One by auto
      with recursive_step 1(2)[OF False] have IH: 
        "(pf ! rep_of l a \<approx> c) \<in>
 Congruence_Closure (representatives_set (l[rep_of l a := (pf ! rep_of l a)]) \<union> output'
\<union> pending_set_explain pend')" 
        using "1.prems" One pRAC' * valid explain_list_invar by simp
      have result: "(output, new_l, pend) = ({a'} \<union> output', new_l', pend')" 
        using 1 explain_along_path_simp2[OF False] One False * recursive_step by simp
      then have a': "a' = (rep_of l a \<approx> pf ! rep_of l a)
\<or> a' = (pf ! rep_of l a \<approx> rep_of l a)" 
        using One valid_eq by auto
      then have "(rep_of l a \<approx> pf ! rep_of l a) \<in> 
Congruence_Closure ({a'} \<union> output')" 
        by blast
      with result have 2: "(rep_of l a \<approx> pf ! rep_of l a) \<in> 
Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
        using Congruence_Closure_split_rule by (metis (no_types, lifting) Pair_inject sup_commute)
      from result have "output' \<subseteq> output"  "pending_set_explain pend' \<subseteq> pending_set_explain pend"
        by blast+
      with cc_output have 3: "(pf ! rep_of l a \<approx> c) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend)" 
        using "2" IH by blast
      from 2 3 4 show ?thesis by blast
    next
      case (Two x21 x22)
      then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where *: "(pfl ! rep_of l a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" 
        by (metis option.sel pending_equation.distinct(1) valid_eq) 
      with recursive_step 1(3)[OF False] have IH: 
        "(pf ! rep_of l a \<approx> c) \<in>
 Congruence_Closure (representatives_set ?union \<union> output'
\<union> pending_set_explain pend')" 
        using * pRAC' valid explain_list_invar "1.prems" by auto 
      have result: "(output, new_l, pend) = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', new_l', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
        using False invar congruence_closure.select_convs * recursive_step 1(1,7) explain_along_path_simp3
        by simp
      then have a': "a' = rep_of l a \<and> b' = pf ! rep_of l a
\<or> a' = pf ! rep_of l a \<and> b' = rep_of l a" 
        using valid_eq * by auto
      have "(a\<^sub>1 \<approx> b\<^sub>1) \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
        "(a\<^sub>2 \<approx> b\<^sub>2) \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
        "(F a\<^sub>1 a\<^sub>2 \<approx> a') \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
        "(F b\<^sub>1 b\<^sub>2 \<approx> b') \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
        using result by auto
      then have 2: "((rep_of l a) \<approx> (pf ! rep_of l a)) \<in> 
Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)" 
        using a' monotonic by blast
      from result have "representatives_set l \<union> output' \<union> pending_set_explain pend'
\<subseteq> representatives_set l \<union> output \<union> pending_set_explain pend" 
        using pending_set_explain_Cons by auto
      with cc_output have "((pf ! rep_of l a) \<approx> c) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend)"
        using Congruence_Closure_monotonic 2 result IH by auto
      then show ?thesis using 4 2 by blast
    qed
  qed
qed

fun pending_set' :: "pending_equation list \<Rightarrow> equation set"
  where
    "pending_set' [] = {}"
  | "pending_set' ((One a') # xs) = {a'} \<union> pending_set xs"
  | "pending_set' ((Two a' b') # xs) = {a', b'} \<union> pending_set xs"

lemma set_union_divide_lemma: "\<Union>{y | y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. k1 y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb }
\<union> \<Union>{y| y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. k2 y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb } = 
\<Union>{y | y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. k1 y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb  \<or> k2 y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb }" 
  by fast

lemma explain_along_path_output_pending_correct:
  assumes "cc_invar cc" 
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
  shows "fst (explain_along_path cc l a c) 
= \<Union>{pending_set' [the ((pf_labels cc) ! x)] | x. x \<in> set (tl p) \<and> l ! x = x}
\<and> set (snd (snd (explain_along_path cc l a c))) 
= \<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl p) \<and> l ! x = x
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}"
proof-
  from assms have "explain_along_path_dom (cc, l, a, c)" 
    using explain_along_path_domain by blast
  then show ?thesis
    using assms proof(induction cc l a c arbitrary: p rule: explain_along_path.pinduct)
    case (1 cc l a c)
    then have invar: "ufa_invar l" "length l = length (proof_forest cc)"
      unfolding explain_list_invar_def by blast+ 
    then show ?case 
    proof(cases "rep_of l a = rep_of l c")
      case True
      have ufa_invar: "ufa_invar l""ufa_invar (proof_forest cc)""ufa_invar (cc_list cc)"using "1.prems" 
        unfolding explain_list_invar_def  cc_list_invar_def proof_forest_invar_def
        by blast+
      have "path l c p a"
      proof-
        have pr: "path l (rep_of l a) (path_to_root l a) a"
          "path l (rep_of l c) (path_to_root l c) c"using path_to_root_correct "1.prems" ufa_invar 
          using invar path_nodes_lt_length_l by presburger+
        have prpf: "path (proof_forest cc) (rep_of l a) (path_to_root l a) a"
          "path (proof_forest cc) (rep_of l c) (path_to_root l c) c"

          using "1.prems"(2,3) explain_list_invar_paths pr by blast+
        have "path (proof_forest cc) (rep_of l c) (butlast(path_to_root l c) @ p) a"
          using "1.prems"(3) path_concat2 prpf(2) by auto
        with prpf path_unique True have "butlast(path_to_root l c) @ p = path_to_root l a" using ufa_invar 
          by auto
        have "p \<noteq> []" using "1.prems" path_not_empty 
          by auto
        with pr obtain k where "path l k p a" using path_divide2 
          by (metis \<open>butlast (path_to_root l c) @ p = path_to_root l a\<close>)
        then have "path (proof_forest cc) k p a" 
          using "1.prems"(2) explain_list_invar_paths by blast
        then have "k = c" using path_unique_if_length_eq "1.prems" invar 
          using ufa_invar(2) by blast
        then show ?thesis 
          using \<open>path l k p a\<close> by blast
      qed
      then have *: "x \<in> set (tl p) \<Longrightarrow> l ! x \<noteq> x" for x using path_contains_no_root "1.prems" 
        unfolding cc_list_invar_def 
        using invar(1) by blast
      have "fst (explain_along_path cc l a c) = {}"
        "set (snd (snd (explain_along_path cc l a c))) = {}" using True explain_along_path_simp1 
        by simp+
      then show ?thesis using * 
        by auto
    next
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
        "pRAC = (take (length p - length (path_to_root l a) + 1) p)"
        using "1.prems" False explain_list_invar_imp_valid_rep unfolding cc congruence_closure.select_convs
        by blast
      have "path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)"
        using "1.prems" unfolding cc congruence_closure.select_convs
        using explain_list_invar_def pRAC path_length_1 path_nodes_lt_length_l rep_of_idem by auto
      then have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)" 
        using "1.prems" unfolding cc congruence_closure.select_convs
        by (metis False pRAC(1) path_butlast path_length_1)
      obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
(pfl ! rep_of l a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! rep_of l a \<and> bb = rep_of l a \<or> aa = rep_of l a \<and> bb = pf ! rep_of l a)
        "using "1.prems" unfolding cc pf_labels_invar_def congruence_closure.select_convs
        by (meson pRAC path_nodes_lt_length_l)
      from "1.prems" invar have explain_list_invar: "explain_list_invar (l[rep_of l a := pf ! rep_of l a]) (proof_forest cc)" 
        unfolding cc congruence_closure.select_convs 
        by (metis (no_types, lifting) explain_list_invar_def explain_list_invar_union pRAC(1) pRAC' path_nodes_lt_length_l rep_of_a_and_parent_rep_neq)
      have rep_neq: "rep_of l a \<noteq> rep_of l (pf ! rep_of l a)"
        using pRAC "1.prems" False rep_of_a_and_parent_rep_neq unfolding cc congruence_closure.select_convs 
        using invar by blast
      then have valid: "(pf ! rep_of l a) < length pf" "ufa_invar (l[rep_of l a := (pf ! rep_of l a)])"
        using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar unfolding cc congruence_closure.select_convs 
        using pRAC' apply blast      using ufa_invar_fun_upd' "1.prems" unfolding cc congruence_closure.select_convs 
        using \<open>path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)\<close> explain_list_invar_def pRAC' path_length_1 path_nodes_lt_length_l rep_neq by auto

      have "l ! rep_of l a = rep_of l a" 
        using "1.prems" explain_list_invar_def path_nodes_lt_length_l rep_of_min by auto 
      have union_cases: "(x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x \<or> x = rep_of l a) \<longleftrightarrow> 
(x \<in> set (tl p) \<and> l ! x = x)" for x 
      proof
        assume prems: "(x \<in> set (tl (butlast pRAC)) 
\<and> l[rep_of l a := pf ! rep_of l a] ! x = x) \<or> x = rep_of l a"
        then show "x \<in> set (tl p) \<and> l ! x = x"
        proof(cases "x = rep_of l a")
          case True
          have "rep_of l a \<in> set (tl p)" 
          proof-
            from pRAC have 1: "rep_of l a \<in> set pRAC" 
              by (metis in_set_conv_decomp invar pRAC' path_nodes_lt_length_l path_snoc path_unique)
            then have 2:"rep_of l a \<in> set p" using pRAC 
              by (meson in_set_takeD)
            then have 3:"hd p = c" 
              using "1.prems"(3) path_hd by blast
            have "c \<noteq> rep_of l a" 
              using False \<open>path l (rep_of l (rep_of l a)) [rep_of l a] (rep_of l a)\<close> path_single by blast
            then show ?thesis using  1 2 3 
              by (simp add: not_hd_in_tl)
          qed
          then show ?thesis 
            by (simp add: True \<open>l ! rep_of l a = rep_of l a\<close>)
        next
          case False
          then have "x \<in> set (tl p)" 
            using prems unfolding pRAC 
            by (metis butlast_tl in_set_butlastD in_set_takeD tl_take)
          then show ?thesis 
            using False prems by auto
        qed
      next
        assume prems: "x \<in> set (tl p) \<and> l ! x = x"
        have "pRAC = take (length pRAC) p" using pRAC 
          by (metis length_take min_eq_arg(2) nat_le_linear take_all)
        then have pRAC2: "p = pRAC @ drop (length pRAC) p" unfolding pRAC 
          by (metis append_take_drop_id pRAC(2))
        let ?pRA = "last pRAC # drop (length pRAC) p"
        have *: "pRAC ~= []" using pRAC path_not_empty 
          by blast
        then have pRA: "path pf (rep_of l a) ?pRA a" using path_divide1 pRAC2 "1.prems"(3) cc 
          by (metis congruence_closure.select_convs(5) pRAC(1) path_last)
        then have pRA2: "path l (rep_of l a) (path_to_root l a) a" 
          using path_to_root_correct "1.prems" unfolding cc_list_invar_def 
          by (simp add: explain_list_invar_def path_nodes_lt_length_l)
        then have pRA3: "path pf (rep_of l a) (path_to_root l a) a" 
          using  "1.prems" explain_list_invar_paths cc by simp
        then have p_eq: "(path_to_root l a) = ?pRA " 
          using invar pRA path_unique by blast
        have *: " p =  (butlast pRAC) @ ?pRA" using pRAC2 * 
          by (metis Cons_eq_appendI append.assoc append_Nil append_butlast_last_id)
        have "butlast pRAC\<noteq> []"using pRAC' path_not_empty 
          by fast
        then have "tl p = (tl (butlast pRAC)) @ ?pRA" 
          by (metis "*" tl_append2)
        then have *: "x \<in> set (tl (butlast pRAC)) \<or>
x \<in> set ?pRA" using prems 
          by auto

        show "x \<in> set (tl (butlast pRAC)) 
\<and> l[rep_of l a := pf ! rep_of l a] ! x = x \<or> x = rep_of l a"
        proof(cases "x = rep_of l a")
          case False
          then show ?thesis proof(cases "x \<in> set (tl (butlast pRAC))")
            case True
            then show ?thesis 
              by (metis nth_list_update_neq prems)
          next
            case False': False
            then have "x \<in> set ?pRA" using * 
              by blast
            then have "x \<in> set (tl ?pRA)" using False 
              using pRAC(1) path_last by fastforce
            then obtain i where i: "?pRA ! i = x" "i < length ?pRA" 
              by (metis \<open>x \<in> set ?pRA\<close> in_set_conv_nth)
            have "hd ?pRA = rep_of l a " using pRA path_hd 
              by blast
            then have neq_zero: "i \<noteq> 0" using False i 
              by (metis list.sel(1) nth_Cons_0)
            with i have *: "
    (last pRAC # drop (length pRAC) p) ! (i - 1 + 1) = x"  "i - 1 < length (last pRAC # drop (length pRAC) p) - 1 "
              by auto
            then have *: "?pRA ! (i - 1) = l ! x" using prems 
                path_previous_node[OF pRA3[unfolded p_eq] *(2,1)] 
              by (metis pRA2 p_eq path_previous_node)
            have "ufa_invar l" 
              using "1.prems"(2) explain_list_invar_def by blast
            then have "path l (?pRA ! (i - 1)) [?pRA ! (i - 1), x] x" 
              using path_take_two neq_zero i pRA2 p_eq *
              by metis
            then have "False" using prems 
              by (metis not_Cons_self2 path.simps path_root)
            then show ?thesis by simp
          qed
        qed simp
      qed

      show ?thesis proof(cases "the (pfl ! rep_of l a)")
        case (One a')
        from valid_eq have *: "pfl ! rep_of l a = Some (One a')" 
          using One by auto
        have result: "explain_along_path cc l a c = ({a'} \<union> output', new_l', pend')" 
          using 1 explain_along_path_simp2[OF False] One False * recursive_step cc by simp 
        have "pf ! rep_of l a \<noteq> rep_of l a" 
          by (simp add: pRAC)
            \<comment> \<open>Output, case One\<close>
        then have a': "{a'} = pending_set' [the (pf_labels cc ! rep_of l a)]" 
          using "1.prems" using One valid_eq * cc
          by simp
        from 1(2)[OF False] One "1.prems" recursive_step cc explain_list_invar pRAC' valid 
        have IH: "output' =
    \<Union> {pending_set' [the (pf_labels cc ! x)] |x. x \<in> set (tl (butlast pRAC)) \<and> 
?union ! x = x}" 
          by auto
        from * union_cases have union: "\<Union> {pending_set' [the (pf_labels cc ! x)] |x. x \<in> set (tl p) \<and> l ! x = x}
= (\<Union> {pending_set' [the (pf_labels cc ! x)] |x. x \<in> set (tl (butlast pRAC))  \<and> ?union ! x = x})
\<union> pending_set' [the (pf_labels cc ! rep_of l a)]"
          by blast
            \<comment> \<open>Pending, case One\<close>
        from 1(2)[OF False] One "1.prems" recursive_step cc explain_list_invar pRAC' valid
        have IH_p: "set pend' =
        \<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}" 
          by auto
        from union_cases have union_cases_p: 
          "x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))
\<longleftrightarrow> 
(x \<in> set (tl p) \<and> l ! x = x \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))" 
          for x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb
          using * cc 
          by (metis congruence_closure.select_convs(6) option.inject pending_equation.distinct(1))
        with *  have union_p: 
          "\<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl p) \<and> l ! x = x
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}
= \<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}" 
          by simp

        show ?thesis 
          using  a' IH IH_p cc result union union_p by auto 
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
            \<comment> \<open>Output, case Two\<close>
        then have a': "{(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} = pending_set' [the (pf_labels cc ! rep_of l a)]" 
          unfolding cc  congruence_closure.select_convs Two pending_set'.simps
          using Two * by auto
        from 1(3)[OF False] Two * "1.prems" recursive_step cc explain_list_invar pRAC' valid 
        have IH: "output' =
    \<Union> {pending_set' [the (pf_labels cc ! x)] |x. x \<in> set (tl (butlast pRAC)) \<and> 
?union ! x = x}" 
          by simp
        with Two * union_cases have union: "\<Union> {pending_set' [the (pf_labels cc ! x)] |x. x \<in> set (tl p) \<and> l ! x = x}
= (\<Union> {pending_set' [the (pf_labels cc ! x)] |x. x \<in> set (tl (butlast pRAC))  \<and> ?union ! x = x})
\<union> pending_set' [the (pf_labels cc ! rep_of l a)]"
          by blast
            \<comment> \<open>Pending, case Two\<close>
        then have pend': "{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} \<union> set pend' = set (snd (snd (explain_along_path cc l a c)))" 
          using result by simp
        from 1(3)[OF False] Two * "1.prems" recursive_step cc explain_list_invar pRAC' valid
        have IH_p: "set pend' =
    \<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}" 
          by simp
        from union_cases have union_cases_p: 
          "(x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
\<or> (x = rep_of l a \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
\<longleftrightarrow> 
(x \<in> set (tl p) \<and> l ! x = x \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))" 
          for x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb
          using * unfolding cc congruence_closure.select_convs 
          by blast
        with Two * have  
          2: "\<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl p) \<and> l ! x = x
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}
= \<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))
\<or> x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}"
          by simp
        have 3: 
          "\<Union>{y | y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))\<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}}
\<union> \<Union>{y| y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))\<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}}
=
\<Union>{y | y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)) \<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}
\<or> x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))
\<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}}" 
          using set_union_divide_lemma .
        have 4:"\<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))
\<or> x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}

= 

\<Union>{y | y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)) \<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}
\<or> x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))
\<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}}
"
          by blast

        have 5:"\<Union>{y | y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))\<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}}
=
\<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x \<in> set (tl (butlast pRAC)) \<and> ?union ! x = x
    \<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}"    
          "\<Union>{y| y x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))\<and> y = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}}
= \<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))}"
          by blast+
        have 6: "\<Union>{{(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)} | x a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 bb. x = rep_of l a
\<and> ((pf_labels cc) ! x) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))} = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}"
          using * cc by simp
        show ?thesis 
          using  a' IH IH_p cc result union 2 3 4 5 6 by auto
      qed
    qed 
  qed
qed


text \<open>This invar shows the correctness of the explain function.
      We can't directly show that it's correct, because the correctness of it
      depends on how exactly the proof forest was built, aka in a way that the 
      algorithms can terminate and the proofs of two different edges do not 
      depend on each other.\<close>

definition cc_explain_correctness_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "cc_explain_correctness_invar cc \<equiv> (\<forall> l eqs.
explain_list_invar l (proof_forest cc)
\<longrightarrow>  (\<forall> (a, b) \<in> set eqs . a < nr_vars cc \<and> b < nr_vars cc) 
\<longrightarrow>
  (\<forall> (a, b) \<in> set eqs .
    are_congruent cc (a \<approx> b) \<longrightarrow>
    (a \<approx> b) \<in> Congruence_Closure (cc_explain_aux cc l eqs \<union> representatives_set l))
)"

lemma cc_explain_correctness_invar':
  assumes "cc_explain_correctness_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "(\<forall> (a, b) \<in> set eqs . a < nr_vars cc \<and> b < nr_vars cc)"
    "(a, b) \<in> set eqs"
    "are_congruent cc (a \<approx> b)"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain_aux cc l eqs \<union> representatives_set l)"
  using assms unfolding cc_explain_correctness_invar_def by blast


subsection \<open>Correctness invar of \<open>cc_explain\<close>\<close>

lemma path_invariant_after_add_edge:
  assumes "c = lowest_common_ancestor pf a b"
    "c' = lowest_common_ancestor (add_edge pf e e') a b"
    "path pf c pAC a" "path pf c pBC b"  
    "path (add_edge pf e e') c' pAC' a" "path (add_edge pf e e') c' pBC' b" 
    "ufa_invar pf" "e < length pf" "e' < length pf" "rep_of pf e \<noteq> rep_of pf e'"
  shows
    "\<Union>{pending_set' [the (pfl ! x)] | x. x \<in> set (tl pAC) \<and> l ! x = x}
\<union> \<Union>{pending_set' [the (pfl ! x)] | x. x \<in> set (tl pBC) \<and> l ! x = x}
= \<Union>{pending_set' [the ((add_label pfl pf e lbl) ! x)] | x. x \<in> set (tl pAC') \<and> l ! x = x}
\<union> \<Union>{pending_set' [the ((add_label pfl pf e lbl) ! x)] | x. x \<in> set (tl pBC') \<and> l ! x = x}"
    (is "?base = ?step")
proof-
  have dom: "add_label_dom (pfl, pf, e, lbl)"
    using add_label_domain assms by blast
  from dom assms show "?base = ?step"
  proof(induction rule: add_label.pinduct)
    case (1 pfl pf e lbl)
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      with "1.prems" have "add_label pfl pf e lbl = (pfl[e := Some lbl])" 
        using "1.hyps" add_label.psimps by auto
      have dom': "add_edge_dom (pf, e, e')"
        using add_edge_domain "1.prems" by blast
      with "1.prems"  have "add_edge pf e e' = (pf[e := e'])" 
        using "1.hyps" add_edge.psimps True by presburger
      have "ufa_invar (add_edge pf e e')" 
        by (simp add: "1.prems" add_edge_ufa_invar_invar)
      have "e \<notin> set (tl pAC)" "e \<notin> set (tl pBC)" 
        using "1.prems" True path_contains_no_root by blast+
      then have paths: "path (pf[e := e']) c pAC a" "path (pf[e := e']) c pBC b"  
        by (auto simp add: "1.prems"(3-) path_fun_upd)
      from "1.prems" have "c = c'" using lowest_common_ancestor_fun_upd
        by (metis True \<open>add_edge pf e e' = pf[e := e']\<close> path_nodes_lt_length_l path_rep_eq)
      then have "pAC = pAC'"  "pBC = pBC'" 
        using "1.prems" \<open>add_edge pf e e' = pf[e := e']\<close> paths \<open>ufa_invar (add_edge pf e e')\<close> path_unique by auto
      have "x \<noteq> e \<Longrightarrow> pfl ! x = add_label pfl pf e lbl ! x" for x 
        by (simp add: \<open>add_label pfl pf e lbl = pfl[e := Some lbl]\<close>)
      then show ?thesis 
        by (smt (verit, best) Collect_cong \<open>e \<notin> set (tl pAC)\<close> \<open>e \<notin> set (tl pBC)\<close> \<open>pAC = pAC'\<close> \<open>pBC = pBC'\<close> )
    next
      case False
      have IH: 
        "\<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pAC) \<and> l ! x = x} \<union>
    \<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pBC) \<and> l ! x = x}
    = \<Union> {pending_set' [the (add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)) ! x)] |x.
          x \<in> set (tl pAC') \<and> l ! x = x} \<union>
       \<Union> {pending_set' [the (add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)) ! x)] |x.
           x \<in> set (tl pBC') \<and> l ! x = x}"
        sorry
      have 2: "\<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pAC) \<and> l ! x = x} \<union>
    \<Union> {pending_set' [the (pfl[e := Some lbl] ! x)] |x. x \<in> set (tl pBC) \<and> l ! x = x}
= \<Union> {pending_set' [the (pfl ! x)] |x. x \<in> set (tl pAC) \<and> l ! x = x} \<union>
    \<Union> {pending_set' [the (pfl ! x)] |x. x \<in> set (tl pBC) \<and> l ! x = x}"
        sorry
      from False have "add_label pfl pf e lbl = add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e))"
        by (simp add: "1.hyps" add_label.psimps)
      then show ?thesis using False 2 IH by simp
    qed
  qed
qed

lemma cc_explain_correctness_invar_mini_step:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr>" 
    "cc_explain_correctness_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    (is "cc_explain_correctness_invar ?base")
    "validity_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf,
 pf_labels = pfl, input = ip\<rparr>"
  shows "cc_explain_correctness_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
    (is "cc_explain_correctness_invar ?step")
  unfolding cc_explain_correctness_invar_def
proof(standard, standard, standard, standard, standard, standard, standard)
  fix la eqs x aa ba
  assume prems: "explain_list_invar la (proof_forest ?step)"
    "\<forall>(aa, ba)\<in>set eqs. aa < nr_vars ?step \<and> ba < nr_vars ?step"
    "x \<in> set eqs" "x = (aa, ba)" 
    "are_congruent ?step (aa \<approx> ba)"
  then have explain_list_invar_base: "explain_list_invar la (proof_forest ?base)" 
    "nr_vars ?step = nr_vars ?base"
    unfolding congruence_closure.select_convs sorry
  then show "(aa \<approx> ba) \<in> Congruence_Closure (cc_explain_aux ?step la eqs \<union> representatives_set la)"
  proof(cases "are_congruent ?base (aa \<approx> ba)")
    case True
    then have 
      "(aa \<approx> ba) \<in> Congruence_Closure (cc_explain_aux ?base la eqs \<union> representatives_set la)"
      using assms cc_explain_correctness_invar' explain_list_invar_base prems 
      by simp
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

subsubsection \<open>Initial cc\<close>

lemma are_congruent_initial_cc:
  assumes "valid_vars (a \<approx> b) n" "are_congruent (initial_cc n) (a \<approx> b)"  
  shows "a = b"
proof-
  from assms have *: "rep_of (cc_list (initial_cc n)) a = rep_of (cc_list (initial_cc n)) b"
    by fastforce
  with assms(1) have "rep_of (cc_list (initial_cc n)) a = a"
    "rep_of (cc_list (initial_cc n)) b = b"
    using rep_of_refl by auto
  with * show ?thesis 
    by argo
qed

theorem cc_explain_correctness_invar_initial_cc: 
  "cc_explain_correctness_invar (initial_cc n)"
  unfolding cc_explain_correctness_invar_def
proof(standard, standard, standard, standard, standard, standard, standard)
  fix l eqs x a b
  assume "explain_list_invar l (proof_forest (initial_cc n))"
    "\<forall>(a, b)\<in>set eqs.
          a < nr_vars (initial_cc n) \<and> b < nr_vars (initial_cc n)"
    "x \<in> set eqs"
    "x = (a, b)"
    "are_congruent (initial_cc n) (a \<approx> b)"
  then have "a = b" using are_congruent_initial_cc 
    by auto
  then show "(a \<approx> b)
       \<in> Congruence_Closure
           (cc_explain_aux (initial_cc n) l eqs \<union> representatives_set l)" 
    by blast
qed

subsection \<open>Correctness of \<open>cc_explain\<close>\<close>

theorem cc_explain_correct:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc" "valid_vars (a \<approx> b) (nr_vars cc)"
    "cc_explain_correctness_invar cc"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain cc a b)"
proof-
  have "explain_list_invar [0..<nr_vars cc] (proof_forest cc)"
    using explain_list_invar_initial assms(2) unfolding inv_same_length_def by metis
  moreover have "(\<forall>(a, b)\<in>set [(a, b)]. a < nr_vars cc \<and> b < nr_vars cc)"
    using assms by auto
  moreover have "(a, b) \<in> set [(a, b)]" by simp
  ultimately have *: "(a \<approx> b) \<in> Congruence_Closure 
(cc_explain_aux cc [0..<nr_vars cc] [(a, b)] \<union> representatives_set [0..<nr_vars cc])"
    using assms unfolding cc_explain_correctness_invar_def by blast
  then have "representatives_set [0..<nr_vars cc] = {}"
    by simp
  then show ?thesis 
    by (metis "*" Un_empty_right)
qed
