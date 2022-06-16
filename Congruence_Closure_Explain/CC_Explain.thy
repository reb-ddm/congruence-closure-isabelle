section \<open>Explain for Congruence Closure\<close>
theory CC_Explain
  imports CC_Invars 
begin 

subsection \<open>Explain definition\<close>

text \<open>The "highest node" is in this case the same as the rep_of, because we do not 
      have the optimisation of checking which equivalence class is bigger, 
      we just make the union in the given order. When adding this optimisation,
      a highest_node function must be also implemented. \<close>

text \<open>There are three variables changed by the function \<open>explain_along_path\<close>: 

    * The overall output of explain
    * The Union Find list of the additional union find, which is local to the explain function
    * The list of pending proofs, which need to be recursively called with cc_explain
      
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
          (let (output, new_l, pending) = explain_along_path cc (ufa_union l a b) b c
          in ({a'} \<union> output, new_l, pending))
        | Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b') \<Rightarrow> 
          (let (output, new_l, pending) = explain_along_path cc (ufa_union l a b) b c
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
    "(output, new_l, pend) = explain_along_path cc (ufa_union l a ((proof_forest cc) ! rep_of l a)) 
     ((proof_forest cc) ! rep_of l a) c"
    "explain_along_path_dom (cc, l, a, c)"
  shows "explain_along_path cc l a c = ({a'} \<union> output, new_l, pend)"
 using explain_along_path.psimps unfolding Let_def
    by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(5))


lemma explain_along_path_simp3:
  assumes "rep_of l a \<noteq> rep_of l c"
    "(pf_labels cc) ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))"
    "explain_along_path cc (ufa_union l a ((proof_forest cc) ! rep_of l a)) 
     ((proof_forest cc) ! rep_of l a) c = (output, new_l, pend)"
    "explain_along_path_dom (cc, l, a, c)"
  shows "explain_along_path cc l a c = ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, 
         new_l, [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend)"
  using explain_along_path.psimps unfolding Let_def
    by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(6) equation.simps(6))

function cc_explain_aux :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> (nat * nat) list \<Rightarrow> equation set"
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
else cc_explain_aux cc l xs)
"
  by pat_completeness auto

fun cc_explain :: "congruence_closure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> equation set"
  where
"cc_explain cc a b = cc_explain_aux cc [0..<nr_vars cc] [(a, b)]"

text \<open>TODO: To show about pfl: left a = i and right a = pf ! i or opposite
also it's never None if pf ! i ~= i.\<close>

subsection \<open>Correctness of \<open>explain_along_path\<close>\<close>

text \<open>This function is needed in order to interpret the pending list of the explain
operation as a set of equations.\<close>
fun pending_set_explain :: "(nat * nat) list \<Rightarrow> equation set"
  where
    "pending_set_explain pend = set (map (\<lambda>(a, b) . (a \<approx> b)) pend)"

lemma pending_set_explain_Cons:
  "pending_set_explain ((a, b) # pend) = {(a \<approx> b)} \<union> pending_set_explain pend"
  by auto

lemma explain_along_path_correctness:
  assumes "explain_along_path_dom (\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>, l, a, c)"
(is "explain_along_path_dom (?cc, l, a, c)")
    "ufa_invar pf"
    "a < length pf"
    "c < length pf"
    "ufa_invar l"
    "length l = length pf"
    "explain_along_path \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr> l a c = (output, new_l, pend)"
"path pf c pAC a"
"pf_labels_invar \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "(a \<approx> c) \<in> Congruence_Closure (representatives_set l \<union> output 
\<union> pending_set_explain pend)"
  using assms proof(induction "\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    l a c arbitrary: pAC "output" new_l pend rule: explain_along_path.pinduct)
  case (1 l a c)
  then show ?case proof(cases "rep_of l a = rep_of l c")
    case True
    then have "(a \<approx> c) \<in> Congruence_Closure (representatives_set l)"
      using CC_same_rep_representatives_set[of l a c] 1 by argo
    then show ?thesis 
      using Congruence_Closure_split_rule by auto
  next
    case False
    obtain output' new_l' pend' where recursive_step: "explain_along_path ?cc
     (ufa_union l a (pf ! rep_of l a)) (pf ! rep_of l a) c = (output', new_l', pend')"
      using prod_cases3 by blast
    have valid: "(pf ! rep_of l a) < length pf" "ufa_invar (ufa_union l a (pf ! rep_of l a))"
      using "1.prems" path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar by (metis rep_of_bound)+
    have "(a \<approx> (rep_of l a)) \<in> Congruence_Closure (representatives_set l)"
      by (auto simp add: "1.prems" rep_of_iff)
    then have 4: "(a \<approx> (rep_of l a)) \<in> Congruence_Closure 
(representatives_set l \<union> output \<union> pending_set_explain pend)"
      using Congruence_Closure_split_rule by auto
    \<comment> \<open>If \<open>(pf ! rep_of l a) \<approx> c\<close> is in the congruence closure of the recursive call, 
        then it will also be in the congruence closure of the output.\<close>
    let ?union = "(ufa_union l a (pf ! rep_of l a))"
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
          using valid(2) path_to_root_correct by blast
        then show ?thesis proof(cases "rep_of l a = rep_of l k")
          case True
            \<comment> \<open>If they are in rep_set: in l: \<open>rep_of l a\<close> has the same rep as \<open>a\<close>,
                and \<open>pf ! rep_of l a\<close> has the same rep as \<open>rep_of ?union k\<close>, and 
                \<open>rep_of l a\<close> and \<open>a\<close> are congruent by assumption.\<close>
          then have "rep_of l (pf ! rep_of l a) = rep_of ?union k"
            using "1.prems" rep_set(2) ufa_union_aux valid(1) by auto
          with "1.prems" have
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
            by (metis length_list_update rep_set(2) ufa_union_aux valid(1))
          then show ?thesis 
            using symmetric Congruence_Closure_split_rule a_eq_rep_of_a_in_CC_representatives_set(2) rep_set by force
        qed 
      qed 
    qed
    obtain pRAC where pRAC: "path pf c pRAC (rep_of l a)"sorry
    then have pRAC': "path pf c (butlast pRAC) (pf ! rep_of l a)"
        by (metis "1.prems"(2) "1.prems"(4) "1.prems"(5) False path_butlast rep_of_idem)
      from pRAC have "pf ! rep_of l a \<noteq> rep_of l a" using "1.prems"(7)
        by (metis "1.prems"(2) "1.prems"(4) "1.prems"(5) False path_root rep_of_min rep_of_refl)
      then obtain aa a\<^sub>1 a\<^sub>2 bb b\<^sub>1 b\<^sub>2 where valid_eq: "
(pfl ! rep_of l a = Some (One (aa \<approx> bb)) \<or> 
          pfl ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb)))
          \<and> (aa = pf ! rep_of l a \<and> bb = rep_of l a \<or> aa = rep_of l a \<and> bb = pf ! rep_of l a)
        "using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs(*3*) 
        by (metis rep_of_less_length_l)
    show ?thesis proof(cases "the (pfl ! rep_of l a)")
      case (One a')
      from valid_eq have *: "pfl ! rep_of l a = Some (One a')" 
        using One by auto
      with recursive_step 1(2)[OF False] have IH: 
        "(pf ! rep_of l a \<approx> c) \<in>
 Congruence_Closure (representatives_set (ufa_union l a (pf ! rep_of l a)) \<union> output'
\<union> pending_set_explain pend')" 
        using "1.prems" One valid pRAC' by simp
      have result: "(output, new_l, pend) = ({a'} \<union> output', new_l', pend')" 
        using 1 explain_along_path_simp2[OF False] One False * recursive_step by auto
      then have a': "a' = (rep_of l a \<approx> pf ! rep_of l a)
\<or> a' = (pf ! rep_of l a \<approx> rep_of l a)" 
        using One valid_eq by auto
      then have "(rep_of l a \<approx> pf ! rep_of l a) \<in> 
Congruence_Closure ({a'} \<union> output')" 
        by blast
      with result have 2: "(rep_of l a \<approx> pf ! rep_of l a) \<in> 
Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
        using Congruence_Closure_split_rule by (metis (no_types, lifting) Pair_inject sup_commute)
      from result have "output' \<subseteq> output"  "pending_set_explain pend' \<subseteq> pending_set_explain pend "
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
 Congruence_Closure (representatives_set (ufa_union l a (pf ! rep_of l a)) \<union> output'
\<union> pending_set_explain pend')" 
        using * pRAC' by (simp add: "1.prems" Two valid)
      have result: "(output, new_l, pend) = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', new_l', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
        using 1 explain_along_path_simp3[OF False] * recursive_step by auto
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


subsection \<open>Correctness of explain\<close>

lemma cc_explain_aux_correct:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain_aux cc ([0..<nr_vars cc]) [(a, b)])"
  sorry

lemma cc_explain_correct:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc"
  shows "(a \<approx> b) \<in> Congruence_Closure (cc_explain cc a b)"
  sorry

lemma cc_explain_valid:
  assumes "are_congruent cc (a \<approx> b)" "cc_invar cc"
  shows "cc_explain cc a b \<subseteq> input cc"
  sorry

end