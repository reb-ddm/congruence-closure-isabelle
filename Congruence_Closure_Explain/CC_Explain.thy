section \<open>Explain for Congruence Closure\<close>
theory CC_Explain
  imports CC_Invars 
begin 

subsection \<open>Explain definition\<close>

text \<open>The highest node is in this case the same as the rep_of, because we do not 
      have the optimisation of checking which equivalence class is bigger, 
      we just make the union in the given order. When adding this optimisation,
      a highest_node function must be also implemented. \<close>

text \<open>There are three variables changed by the function \<open>explain_along_path\<close>: 

      The overall output of explain
      The Union Find list of the additional union find, which is local to the explain function
      The list of pending proofs, which need to be recursively called with cc_explain
      
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
  shows "explain_along_path cc l a c = ({a'} \<union> output, new_l, pend)"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path.domintros sorry
  then show ?thesis using explain_along_path.psimps unfolding Let_def
    by (metis (no_types, lifting) assms case_prod_conv option.sel pending_equation.simps(5))
qed

lemma explain_along_path_simp3:
  assumes "rep_of l a \<noteq> rep_of l c"
    "(pf_labels cc) ! rep_of l a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))"
    "explain_along_path cc (ufa_union l a ((proof_forest cc) ! rep_of l a)) 
     ((proof_forest cc) ! rep_of l a) c = (output, new_l, pend)"
  shows "explain_along_path cc l a c = ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, 
         new_l, [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend)"
proof-
  have "explain_along_path_dom (cc, l, a, c)"
    using assms explain_along_path.domintros sorry
  then show ?thesis using explain_along_path.psimps unfolding Let_def
    using assms case_prod_conv option.sel pending_equation.simps(6) equation.simps(6) 
    by (metis (no_types, lifting))
qed

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

subsection \<open>Invariant for the additional union find in cc_explain\<close>

definition explain_list_invar :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
\<comment> \<open>They have the same rep\<close>
"explain_list_invar l pf \<equiv> (\<forall> i < length l. l ! i \<noteq> i \<longrightarrow> l ! i = pf ! i) \<and> 
(length l = length pf)"

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
"explain_list_invar [0..<n] [0..<n]"
  unfolding explain_list_invar_def by blast

lemma explain_list_invar_union:
  assumes "explain_list_invar l pf" "a < length l"
  shows "explain_list_invar (ufa_union l a (pf ! rep_of l a)) pf"
  unfolding explain_list_invar_def 
proof(standard, standard, standard, standard)
  fix i
  assume prems: "i < length (ufa_union l a (pf ! rep_of l a))"
"ufa_union l a (pf ! rep_of l a) ! i \<noteq> i"
  show "ufa_union l a (pf ! rep_of l a) ! i = pf ! i"
  proof(cases "i = rep_of l a")
    case True
    have "rep_of l a < length l" 
      using True prems(1) by auto
    with True have "ufa_union l a (pf ! rep_of l a) ! i = rep_of l (pf ! rep_of l a)" 
      by simp
    then show ?thesis sorry
  next
    case False
    then show ?thesis using assms(1) prems unfolding explain_list_invar_def by simp
  qed
next 
  show "length (ufa_union l a (pf ! rep_of l a)) = length pf" 
    using assms(1) unfolding explain_list_invar_def by simp
qed

lemma explain_list_invar_explain_along_path:
"True"
  sorry

text "To show about pfl: left a = i and right a = pf ! i or opposite
also it's never None if pf ! i ~= i."

subsection \<open>Correctness of \<open>explain_along_path\<close>\<close>
fun pending_set_explain :: "(nat * nat) list \<Rightarrow> equation set"
  where
    "pending_set_explain pend = set (map (\<lambda>(a, b) . (a \<approx> b)) pend)"

lemma pending_set_explain_Cons:
  "pending_set_explain ((a,b) # pend) = {(a \<approx> b)} \<union> pending_set_explain pend"
  by auto

lemma explain_along_path_correctness:
  assumes "ufa_invar pf"
    "a < length pf"
    "c < length pf"
    "ufa_invar l"
    "path pf c pAC a"
    "length l = length pf"
    "explain_along_path \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr> l a c = (output, new_l, pend)"
  shows "(a \<approx> c) \<in> Congruence_Closure (representatives_set l \<union> output 
\<union> pending_set_explain pend)"
  using assms proof(induction "length pAC" arbitrary: "output" new_l pend l pAC a rule: less_induct)
  case less
  then show ?case proof(cases "pf ! a = a")
    case True
    with less have "c = a" using path_root by auto
    then show ?thesis by blast
  next
    case False
    then show ?thesis proof(cases "rep_of l a = rep_of l c")
      case True
      then have "(a \<approx> c) \<in> Congruence_Closure (representatives_set l)"
        using CC_same_rep_representatives_set[of l a c] less by argo
      then show ?thesis 
        using Congruence_Closure_split_rule by auto
    next
      case False': False
      then obtain paRoot where paRoot: "path l (rep_of l a) paRoot a" 
        using less False by (metis path_to_root_correct) 
      then have *: "path pf (rep_of l a) paRoot a" sorry (*1*)
      have length_pAC: "length paRoot < length pAC" 
      proof(rule ccontr)
        \<comment> \<open>If paRoot was longer than pAC, then there would be a path
from a to c in the additional union find (l), 
therefore a and c would have the same representative, which is a contradiction.\<close>
        let ?pARfront = "take (length paRoot - length pAC + 1) paRoot"
        let ?pARback = "drop (length paRoot - length pAC + 1) paRoot"
        assume length_p: "\<not> length paRoot < length pAC"
        then have not_empty: "?pARfront \<noteq> []" 
          by (metis "*" add_nonneg_eq_0_iff less_eq_nat.simps(1) path_properties take_eq_Nil2 zero_neq_one)
        with paRoot have p: "path l (rep_of l a) (?pARfront @ ?pARback) a"
          by auto
        then have path_pf_to_a: "path l (rep_of l a) (?pARfront) (last ?pARfront)"
          "path l (last ?pARfront) (last ?pARfront # ?pARback) a"
          using path_divide1[OF p not_empty] by blast+
        then have path_pf_to_a: "path pf (last ?pARfront) (last ?pARfront # ?pARback) a"
          sorry (*1*)
        then have "length (last ?pARfront # ?pARback) = length pAC" 
          by (metis (no_types, lifting) One_nat_def Suc_diff_1 ab_semigroup_add_class.add.commute add_diff_cancel_right add_diff_inverse_nat drop0 drop_Suc_Cons length_drop length_greater_0_conv length_p less.prems(5) list.discI path.simps)
        then have "c = last ?pARfront" 
          using less.prems(1,5) path_pf_to_a path_unique_if_length_eq by blast
        then have "rep_of l c = rep_of l a" 
          using less.prems(4) not_empty p path_divide1 path_rep_eq by blast
        then show "False"
          using False' by auto
      qed
      let ?pRootC = "(take (length pAC - length paRoot + 1) pAC)"
      from length_pAC have "path pf c ?pRootC (rep_of l a)" 
        using * less path_longer by fast
      with less path_butlast have path_to_parent: "path pf c (butlast ?pRootC) (pf ! rep_of l a)" 
        by (metis False' \<open>path l (rep_of l a) paRoot a\<close> path_rep_eq)
      have "length paRoot > 0"
        by (metis "*" length_greater_0_conv path_not_empty)
      then have "length pAC - length paRoot + 1 \<le> length pAC"  
        using length_pAC by linarith
      then have length_pRootC: "length (butlast ?pRootC) < length pAC"  
        by simp
      obtain output' new_l' pend' where recursive_step: "
explain_along_path
     \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>
     (ufa_union l a (pf ! rep_of l a)) (pf ! rep_of l a) c = (output', new_l', pend')"
        using prod_cases3 by blast
      have valid: "(pf ! rep_of l a) < length pf" "ufa_invar (ufa_union l a (pf ! rep_of l a))"
        using "*" less.prems(1,4,6) path_nodes_lt_length_l ufa_invarD(2) ufa_union_invar by auto
      with less(1)[OF length_pRootC less(2) this(1) less(4) this(2) path_to_parent] 
        path_to_parent recursive_step have IH: "(pf ! rep_of l a \<approx> c) \<in>
 Congruence_Closure (representatives_set (ufa_union l a (pf ! rep_of l a)) \<union> output'
\<union> pending_set_explain pend')" using less(7) by auto
      then have 3: "((pf ! rep_of l a) \<approx> (rep_of l a)) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend) \<Longrightarrow>
output' \<subseteq> output \<Longrightarrow> pending_set_explain pend' \<subseteq> pending_set_explain pend \<Longrightarrow> 
((pf ! rep_of l a) \<approx> c) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend)"
      proof(rule Congruence_Closure_imp)
        fix eq
        let ?union = "(ufa_union l a (pf ! rep_of l a))"
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
\<open>rep_of l a\<close> and \<open>a\<close> are congruent as an assumption.\<close>
            then have "rep_of l (pf ! rep_of l a) = rep_of ?union k"
              using less.prems(4,6) rep_set(2) ufa_union_aux valid(1) by auto
            then have
              *: "((pf ! rep_of l a) \<approx> (rep_of ?union k))
\<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
              by (metis (no_types, lifting) Congruence_Closure.symmetric Congruence_Closure_split_rule a_eq_rep_of_a_in_CC_representatives_set(2) less.prems(6) valid(1))
            then have
              "(k \<approx> rep_of l a)
\<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
              by (metis (no_types, lifting) symmetric Congruence_Closure_split_rule True a_eq_rep_of_a_in_CC_representatives_set(2) length_list_update rep_set(2))
            with * show ?thesis 
              using prems by (metis (no_types, lifting) symmetric transitive1 rep_set(1))
          next
            case False
            then have "rep_of ?union k = rep_of l k" 
              by (metis length_list_update less.prems(4,6) paRoot path_nodes_lt_length_l rep_set(2) ufa_union_aux valid(1))
            then show ?thesis 
              using symmetric Congruence_Closure_split_rule a_eq_rep_of_a_in_CC_representatives_set(2) rep_set by force
          qed 
        qed 
      qed
      have "(a \<approx> (rep_of l a)) \<in> Congruence_Closure (representatives_set l)"
        by (auto simp add: less.prems(2) less.prems(4) less.prems(6) rep_of_iff)
      then have 1: "(a \<approx> rep_of l a) \<in> Congruence_Closure 
(representatives_set l \<union> output \<union> pending_set_explain pend)"
        using Congruence_Closure_split_rule by auto
      show ?thesis proof(cases "the (pfl ! rep_of l a)")
        case (One a')
        then have *: "pfl ! rep_of l a = Some (One a')" sorry (*3*)
            (*TODO add pfl invar, similar to pending invar*)
        have dom: "explain_along_path_dom
     (\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>, 
l,a, c)" sorry 
        have result: "(output, new_l, pend) = ({a'} \<union> output', new_l', pend')" 
          using less(8) explain_along_path_simp2[OF False'] One 
            False * recursive_step by auto
        then have a': "a' = (rep_of l a \<approx> pf ! rep_of l a)
\<or> a' = (pf ! rep_of l a \<approx> rep_of l a)" sorry (*3*)
        have "(rep_of l a \<approx> pf ! rep_of l a) \<in> 
Congruence_Closure ({a'} \<union> output')" 
          using a' by blast
        then have 2: "(rep_of l a \<approx> pf ! rep_of l a) \<in> 
Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
          using result Congruence_Closure_split_rule 
          by (metis (no_types, lifting) Pair_inject sup_commute)
        from result have "representatives_set l \<union> output' \<union> pending_set_explain pend'
\<subseteq> representatives_set l \<union> output \<union> pending_set_explain pend" 
          by blast
        with 3 have "(pf ! rep_of l a \<approx> c) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend)"
          using Congruence_Closure_monotonic 2 symmetric result by blast
        then show ?thesis using 1 2 by blast
      next
        case (Two x21 x22)
        then obtain a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b' where *: "(pfl ! rep_of l a)
= Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))" sorry (*3*)
        have dom: "explain_along_path_dom
     (\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>, 
l, a, c)" sorry (*4*)
        have result: "(output, new_l, pend) = 
({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output', new_l', [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend')" 
          using less(8) explain_along_path_simp3[OF False']
            False * recursive_step by auto
        then have a': "a' = rep_of l a \<and> b' = pf ! rep_of l a
\<or> a' = pf ! rep_of l a \<and> b' = rep_of l a" sorry (*3*)
        have "(a\<^sub>1 \<approx> b\<^sub>1) \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
          "(a\<^sub>2 \<approx> b\<^sub>2) \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
          "(F a\<^sub>1 a\<^sub>2 \<approx> a') \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
          "(F b\<^sub>1 b\<^sub>2 \<approx> b') \<in> Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)"
          using result by auto
        then have 2: "(rep_of l a \<approx> pf ! rep_of l a) \<in> 
Congruence_Closure (representatives_set l \<union> output \<union> pending_set_explain pend)" 
          using a' monotonic by blast
        from result have "representatives_set l \<union> output' \<union> pending_set_explain pend'
\<subseteq> representatives_set l \<union> output \<union> pending_set_explain pend" 
          using pending_set_explain_Cons by auto
        with 3 have "(pf ! rep_of l a \<approx> c) \<in> Congruence_Closure
        (representatives_set l \<union> output \<union> pending_set_explain pend)"
          using Congruence_Closure_monotonic 2 symmetric result by auto
        then show ?thesis using 1 2 by blast
      qed
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