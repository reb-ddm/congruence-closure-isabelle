theory CC_Explain_Timestamps
  imports CC_Explain_Invar2
begin 

section \<open>Definition of explain with timestamps\<close>

function (domintros) explain_along_path3 :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    nat \<Rightarrow> (equation set * nat list * (nat * nat) list * nat)"
  where 
    "explain_along_path3 cc l a c n = 
(if a = c 
then
  ({}, l, [], n)
else
  (let b = (proof_forest cc) ! a in 
    (let k = (if l ! a = a then n else l ! a) in
      (
      case the ((pf_labels cc) ! a) of 
          One a' \<Rightarrow>  
            (let (output, new_l, pending, n') = explain_along_path3 cc (l[a := k]) b c (n + 1)
            in ({a'} \<union> output, new_l, pending, n'))
          | Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b') \<Rightarrow> 
            (let (output, new_l, pending, n') = explain_along_path3 cc (l[a := k]) b c (n + 1)
            in ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, new_l, [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pending, n'))
      )
    )
  )
)"
  by pat_completeness auto

lemma explain_along_path3_simp1:
  assumes "a = c"
  shows "explain_along_path3 cc l a c n = ({}, l, [], n)"
proof-
  have "explain_along_path3_dom (cc, l, a, c, n)"
    using assms explain_along_path3.domintros by blast
  then show ?thesis using explain_along_path3.psimps 
    by (simp add: assms)
qed

lemma explain_along_path3_simp2:
  assumes "a \<noteq> c"
    "(pf_labels cc) ! a = Some (One a')"
    "k = (if l ! a = a then n else l ! a)"
    "explain_along_path3 cc (l[a := k]) ((proof_forest cc) ! a) c (n + 1) = (output, new_l, pend, n')"
    "explain_along_path3_dom (cc, l, a, c, n)"
  shows "explain_along_path3 cc l a c n = ({a'} \<union> output, new_l, pend, n')"
  using explain_along_path3.psimps assms unfolding Let_def 
  by auto

lemma explain_along_path3_simp3:
  assumes "a \<noteq> c"
    "(pf_labels cc) ! a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))"
    "k = (if l ! a = a then n else l ! a)"
    "explain_along_path3 cc (l[a := k]) ((proof_forest cc) ! a) c (n + 1) = (output, new_l, pend, n')"
    "explain_along_path3_dom (cc, l, a, c, n)"
  shows "explain_along_path3 cc l a c n = ({(F a\<^sub>1 a\<^sub>2 \<approx> a'), (F b\<^sub>1 b\<^sub>2 \<approx> b')} \<union> output, new_l,
     [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend, n')"
  using explain_along_path3.psimps assms unfolding Let_def 
  by auto


function (domintros) cc_explain_aux3 :: "congruence_closure \<Rightarrow> nat list \<Rightarrow> (nat * nat) list \<Rightarrow> 
nat \<Rightarrow> equation set"
  where
    "cc_explain_aux3 cc l [] n = {}"
  | "cc_explain_aux3 cc l ((a, b) # xs) n =
(if are_congruent cc (a \<approx> b)
then
  (let c = lowest_common_ancestor (proof_forest cc) a b;
    (output1, new_l, pending1, n') = explain_along_path3 cc l a c n;
    (output2, new_new_l, pending2, n'') = explain_along_path3 cc new_l b c n'
  in
    output1 \<union> output2 \<union> cc_explain_aux3 cc new_new_l (pending1 @ pending2 @ xs) n'')
else cc_explain_aux3 cc l xs n)"
  by pat_completeness auto

lemma cc_explain_aux3_simp1:
  "cc_explain_aux3 cc l [] n = {}" 
  using cc_explain_aux3.domintros cc_explain_aux3.psimps by blast

lemma cc_explain_aux3_simp2:
  assumes "cc_explain_aux3_dom (cc, l, ((a, b) # xs), n)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "are_congruent cc (a \<approx> b)"
    "(output1, new_l, pending1, n') = explain_along_path3 cc l a c n"
    "(output2, new_new_l, pending2, n'') = explain_along_path3 cc new_l b c n'"
  shows "cc_explain_aux3 cc l ((a, b) # xs) n = 
output1 \<union> output2 \<union> cc_explain_aux3 cc new_new_l (pending1 @ pending2 @ xs) n''" 
  using cc_explain_aux3.psimps assms unfolding Let_def 
  by auto

lemma cc_explain_aux3_simp3:
  assumes "cc_explain_aux3_dom (cc, l, ((a, b) # xs), n)"
    "\<not> are_congruent cc (a \<approx> b)"
  shows "cc_explain_aux3 cc l ((a, b) # xs) n = cc_explain_aux3 cc l xs n" 
  using cc_explain_aux3.domintros cc_explain_aux3.psimps assms unfolding Let_def 
  by auto

abbreviation cc_explain3 :: "congruence_closure \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> equation set"
  where
    "cc_explain3 cc a b \<equiv> cc_explain_aux3 cc [0..<nr_vars cc] [(a, b)] 0"

subsection \<open>Termination proof of \<open>cc_explain2\<close>\<close>

subsubsection \<open>Termination of \<open>explain_along_path2\<close>\<close>

lemma explain_along_path3_domain:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
  shows "explain_along_path3_dom (cc, l, a, c, n)"
  using assms proof(induction "length p" arbitrary: p a l n rule: less_induct)
  case less
  then show ?case proof(cases "a = c")
    case True
    then show ?thesis using explain_along_path3.domintros by blast
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
    define k where "k = (if l ! a = a then n else l ! a)"
    with less(1,2)  pRAC' cc have recursive_dom:
      "explain_along_path3_dom (cc, (l[a := k]), (pf ! a), c, (n + 1))" 
      by (metis \<open>0 < length p\<close> congruence_closure.select_convs(5) diff_less length_butlast less_numeral_extra(1))
    show ?thesis using cc recursive_dom explain_along_path3.domintros k_def list_update_id 
      Suc_eq_plus1 congruence_closure.select_convs(5) 
      by (smt (verit, best))
  qed
qed

theorem cc_explain_aux3_domain:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
  shows "cc_explain_aux3_dom (cc, l, xs, n)"
  sorry

lemma cc_explain_aux_cc_explain_aux3_equivalence:
  assumes "was_already_in_pending_dom (cc, l, xs2, xs)"
    "cc_invar cc"
    "\<forall> (a, b) \<in> set xs2 . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs2 . are_congruent cc (a \<approx> b)"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "explain_list_invar l (proof_forest cc)" 
    "set xs2 \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)"
    "subseq xs xs2"
  shows "cc_explain_aux3 cc l xs2 n \<subseteq>
cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)
\<union> \<Union>(cc_explain_aux2 cc ` (\<lambda> x . [x]) ` (additional_uf_pairs_set l (pf_labels cc)))"
  sorry

end