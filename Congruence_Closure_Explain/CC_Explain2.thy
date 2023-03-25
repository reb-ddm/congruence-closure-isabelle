theory CC_Explain2
  imports CC_Definition2 "HOL-Library.Multiset_Order"
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


subsection \<open>Termination of \<open>explain_along_path2\<close>\<close>

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

subsection \<open>Induction rule on \<open>explain_long_path2\<close>\<close>

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
        have "(proof_forest cc) ! a \<noteq> a" "a < length (proof_forest cc)"
          using "1.prems"(2) False path_no_root apply auto[1]
          using "1.prems"(2) path_nodes_lt_length_l by fastforce
        then obtain x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y where Some: "((pf_labels cc) ! a = Some (One (x' \<approx> y)) \<or> 
          (pf_labels cc) ! a = Some (Two (F x\<^sub>1 x\<^sub>2 \<approx> x') (F y\<^sub>1 y\<^sub>2 \<approx> y)))
          \<and> (x' = (proof_forest cc) ! a \<and> y = a \<or> x' = a \<and> y = (proof_forest cc) ! a)
          \<and> valid_vars_pending (the ((pf_labels cc) ! a)) (cc_list cc)"
          using Two "1.prems" False not_none unfolding pf_labels_invar_def 
          by blast
        then have Some: "(pf_labels cc) ! a = 
Some (Two (F x\<^sub>1 x\<^sub>2 \<approx> x') (F y\<^sub>1 y\<^sub>2 \<approx> y))" "x\<^sub>1 < nr_vars cc" "x\<^sub>2 < nr_vars cc" "x' < nr_vars cc"
          "y\<^sub>1 < nr_vars cc" "y\<^sub>2 < nr_vars cc"  "y < nr_vars cc"
          using Two by fastforce+
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


subsection \<open>Lemmata about \<open>cc_explain_along_path\<close> and \<open>cc_explain_along_path2\<close>\<close>

fun pending_pairs :: "pending_equation option \<Rightarrow> (nat * nat) set"
  where
    "pending_pairs None = {}"
  | "pending_pairs (Some (One a)) = {}"
  | "pending_pairs (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))) = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}"
  | "pending_pairs (Some (Two a b)) = {}"

definition additional_uf_pairs_set where
  "additional_uf_pairs_set l pfl \<equiv> \<Union>{pending_pairs (pfl ! a) |a. a < length l \<and> l ! a \<noteq> a}"

lemma additional_uf_labels_set_fun_upd_l:
  assumes "k \<noteq> pf ! k" "k < length l"
  shows "additional_uf_labels_set (l[k := pf ! k]) pfl =
additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
proof
  show "additional_uf_labels_set (l[k := pf ! k]) pfl
    \<subseteq> additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
  proof
    fix x assume "x \<in> additional_uf_labels_set (l[k := pf ! k]) pfl"
    then obtain i where i: "x \<in> pe_to_set (pfl ! i)" 
      "i < length (l[k := pf ! k])" "l[k := pf ! k] ! i \<noteq> i" 
      unfolding additional_uf_labels_set_def by auto
    then show "x \<in> additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
    proof(cases "l ! i = i")
      case True
      with i show ?thesis unfolding additional_uf_labels_set_def 
        by (metis (no_types, lifting) Un_iff nth_list_update_neq)
    next
      case False
      then show ?thesis unfolding additional_uf_labels_set_def 
        using i by auto
    qed
  qed
next
  show "additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)
    \<subseteq> additional_uf_labels_set (l[k := pf ! k]) pfl"
  proof
    fix x assume "x \<in> additional_uf_labels_set l pfl \<union> pe_to_set (pfl ! k)"
    then show "x \<in> additional_uf_labels_set (l[k := pf ! k]) pfl"
    proof
      assume "x \<in> additional_uf_labels_set l pfl"
      then obtain i where i: "x \<in> pe_to_set (pfl ! i)" "i < length l \<and> l ! i \<noteq> i"
        unfolding additional_uf_labels_set_def by blast
      then have "l[k := pf ! k] ! i \<noteq> i" using assms 
        by (metis nth_list_update_eq nth_list_update_neq)
      then show ?thesis unfolding additional_uf_labels_set_def 
        using i(1) i(2) by auto
    next
      assume "x \<in> pe_to_set (pfl ! k)"
      have "l[k := pf ! k] ! k \<noteq> k" 
        using assms by simp
      then show ?thesis unfolding additional_uf_labels_set_def
        using \<open>x \<in> pe_to_set (pfl ! k)\<close> assms(2) length_list_update mem_Collect_eq by fastforce
    qed
  qed
qed

lemma additional_uf_labels_set_explain_along_path:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "additional_uf_labels_set new_l (pf_labels cc) = 
additional_uf_labels_set l (pf_labels cc) \<union> output"
  using assms proof(induction rule: explain_along_path_induct)
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  have "additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> pe_to_set (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) One.hyps(3,4,5,8,9) additional_uf_labels_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_iff rep_of_less_length_l)
  moreover have "pe_to_set (pf_labels cc ! rep_of l a) = {x1}" 
    by (simp add: One.hyps(10))
  ultimately show ?case 
    by (simp add: One.IH)
next
  case (Two cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" new_l pend)
  have "additional_uf_labels_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> pe_to_set (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) Two.hyps(3,4,5,8,9) additional_uf_labels_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_iff rep_of_less_length_l)
  moreover have "pe_to_set (pf_labels cc ! rep_of l a) = {F x\<^sub>1 x\<^sub>2 \<approx> x', F y\<^sub>1 y\<^sub>2 \<approx> y}" 
    by (simp add: Two.hyps(10-12))
  ultimately show ?case 
    by (simp add: Two.IH)
qed simp

lemma additional_uf_labels_set_explain_along_path':
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output1, new_l, pend1)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pend2)"
    "a < nr_vars cc" "b < nr_vars cc"
    "are_congruent cc (a \<approx> b)"
  shows "additional_uf_labels_set l (pf_labels cc) \<subseteq>
additional_uf_labels_set new_new_l (pf_labels cc)"
proof-
obtain p1 p2 where paths: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b"
    using assms lowest_common_ancestor_correct unfolding proof_forest_invar_def 
    by (metis assms(1) explain_along_path_lowest_common_ancestor)
  have 1: "additional_uf_labels_set l (pf_labels cc) \<subseteq> additional_uf_labels_set new_l (pf_labels cc)"
    using additional_uf_labels_set_explain_along_path assms paths 
    by blast
  have eli: "explain_list_invar new_l (proof_forest cc)" using assms 
    by (metis explain_along_path_domain explain_list_invar_explain_along_path' paths(1))
  then have  "additional_uf_labels_set new_l (pf_labels cc)
 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
    using additional_uf_labels_set_explain_along_path assms paths 
    by blast
  then show ?thesis using 1 
    by simp
qed

lemma additional_uf_pairs_set_fun_upd_l:
  assumes "k \<noteq> pf ! k" "k < length l"
  shows "additional_uf_pairs_set (l[k := pf ! k]) pfl =
additional_uf_pairs_set l pfl \<union> pending_pairs (pfl ! k)"
proof
  show "additional_uf_pairs_set (l[k := pf ! k]) pfl
    \<subseteq> additional_uf_pairs_set l pfl \<union> pending_pairs (pfl ! k)"
  proof
    fix x assume "x \<in> additional_uf_pairs_set (l[k := pf ! k]) pfl"
    then obtain i where i: "x \<in> pending_pairs (pfl ! i)" 
      "i < length (l[k := pf ! k])" "l[k := pf ! k] ! i \<noteq> i" 
      unfolding additional_uf_pairs_set_def by auto
    then show "x \<in> additional_uf_pairs_set l pfl \<union> pending_pairs (pfl ! k)"
    proof(cases "l ! i = i")
      case True
      with i show ?thesis
        by (metis (no_types, lifting) Un_iff nth_list_update_neq)
    next
      case False
      then show ?thesis unfolding additional_uf_pairs_set_def 
        using i by auto
    qed
  qed
next
  show "additional_uf_pairs_set l pfl \<union> pending_pairs (pfl ! k)
    \<subseteq> additional_uf_pairs_set (l[k := pf ! k]) pfl"
  proof
    fix x assume "x \<in> additional_uf_pairs_set l pfl \<union> pending_pairs (pfl ! k)"
    then show "x \<in> additional_uf_pairs_set (l[k := pf ! k]) pfl"
    proof
      assume "x \<in> additional_uf_pairs_set l pfl"
      then obtain i where i: "x \<in> pending_pairs (pfl ! i)" "i < length l \<and> l ! i \<noteq> i"
        unfolding additional_uf_pairs_set_def by blast
      then have "l[k := pf ! k] ! i \<noteq> i" using assms 
        by (metis nth_list_update_eq nth_list_update_neq)
      then show ?thesis unfolding additional_uf_pairs_set_def 
        using i(1) i(2) by auto
    next
      assume "x \<in> pending_pairs (pfl ! k)"
      have "l[k := pf ! k] ! k \<noteq> k" 
        using assms by simp
      then show ?thesis unfolding additional_uf_pairs_set_def
        using \<open>x \<in> pending_pairs (pfl ! k)\<close> assms(2) length_list_update mem_Collect_eq by fastforce
    qed
  qed
qed

lemma additional_uf_pairs_set_explain_along_path:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "additional_uf_pairs_set new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pend"
  using assms proof(induction rule: explain_along_path_induct)
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  have "additional_uf_pairs_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_pairs_set l (pf_labels cc) \<union> pending_pairs (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) One.hyps(3,4,5,8,9) additional_uf_pairs_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_iff rep_of_less_length_l)
  moreover have "pending_pairs (pf_labels cc ! rep_of l a) = {}" 
    by (simp add: One.hyps(10))
  ultimately show ?case 
    by (simp add: One.IH)
next
  case (Two cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" new_l pend)
  have "additional_uf_pairs_set (l[rep_of l a := x]) (pf_labels cc)
= additional_uf_pairs_set l (pf_labels cc) \<union> pending_pairs (pf_labels cc ! rep_of l a)"
    by (metis (no_types, lifting) Two.hyps(3,4,5,8,9) additional_uf_pairs_set_fun_upd_l explain_list_invar_def path_nodes_lt_length_l path_root rep_of_iff rep_of_less_length_l)
  moreover have "pending_pairs (pf_labels cc ! rep_of l a) = {(x\<^sub>1,y\<^sub>1), (x\<^sub>2, y\<^sub>2)}" 
    by (simp add: Two.hyps(10-12))
  ultimately show ?case 
    by (simp add: Two.IH)
qed simp

lemma additional_uf_pairs_set_explain_along_path'':
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "a < nr_vars cc" "b < nr_vars cc"
    "are_congruent cc (a \<approx> b)"
    "explain_along_path cc l a c = (output1, new_l, pend1)"
    "explain_along_path cc new_l a c = (output2, new_new_l, pend2)"
  shows "additional_uf_pairs_set new_new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pend1 \<union> set pend2"
proof-
  have "ufa_invar (proof_forest cc)" "nr_vars cc = length (proof_forest cc)" 
    using assms unfolding proof_forest_invar_def same_length_invar_def
    by auto
  then obtain p1 p2 where "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b"
    using assms lowest_common_ancestor_correct 
    by (metis are_congruent_implies_proof_forest_rep_of_eq length_explain_list_cc_list)
  then have 1: "additional_uf_pairs_set new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pend1" 
    using additional_uf_pairs_set_explain_along_path by (simp add: assms(1) assms(2) assms(7))
  have "explain_list_invar new_l (proof_forest cc)" using assms 
    by (metis explain_list_invar_explain_along_path'' length_explain_list_cc_list)
  then have "additional_uf_pairs_set new_new_l (pf_labels cc) = 
additional_uf_pairs_set new_l (pf_labels cc) \<union> set pend2" 
    using additional_uf_pairs_set_explain_along_path 
    using \<open>path (proof_forest cc) c p1 a\<close> assms(1) assms(8) by auto
  then show ?thesis using 1 
    by auto
qed

lemma additional_uf_pairs_set_explain_along_path':
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output1, new_l, pend1)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pend2)"
    "a < nr_vars cc" "b < nr_vars cc"
    "are_congruent cc (a \<approx> b)"
  shows "additional_uf_pairs_set l (pf_labels cc) \<subseteq>
additional_uf_pairs_set new_new_l (pf_labels cc)"
proof-
obtain p1 p2 where paths: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b"
    using assms lowest_common_ancestor_correct unfolding proof_forest_invar_def 
    by (metis assms(1) explain_along_path_lowest_common_ancestor)
  have 1: "additional_uf_pairs_set l (pf_labels cc) \<subseteq> additional_uf_pairs_set new_l (pf_labels cc)"
    using additional_uf_pairs_set_explain_along_path assms paths 
    by blast
  have eli: "explain_list_invar new_l (proof_forest cc)" using assms 
    by (metis explain_along_path_domain explain_list_invar_explain_along_path' paths(1))
  then have  "additional_uf_pairs_set new_l (pf_labels cc)
 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
    using additional_uf_pairs_set_explain_along_path assms paths 
    by blast
  then show ?thesis using 1 
    by simp
qed

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

lemma explain_along_path_new_l_unchanged:
  assumes "cc_invar cc"
    "explain_list_invar l (proof_forest cc)" 
    "path (proof_forest cc) c p a"
    "explain_along_path cc l a c = (output, new_l, pend)"
    "l ! k \<noteq> k" "k < length l"
  shows "new_l ! k = l ! k" 
  using assms proof(induction rule: explain_along_path_induct)
  case (One cc l a c p1 p2 x x1 x11 x12 "output" new_l pend)
  have "l[rep_of l a := x] ! k \<noteq> k" 
    by (metis One.hyps(3,9) One.prems(1,2) explain_list_invar_def nth_list_update_eq nth_list_update_neq)
  then show ?case 
    using One.IH One.hyps(3,6) One.prems(1,2) explain_list_invar_def by auto
next
  case (Two cc l a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" new_l pend)
  have "l[rep_of l a := x] ! k \<noteq> k" 
    by (metis Two.hyps(3,9) Two.prems(1,2) explain_list_invar_def nth_list_update_eq nth_list_update_neq)
  then show ?case 
    using Two.IH Two.hyps(3,6) Two.prems(1,2) explain_list_invar_def by auto
qed blast

lemma explain_along_path_explain_along_path2_output_subset:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
    "explain_along_path2 cc a c = (output2, pend2)"
    "explain_list_invar l (proof_forest cc)" 
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "output2 \<subseteq> additional_uf_labels_set new_l (pf_labels cc)"
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
    have "output = {x1} \<union> o_rec" "new_l = l_rec"
      using explain_along_path_simp2[OF *] One rec 
        explain_along_path_domain[OF One(2,14,3)] True by auto
    have IH: "output2 \<subseteq> additional_uf_labels_set l_rec (pf_labels cc)"
      using One(13) invar rec by blast
    have "length l_rec = length l" "l_rec ! a = x"
      using rec explain_along_path_new_l_length 
       apply (metis One.hyps(2,3) One.prems(1,2) \<open>new_l = l_rec\<close>)
      using rec explain_along_path_new_l_unchanged 
      by (smt (verit) One.hyps(2-7) One.prems(1) True explain_list_invar_def invar nth_list_update_eq path_nodes_lt_length_l path_root)
    then have "x1 \<in> pe_to_set (pf_labels cc ! a)" "a < length l_rec" "l_rec ! a \<noteq> a"
        apply (simp add: One.hyps(8))
      using One.hyps(3) One.prems(1) \<open>length l_rec = length l\<close> explain_list_invar_def path_nodes_lt_length_l apply fastforce
      using One.hyps(3,6,7) \<open>l_rec ! a = x\<close> path_root by auto
    then have "{x1} \<subseteq> additional_uf_labels_set l_rec (pf_labels cc)"
      unfolding additional_uf_labels_set_def by auto
    then show ?thesis 
      using IH \<open>new_l = l_rec\<close> by simp
  next
    case False
    then have *: "x = l ! a" 
      by (metis (no_types, lifting) One.hyps(3,7) One.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    have "length new_l = length l" "new_l ! a = x"
      using explain_along_path_new_l_length 
       apply (metis One.hyps(2,3) One.prems(1,2))
      using * One 
      by (smt (verit, del_insts) False explain_along_path_new_l_unchanged length_explain_list_cc_list path_nodes_lt_length_l rep_of_refl same_length_invar_def)
    then have "x1 \<in> pe_to_set (pf_labels cc ! a)" "a < length new_l" "new_l ! a \<noteq> a"
        apply (simp add: One.hyps(8))
      using One.hyps(3) One.prems(1) \<open>length new_l = length l\<close> explain_list_invar_def path_nodes_lt_length_l apply auto[1]
      using "*" False \<open>new_l ! a = x\<close> rep_of_refl by auto
    then have "x1 \<in> additional_uf_labels_set new_l (pf_labels cc)"
      unfolding additional_uf_labels_set_def by blast
    have "explain_along_path cc l x c = explain_along_path cc l a c"
      using "*" One.hyps(2) One.hyps(3) One.prems(1) explain_along_path_parent_eq by presburger
    then show ?thesis
      using One.IH One.hyps(2,3) One.prems(1,2) explain_along_path_parent_eq 
      by (metis \<open>x1 \<in> additional_uf_labels_set new_l (pf_labels cc)\<close> insert_is_Un insert_subset)
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
    have "output = {x21, x22} \<union> o_rec" "new_l = l_rec"
      using explain_along_path_simp3[OF *] Two rec 
        explain_along_path_domain[OF Two(2,19,3)] True by auto
    have IH: "output2 \<subseteq> additional_uf_labels_set l_rec (pf_labels cc)"
      using Two(18) invar rec by blast
    have "length l_rec = length l" "l_rec ! a = x"
      using rec explain_along_path_new_l_length 
       apply (metis Two.hyps(2,3) Two.prems(1,2) \<open>new_l = l_rec\<close>)
      using rec explain_along_path_new_l_unchanged 
Two.hyps(2-7) Two.prems(1) True explain_list_invar_def invar nth_list_update_eq path_nodes_lt_length_l path_root
      by (smt (verit))
    then have "{x21, x22} \<subseteq> pe_to_set (pf_labels cc ! a)" "a < length l_rec" "l_rec ! a \<noteq> a"
        apply (simp add: Two.hyps(8))
      using Two.hyps(3) Two.prems(1) \<open>length l_rec = length l\<close> explain_list_invar_def path_nodes_lt_length_l apply fastforce
      using Two.hyps(3,6,7) \<open>l_rec ! a = x\<close> path_root by auto
    then have "{x21, x22} \<subseteq> additional_uf_labels_set l_rec (pf_labels cc)"
      unfolding additional_uf_labels_set_def by auto
    then show ?thesis 
      using IH \<open>new_l = l_rec\<close> Two(9,10) by simp
  next
    case False
    then have *: "x = l ! a" 
      by (metis (no_types, lifting) Two.hyps(3,7) Two.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    have "length new_l = length l" "new_l ! a = x"
      using explain_along_path_new_l_length 
       apply (metis Two.hyps(2,3) Two.prems(1,2))
      using * Two False explain_along_path_new_l_unchanged length_explain_list_cc_list path_nodes_lt_length_l rep_of_refl same_length_invar_def
      by (smt (verit, del_insts))
    then have "{x21, x22} \<subseteq> pe_to_set (pf_labels cc ! a)" "a < length new_l" "new_l ! a \<noteq> a"
        apply (simp add: Two.hyps(8))
      using Two.hyps(3) Two.prems(1) \<open>length new_l = length l\<close> explain_list_invar_def path_nodes_lt_length_l apply auto[1]
      using "*" False \<open>new_l ! a = x\<close> rep_of_refl by auto
    then have "{x21, x22} \<subseteq> additional_uf_labels_set new_l (pf_labels cc)"
      unfolding additional_uf_labels_set_def by blast
    have "explain_along_path cc l x c = explain_along_path cc l a c"
      using "*" Two.hyps(2,3) Two.prems(1) explain_along_path_parent_eq by presburger
    then show ?thesis
      using Two.IH Two.hyps(2,3) Two.prems(1,2) explain_along_path_parent_eq Two(9,10)
      by (metis Un_least \<open>{x21, x22} \<subseteq> additional_uf_labels_set new_l (pf_labels cc)\<close>)
  qed
qed

lemma explain_along_path_explain_along_path2_output_subset':
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output1, new_l, pending1)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
    "explain_list_invar l (proof_forest cc)"
    "explain_along_path2 cc a c = (output12, pending12)"
    "explain_along_path2 cc b c = (output22, pending22)"
       shows "output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
proof-
  obtain p1 p2 where paths: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b"
    using assms lowest_common_ancestor_correct unfolding proof_forest_invar_def 
    by (metis assms(1) case_prod_conv explain_along_path_lowest_common_ancestor list.set_intros(1))
  have 1: "output12 \<subseteq> additional_uf_labels_set new_l (pf_labels cc)"
    using explain_along_path_explain_along_path2_output_subset assms paths 
    by metis
  have eli: "explain_list_invar new_l (proof_forest cc)" using assms 
    by (metis explain_along_path_domain explain_list_invar_explain_along_path' paths(1))
  then have 2: "output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
    using explain_along_path_explain_along_path2_output_subset assms paths 
    by metis
  have 3: "additional_uf_labels_set new_l (pf_labels cc) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
    using assms additional_uf_labels_set_explain_along_path eli paths 
    by (metis Un_upper1)
  then show ?thesis using 1 2 3 
    by simp
qed

lemma explain_along_path_explain_along_path2_pending_subset:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
    "explain_along_path2 cc a c = (output2, pend2)"
    "explain_list_invar l (proof_forest cc)" 
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "set pend2 \<subseteq> additional_uf_pairs_set new_l (pf_labels cc)"
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
    have "new_l = l_rec"
      using explain_along_path_simp2[OF *] One rec 
        explain_along_path_domain[OF One(2,14,3)] True by auto
    have IH: "set pend2 \<subseteq> additional_uf_pairs_set l_rec (pf_labels cc)"
      using One(13) invar rec by blast
    show ?thesis 
      using IH \<open>new_l = l_rec\<close> by simp
  next
    case False
    then have *: "x = l ! a" 
      by (metis (no_types, lifting) One.hyps(3,7) One.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    then have "explain_along_path cc l x c = explain_along_path cc l a c"
      using One.hyps(2) One.hyps(3) One.prems(1) explain_along_path_parent_eq by presburger
    then show ?thesis
      using One.IH One.hyps(2,3) One.prems(1,2) explain_along_path_parent_eq 
      by metis
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
    have "new_l = l_rec" "pend = [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] @ p_rec"
      using explain_along_path_simp3[OF *] Two rec 
        explain_along_path_domain[OF Two(2,19,3)] True by auto
    have IH: "set pend2 \<subseteq> additional_uf_pairs_set l_rec (pf_labels cc)"
      using Two(18) invar rec by blast
    have "length l_rec = length l" "l_rec ! a = x" "{(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)} \<subseteq> pending_pairs (pf_labels cc ! a)"
      using rec explain_along_path_new_l_length 
        apply (metis Two.hyps(2,3) Two.prems(1,2) \<open>new_l = l_rec\<close>)
      using rec explain_along_path_new_l_unchanged 
       apply (smt (verit) Two.hyps(2-7) Two.prems(1) True explain_list_invar_def invar nth_list_update_eq path_nodes_lt_length_l path_root)
      by (simp add: Two.hyps(8-10))
    then have "{(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)} \<subseteq> additional_uf_pairs_set l_rec (pf_labels cc)"
      unfolding additional_uf_pairs_set_def 
      by (smt (verit, del_insts) Sup_upper2 True Two.hyps(3) Two.hyps(6) Two.hyps(7) Two.hyps(8) \<open>new_l = l_rec\<close> explain_list_invar_def insert_Collect invar length_list_update mem_Collect_eq path_no_root path_nodes_lt_length_l singleton_conv)
    then show ?thesis 
      using IH \<open>new_l = l_rec\<close> by simp
  next
    case False
    then have *: "x = l ! a" 
      by (metis (no_types, lifting) Two.hyps(3,7) Two.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    have "length new_l = length l" "new_l ! a = x"
      using explain_along_path_new_l_length 
       apply (metis Two.hyps(2,3) Two.prems(1,2))
      using * Two 
      by (smt (verit, del_insts) False explain_along_path_new_l_unchanged length_explain_list_cc_list path_nodes_lt_length_l rep_of_refl same_length_invar_def)
    then have "{(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)} \<subseteq> pending_pairs (pf_labels cc ! a)" "a < length new_l" "new_l ! a \<noteq> a"
        apply (simp add: Two.hyps(8-10))
      using Two.hyps(3) Two.prems(1) \<open>length new_l = length l\<close> explain_list_invar_def path_nodes_lt_length_l apply auto[1]
      using "*" False \<open>new_l ! a = x\<close> rep_of_refl by auto
    then have "{(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)} \<subseteq> additional_uf_pairs_set new_l (pf_labels cc)"
      unfolding additional_uf_pairs_set_def by blast
    have "explain_along_path cc l x c = explain_along_path cc l a c"
      using "*" Two.hyps(2,3) Two.prems(1) explain_along_path_parent_eq by presburger
    then show ?thesis
      using Two.IH Two.hyps(2,3) Two.prems(1,2) explain_along_path_parent_eq Two(9,10)
      using \<open>{(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)} \<subseteq> additional_uf_pairs_set new_l (pf_labels cc)\<close> by auto
  qed
qed

lemma explain_along_path_explain_along_path2_pending_subset':
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "explain_along_path cc l a c = (output1, new_l, pending1)"
    "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
    "equations_of_l_in_pending_invar3 cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
    "explain_along_path2 cc a c = (output12, pending12)"
    "explain_along_path2 cc b c = (output22, pending22)"
  shows "set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
proof-
  obtain p1 p2 where paths: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b"
    using assms lowest_common_ancestor_correct unfolding proof_forest_invar_def 
    by (metis assms(1) case_prod_conv explain_along_path_lowest_common_ancestor list.set_intros(1))
  have 1: "set pending12 \<subseteq> additional_uf_pairs_set new_l (pf_labels cc)"
    using explain_along_path_explain_along_path2_pending_subset assms paths 
    by metis
  have eli: "explain_list_invar new_l (proof_forest cc)" using assms 
    by (metis explain_along_path_domain explain_list_invar_explain_along_path' paths(1))
  then have 2: "set pending22 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
    using explain_along_path_explain_along_path2_pending_subset assms paths 
    by metis
  have 3: "additional_uf_pairs_set new_l (pf_labels cc) \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
    using assms eli paths additional_uf_pairs_set_explain_along_path
    by (metis Un_upper1)
  then show ?thesis using 1 2 3 
    by simp
qed

lemma explain_along_path_new_new_l_same_length:
  assumes "cc_invar cc"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "explain_list_invar l (proof_forest cc)"
    "a < nr_vars cc" "b < nr_vars cc"
    "are_congruent cc (a \<approx> b)"
  shows "length l = length new_new_l"
proof-
  obtain p1 p2 where paths: "path (proof_forest cc) c p1 a" "path (proof_forest cc) c p2 b"
    using assms lowest_common_ancestor_correct unfolding proof_forest_invar_def 
    same_length_invar_def 
    by (metis assms(1) explain_along_path_lowest_common_ancestor)
  with explain_along_path_new_l_length have "length l = length new_l" 
    by (metis assms(1) assms(3) assms(5))
  have eli: "explain_list_invar new_l (proof_forest cc)" using assms 
    by (metis explain_along_path_domain explain_list_invar_explain_along_path' paths(1))
  then show ?thesis using explain_along_path_new_l_length 
    by (metis \<open>length l = length new_l\<close> assms(1) assms(4) paths(2))
qed

lemma explain_along_path_explain_along_path2_output_supset:
  assumes "cc_invar cc"
    "path (proof_forest cc) c p a"
    "explain_along_path2 cc a c = (output2, pend2)"
    "explain_list_invar l (proof_forest cc)" 
    "explain_along_path cc l a c = (output, new_l, pend)"
  shows "output2 \<supseteq> output"
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
    have "output = {x1} \<union> o_rec" 
      using explain_along_path_simp2[OF *] One rec 
        explain_along_path_domain[OF One(2,14,3)] True by simp
    have IH: "output2 \<supseteq> o_rec"
      using One(13) invar rec by blast
    show ?thesis 
      using IH \<open>output = {x1} \<union> o_rec\<close> by auto
  next
    case False
    then have "x = l ! a" 
      by (metis (no_types, lifting) One.hyps(3,7) One.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    then have "explain_along_path cc l x c = explain_along_path cc l a c"
      using One.hyps(2) One.hyps(3) One.prems(1) explain_along_path_parent_eq by presburger
    then show ?thesis
      using One.IH One.hyps(2,3) One.prems(1,2) explain_along_path_parent_eq 
      by (metis Un_insert_left insert_iff subsetI subset_trans sup_bot_left)
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
    have "output = {x21, x22} \<union> o_rec"
      using explain_along_path_simp3[OF *] Two rec 
        explain_along_path_domain[OF Two(2,19,3)] True by simp
    have IH: "output2 \<supseteq> o_rec"
      using Two(18) invar rec by blast
    then show ?thesis 
      using IH \<open>output = {x21, x22} \<union> o_rec\<close> Two(9,10) by blast
  next
    case False
    then have "x = l ! a" 
      by (metis (no_types, lifting) Two.hyps(3,7) Two.prems(1) explain_list_invar_def path_nodes_lt_length_l rep_of_refl)
    then have "explain_along_path cc l x c = explain_along_path cc l a c"
      using Two.hyps(2,3) Two.prems(1) explain_along_path_parent_eq by presburger
    then show ?thesis
      using Two.IH Two.hyps(2,3) Two.prems(1,2) explain_along_path_parent_eq Two(9,10)
      by (metis le_supI2)
  qed
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

lemma explain_along_path2_pending_are_congruent:
  assumes "cc_invar cc"
    "explain_along_path2 cc a c = (output, pend)"
    "path (proof_forest cc) c pAC a"
  shows "\<forall>(a,b)\<in>set pend. are_congruent cc (a \<approx> b)"
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
        then have *: "\<forall>(a,b)\<in>set pend_rec. are_congruent cc (a \<approx> b)"
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
        then have *: "\<forall>(a,b)\<in>set pend_rec. are_congruent cc (a \<approx> b)"
          using 1(3) False Two b_def p2 1(4) rec 
          by (metis option.sel)
        then have pend: "pend = [(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)] @ pend_rec" 
          using Two explain_along_path2_simp3[OF False **] explain_along_path_domain 
          using "1.hyps" "1.prems"(2) False rec \<open>pf_labels cc ! a \<noteq> None\<close> b_def rec by simp
        then have "are_congruent cc (a\<^sub>1 \<approx> b\<^sub>1)" "are_congruent cc (a\<^sub>2 \<approx> b\<^sub>2)" 
          using "1.prems" unfolding pf_labels_invar_def congruence_closure.select_convs
          by (metis "**" False are_congruent_simp option.sel path_no_root path_nodes_lt_length_l valid_vars_pending.simps(2))+
        then show ?thesis 
          using * pend by auto  
      qed
    qed
  qed
qed


end
