theory CC_Explain_Invar2
  imports CC_Explain2 "HOL-Library.Multiset_Order"

begin

subsubsection \<open>Equivalence of \<open>cc_explain_aux\<close> and \<open>cc_explain_aux2\<close>\<close>


fun pending_pairs :: "pending_equation option \<Rightarrow> (nat * nat) set"
  where
    "pending_pairs None = {}"
  | "pending_pairs (Some (One a)) = {}"
  | "pending_pairs (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))) = {(a\<^sub>1, b\<^sub>1), (a\<^sub>2, b\<^sub>2)}"
  | "pending_pairs (Some (Two a b)) = {}"

definition additional_uf_pairs_set where
  "additional_uf_pairs_set l pfl \<equiv> \<Union>{pending_pairs (pfl ! a) |a. a < length l \<and> l ! a \<noteq> a}"

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
      obtain output1 pending1 output2 pending2
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

subsubsection \<open>Lemma about \<open>cc_explain2\<close> and append and subset\<close>

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

lemma cc_explain_aux2_union:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
  shows "cc_explain_aux2 cc xs = \<Union>{cc_explain_aux2 cc [x] |x. x \<in> set xs}"
using assms proof(induction xs)
  case Nil
  then show ?case 
    using cc_explain_aux2_simp1 by fastforce
next
  case (Cons a xs)
  then have "cc_explain_aux2 cc xs = \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set xs}" 
    by simp
  moreover have "cc_explain_aux2 cc (a # xs) = cc_explain_aux2 cc [a] \<union> cc_explain_aux2 cc xs"
"set (a # xs) = {a} \<union> set xs"
    using cc_explain_aux2_app[of cc "[a]" xs] Cons by auto
  moreover have "\<Union> {cc_explain_aux2 cc [x] |x. x \<in> set (a # xs)} = 
\<Union> {cc_explain_aux2 cc [x] |x. x \<in> {a}} \<union> \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set xs}"
    by fastforce
  moreover have "\<Union> {cc_explain_aux2 cc [x] |x. x \<in> {a}} = cc_explain_aux2 cc [a]"
    by blast
  ultimately show ?case using cc_explain_aux2_app 
    by auto
qed

theorem cc_explain_aux2_subset:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ys . a < nr_vars cc \<and> b < nr_vars cc"
    "set xs \<subseteq> set ys"
  shows "cc_explain_aux2 cc xs \<subseteq> cc_explain_aux2 cc ys"
proof-
  have "cc_explain_aux2 cc xs = \<Union>{cc_explain_aux2 cc [x] |x. x \<in> set xs}"
    using cc_explain_aux2_union assms by simp
  moreover have "cc_explain_aux2 cc ys = \<Union>{cc_explain_aux2 cc [y] |y. y \<in> set ys}"
    using cc_explain_aux2_union assms by simp
  ultimately show ?thesis using assms 
    by blast
qed


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
        (((a, b) \<in> set pend \<and> was_already_in_pending cc l xs pend) \<or> 
        (let c = lowest_common_ancestor (proof_forest cc) a b;
             (output1, pending1) = explain_along_path2 cc a c;
             (output2, pending2) = explain_along_path2 cc b c
         in (output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend
        )
     )
"
  by pat_completeness auto

thm was_already_in_pending.domintros
  (*lemma that was_already_in_pending terminates if explain2 terminates*)

(*TODO: prove it the same way as cc_explain2_dom*)
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
  from 2 have congruent: "are_congruent cc (a \<approx> b)" 
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
    by (metis "2.prems"(3) explain_along_path_lowest_common_ancestor length)
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
  then have *: "was_already_in_pending_dom (cc, l, pending1 @ pending2 @ xs, pend)" 
    using 2(2)[OF congruent c_def defs(1) _ defs(2) _ 4 2(6)] by blast
  then have "was_already_in_pending_dom (cc, l, xs, pend)"
    sorry
  then show ?case 
    using was_already_in_pending.domintros c_def defs 2(5,6) *
    sorry
qed

theorem was_already_in_pending_domain:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
  shows "was_already_in_pending_dom (cc, l, xs, pend)"
  using assms explain2_dom_imp_was_already_in_pending_dom cc_explain_aux2_domain 
  by blast

lemma was_already_in_pending_simp1:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "(a, b) \<in> set pend \<and> was_already_in_pending cc l xs pend"
  shows "was_already_in_pending cc l ((a, b) # xs) pend"
proof-
  have "was_already_in_pending_dom (cc, l, (a, b) # xs, pend)"
    using assms was_already_in_pending_domain by blast
  then show ?thesis 
    using was_already_in_pending.psimps(2) assms unfolding Let_def by auto
qed

lemma was_already_in_pending_simp2:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, pending1) = explain_along_path2 cc a c"
    "(output2, pending2) = explain_along_path2 cc b c"
  shows "was_already_in_pending cc l ((a, b) # xs) pend
= (((a, b) \<in> set pend \<and> was_already_in_pending cc l xs pend) 
    \<or> (output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend)"
proof-
  have "was_already_in_pending_dom (cc, l, (a, b) # xs, pend)"
    using assms was_already_in_pending_domain by blast
  then show ?thesis 
    using was_already_in_pending.psimps(2) assms unfolding Let_def by auto
qed

lemma was_already_in_pending_simp3:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, pending1) = explain_along_path2 cc a c"
    "(output2, pending2) = explain_along_path2 cc b c"
    "(a, b) \<notin> set pend"
  shows "was_already_in_pending cc l ((a, b) # xs) pend
= ((output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend)"
proof-
  show ?thesis 
    using was_already_in_pending_simp2 assms by blast
qed

lemma was_already_in_pending_append: 
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
    "\<forall> (a, b) \<in> set ys . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ys . are_congruent cc (a \<approx> b)"
  shows "was_already_in_pending cc l (xs @ ys) pend = 
(was_already_in_pending cc l xs pend \<and> was_already_in_pending cc l ys pend)"
proof-
  from assms have "was_already_in_pending_dom (cc, l, xs, pend)"
    using was_already_in_pending_domain by presburger
  then show ?thesis
    using assms proof(induction rule: was_already_in_pending.pinduct)
    case (1 cc l pend)
    then show ?case 
      by (simp add: was_already_in_pending.psimps(1))
  next
    case (2 cc l a b xs pend)
    then have length: "a < length (proof_forest cc)" "b < length (proof_forest cc)"
      using 2(4,5) unfolding same_length_invar_def by auto
    define c where "c = lowest_common_ancestor (proof_forest cc) a b"
    then obtain p1 p2 where p: "path (proof_forest cc) c p1 a"
      "path (proof_forest cc) c p2 b" using 2(5,6) lowest_common_ancestor_correct 
      unfolding proof_forest_invar_def same_length_invar_def 
      using explain_along_path_lowest_common_ancestor length 
      by (metis "2.prems"(1) case_prod_conv list.set_intros(1))
    obtain output1 pending1 output2 pending2 where
      defs: "(output1, pending1) = explain_along_path2 cc a c"
      "(output2, pending2) = explain_along_path2 cc b c"
      by (metis old.prod.exhaust)
    from 2 have xs_valid: "\<forall>(a, b)\<in>set ((a, b) # xs @ ys). a < nr_vars cc \<and> b < nr_vars cc" 
      "\<forall>(a, b)\<in>set ((a, b) # xs @ ys). are_congruent cc (a \<approx> b)"
      by auto
    have pending_valid: "\<forall>a\<in>set (pending1 @ pending2). case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)"
      "\<forall>a\<in>set (pending1 @ pending2). case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
      using explain_along_path2_pending' p 2(4) defs apply metis
      using explain_along_path2_pending_in_bounds[OF 2(4) defs(1)[symmetric] p(1)]
        explain_along_path2_pending_in_bounds[OF 2(4) defs(2)[symmetric] p(2)] by auto
    then have pending_valid: "\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)"
      "\<forall>a\<in>set (pending1 @ pending2 @ xs). case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
      using p 2(5,6) by auto
    then have IH1: "was_already_in_pending cc l ((pending1 @ pending2 @ xs) @ ys) pend =
    (was_already_in_pending cc l (pending1 @ pending2 @ xs) pend \<and>
     was_already_in_pending cc l ys pend)" using 2(3) c_def defs 
      using "2.prems"(1,4,5) pending_valid by presburger          
    then have IH2: "was_already_in_pending cc l (xs @ ys) pend = 
(was_already_in_pending cc l xs pend \<and> was_already_in_pending cc l ys pend)"
      using 2(2) c_def defs 
      using "2.prems"(1,4,5) pending_valid by simp
    then show ?case
    proof(cases "(a, b) \<in> set pend")
      case True
      then have rec1: "was_already_in_pending cc l ((a, b) # xs) pend
= (((was_already_in_pending cc l xs pend) 
    \<or> (output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend))"
        using was_already_in_pending_simp2 True 2(1,4-) c_def defs by blast
      then have rec2: "was_already_in_pending cc l ((a, b) # (xs @ ys)) pend
= ((was_already_in_pending cc l (xs @ ys) pend) 
    \<or> (output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ (xs @ ys)) pend)"
        using was_already_in_pending_simp2[of cc a b "xs @ ys"] c_def True 2(1,4-) xs_valid defs by presburger
      then show ?thesis using IH2 rec1 IH1 by auto
    next
      case False
      then have rec1: "was_already_in_pending cc l ((a, b) # xs) pend
= ((output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend)"
        using was_already_in_pending_simp3 False 2(1,4-) c_def defs by blast
      from xs_valid have rec2: "was_already_in_pending cc l ((a, b) # (xs @ ys)) pend
= ((output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ (xs @ ys)) pend)"
        using was_already_in_pending_simp3[of cc a b "xs @ ys"] c_def False 2(1,4-) defs by auto
      from IH1 show ?thesis 
        by (simp add: rec2 rec1)
    qed
  qed
qed

text \<open>Invariant\<close>

definition was_already_in_pending3 where
  "was_already_in_pending3 cc l a b xs \<equiv> 
    (((a, b) \<in> set xs) \<or> 
        (let c = lowest_common_ancestor (proof_forest cc) a b;
             (output1, pending1) = explain_along_path2 cc a c;
             (output2, pending2) = explain_along_path2 cc b c
         in ((output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
            \<and> set pending1 \<union> set pending2 \<subseteq> additional_uf_pairs_set l (pf_labels cc))
        ))"

definition equations_of_l_in_pending_invar3 where
  "equations_of_l_in_pending_invar3 cc l xs \<equiv>
  (\<forall> (a, b) \<in> additional_uf_pairs_set l (pf_labels cc).
      was_already_in_pending3 cc l a b xs
  )"

lemma equations_of_l_in_pending_invar3_a_b:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "equations_of_l_in_pending_invar3 cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows 
    "was_already_in_pending3 cc new_new_l a b (pending1 @ pending2 @ xs)"
proof-
  obtain output12 pending12 output22 pending22 where
defs: "(output12, pending12) = explain_along_path2 cc a c"
         "(output22, pending22) = explain_along_path2 cc b c"
    by (metis old.prod.exhaust)
have "output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
    sorry
  moreover have "set pending12 \<union> set pending22 \<subseteq>
additional_uf_pairs_set new_new_l (pf_labels cc)"
    sorry
  ultimately show ?thesis unfolding was_already_in_pending3_def Let_def using defs 
    using assms(4) by force
qed

lemma equations_of_l_in_pending_invar3_invar:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "equations_of_l_in_pending_invar3 cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows 
    "equations_of_l_in_pending_invar3 cc new_new_l (pending1 @ pending2 @ xs)"
  unfolding equations_of_l_in_pending_invar3_def
proof(standard, standard)
  fix x x\<^sub>1 x\<^sub>2
  assume eq: "x \<in> additional_uf_pairs_set new_new_l (pf_labels cc)" "x = (x\<^sub>1, x\<^sub>2)" 
  then obtain n where n: "n < length new_new_l \<and> new_new_l ! n \<noteq> n"
    "x \<in> pending_pairs (pf_labels cc ! n)" unfolding additional_uf_pairs_set_def 
    by blast
  from n(2) obtain a\<^sub>1 a\<^sub>2  a' b\<^sub>1 b\<^sub>2 b' where "pf_labels cc ! n = (Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b')))"
    "x = (a\<^sub>1, b\<^sub>1) \<or> x = (a\<^sub>2, b\<^sub>2)"
    using pending_pairs.cases 
    by (metis insert_iff memb_imp_not_empty pending_pairs.elims)
  have same_length: "length l = length new_new_l" using assms sorry

  have valid_eqs: "a < nr_vars cc \<and> b < nr_vars cc"
    "are_congruent cc (a \<approx> b)" sorry
  show "was_already_in_pending3 cc new_new_l x\<^sub>1 x\<^sub>2 (pending1 @ pending2 @ xs)"
    unfolding was_already_in_pending3_def
  proof- 
    define c where "c = lowest_common_ancestor (proof_forest cc) x\<^sub>1 x\<^sub>2"
    obtain output12 pending12 output22 pending22 where 
      rec: "(output12, pending12) = explain_along_path2 cc x\<^sub>1 c"
      "(output22, pending22) = explain_along_path2 cc x\<^sub>2 c" 
      by (metis old.prod.exhaust)
    have "was_already_in_pending3 cc new_new_l a b (pending1 @ pending2 @ xs)"
      using equations_of_l_in_pending_invar3_a_b assms by simp
    have "(x\<^sub>1, x\<^sub>2) \<in> set (pending1 @ pending2 @ xs) \<or>
    (output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc) \<and>
        set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc))"
    proof(cases "l ! n = n")
      case True
      then have "(x\<^sub>1, x\<^sub>2) \<in> set (pending1 @ pending2)" sorry
      then show ?thesis 
        by auto
    next
      case False
      then have a_b: "x \<in> additional_uf_pairs_set l (pf_labels cc)" using n same_length 
        unfolding additional_uf_pairs_set_def by auto
      then have 1: "was_already_in_pending3 cc l x\<^sub>1 x\<^sub>2 ((a, b) # xs)"
        using assms(2,3,7) n same_length eq unfolding equations_of_l_in_pending_invar3_def  
        by blast
      then have 2: "((x\<^sub>1, x\<^sub>2) \<in> set ((a, b) # xs)) \<or> (output12 \<union> output22 \<subseteq> additional_uf_labels_set l (pf_labels cc) \<and>
      set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set l (pf_labels cc))"
        unfolding was_already_in_pending3_def Let_def using rec c_def by force
      have subset: "additional_uf_labels_set l (pf_labels cc) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
        "additional_uf_pairs_set l (pf_labels cc) \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
        sorry
      have append: "cc_explain_aux2 cc ((a, b) # xs) = cc_explain_aux2 cc [(a, b)] \<union> cc_explain_aux2 cc xs"
        using cc_explain_aux2_app[of cc "[(a, b)]" xs] assms(1,2) 
        by auto
      have 0: "was_already_in_pending3 cc new_new_l a b (pending1 @ pending2 @ xs)"
        using equations_of_l_in_pending_invar3_a_b assms by blast
      consider "(x\<^sub>1, x\<^sub>2) = (a, b)" | "(x\<^sub>1, x\<^sub>2) \<in> set xs" | "output12 \<union> output22 \<subseteq> additional_uf_labels_set l (pf_labels cc) \<and>
      set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set l (pf_labels cc)"
        by (meson "2" set_ConsD)
      then show ?thesis proof(cases)
        case 1
        then show ?thesis using 0 unfolding was_already_in_pending3_def Let_def 
          using c_def local.rec(1) local.rec(2) by force
      next
        case 2
        then show ?thesis 
          by force
      next
        case 3
        then show ?thesis using subset 
          by (meson subset_trans)
      qed
    qed
    then show "(x\<^sub>1, x\<^sub>2) \<in> set (pending1 @ pending2 @ xs) \<or>
    (let c = lowest_common_ancestor (proof_forest cc) x\<^sub>1 x\<^sub>2; (output1, pending1) = explain_along_path2 cc x\<^sub>1 c;
         (output2, pending2) = explain_along_path2 cc x\<^sub>2 c
     in output1 \<union> output2 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc) \<and>
        set pending1 \<union> set pending2 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc))" 
      unfolding was_already_in_pending3_def Let_def 
      using c_def local.rec(1) local.rec(2) by force
  qed
qed

subsection \<open>Equivalence proof of \<open>cc_explain2\<close> and \<open>cc_explain\<close>\<close>

subsubsection \<open>Lemmata about \<open>cc_explain_along_path\<close> and \<open>cc_explain_along_path2\<close>\<close>


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
      by (smt (verit) Two.hyps(2-7) Two.prems(1) True explain_list_invar_def invar nth_list_update_eq path_nodes_lt_length_l path_root)
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
      using * Two 
      by (smt (verit, del_insts) False explain_along_path_new_l_unchanged length_explain_list_cc_list path_nodes_lt_length_l rep_of_refl same_length_invar_def)
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

subsubsection \<open>Equivalence of \<open>explain_along_path\<close> and \<open>explain_along_path2\<close>\<close>

thm was_already_in_pending.pinduct
lemma cc_explain_aux_cc_explain_aux2_equivalence:
  assumes "was_already_in_pending_dom (cc, l, xs2, xs)"
    "cc_invar cc"
    "\<forall> (a, b) \<in> set xs2 . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs2 . are_congruent cc (a \<approx> b)"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
    "explain_list_invar l (proof_forest cc)" 
    "equations_of_l_in_pending_invar3 cc l xs" 
    "set xs2 \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)"
    "subseq xs xs2"
  shows "cc_explain_aux2 cc xs2 \<subseteq>
cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
  using assms proof(induction arbitrary: xs l rule: was_already_in_pending.pinduct)
  case (1 cc l pend)
  then show ?case by (simp add: cc_explain_aux2_simp1)
next
  case (2 cc l a b xs2 xs)
  define c where "c = lowest_common_ancestor (proof_forest cc) a b"
  obtain output12 output22 pending12 pending22 where 
    defs: "explain_along_path2 cc a c = (output12, pending12)"
    "explain_along_path2 cc b c = (output22, pending22)"
    by (metis old.prod.exhaust)
  obtain p1 p2 where path: "path (proof_forest cc) c p1 a"
"path (proof_forest cc) c p2 b"
    using c_def lowest_common_ancestor_correct 2(4,5,6) proof_forest_invar_def 
same_length_invar_def are_congruent_rep_of by fastforce
  then have are_congruent: 
    "\<forall>a\<in>set (pending12 @ pending12 @ xs). case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)"
    using explain_along_path2_pending' 2(8) 2(4) defs
    by fastforce
  have dom: "cc_explain_aux2_dom (cc, (a, b) # xs2)" using cc_explain_aux2_domain 
    by (simp add: "2.prems"(1) "2.prems"(2))
  then have rec': "cc_explain_aux2 cc ((a, b) # xs2) =
output12 \<union> output22 \<union> cc_explain_aux2 cc (pending12 @ pending22 @ xs2)"
    using 2(6) c_def defs cc_explain_aux2_simp2 by simp
  then show ?case 
  proof(cases "xs = (a, b) # tl xs")
    case True
      (* The current pair that we consider is both in xs and in xs2 *)
    obtain output1 new_l pending1 output2 new_new_l pending2 where rec: 
      "explain_along_path cc l a c = (output1, new_l, pending1)"
      "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
      by (meson prod_cases3)
    have "cc_explain_aux_dom (cc, l, ((a, b) # tl xs))" 
      using cc_explain_aux_domain[OF 2(4,9)] 2(7) True by simp
    then have cc_explain_aux: "cc_explain_aux cc l ((a, b) # tl xs) = output1 \<union> output2
\<union> cc_explain_aux cc new_new_l (pending1 @ pending2 @ tl xs)" 
      using cc_explain_aux_simp2 2(1,7,8) rec "2.prems"(3) c_def case_prodD list.set_intros(1) by auto
    have eli: "explain_list_invar new_l (proof_forest cc)" using explain_list_invar_explain_along_path' 
      using "2.prems"(1) "2.prems"(6) explain_along_path_domain local.rec(1) path(1) by blast
have *: "\<forall> (a, b) \<in> set pending12 . a < nr_vars cc \<and> b < nr_vars cc"
"\<forall> (a, b) \<in> set pending22 . a < nr_vars cc \<and> b < nr_vars cc"
"\<forall> (a, b) \<in> set pending12 . are_congruent cc (a \<approx> b)"
"\<forall> (a, b) \<in> set pending22 . are_congruent cc (a \<approx> b)"
"\<forall> (a, b) \<in> set pending1 . a < nr_vars cc \<and> b < nr_vars cc"
"\<forall> (a, b) \<in> set pending2 . a < nr_vars cc \<and> b < nr_vars cc"
"\<forall> (a, b) \<in> set pending1 . are_congruent cc (a \<approx> b)"
"\<forall> (a, b) \<in> set pending2 . are_congruent cc (a \<approx> b)"
        using 2(4) explain_along_path2_pending_in_bounds defs path explain_along_path2_pending_are_congruent
explain_along_path_pending_in_bounds 
             apply blast+
        using explain_along_path_pending_in_bounds path 2(4,9) 
         apply (simp add: local.rec eli)
        using explain_along_path_pending_in_bounds path 2(4,9) 
        using case_prodI2 eli local.rec(2) snd_conv apply simp
        using explain_along_path_pending_are_congruent  path 2(4,9)  
        using local.rec(1) apply presburger
using explain_along_path_pending_are_congruent  path 2(4,9) eli local.rec(2) by blast 
      then have in_bounds: "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2) . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2) . are_congruent cc (a \<approx> b)"
        "\<forall> (a, b) \<in> set (pending1 @ pending2 @ tl xs) . a < nr_vars cc \<and> b < nr_vars cc" 
        "\<forall> (a, b) \<in> set (pending1 @ pending2 @ tl xs) . are_congruent cc (a \<approx> b)" 
        "explain_list_invar new_new_l (proof_forest cc)" 
        using 2(5,6) apply auto[2]
        using * 2(7,8) apply (metis UnE in_set_tlD set_union_code)
        using * 2(7,8) apply (metis UnE in_set_tlD set_union_code)
        using eli explain_list_invar_explain_along_path' 
        using "2.prems"(1) explain_along_path_domain local.rec(2) path(2) by blast
      from eli have supset: "output12 \<supseteq> output1" "output22 \<supseteq> output2" 
      using explain_along_path_explain_along_path2_output_supset defs path 2 rec 
      by metis+
    have add_uf_new_l': "additional_uf_labels_set new_l (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> output1" 
      "additional_uf_labels_set new_new_l (pf_labels cc)
= additional_uf_labels_set new_l (pf_labels cc) \<union> output2"
      using additional_uf_labels_set_explain_along_path  
      using "2.prems"(1) "2.prems"(6) local.rec path eli by auto
    then have add_uf_new_l: "additional_uf_labels_set new_new_l (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> output1 \<union> output2" 
      by simp
    have *: "output12 \<union> output22
    \<subseteq> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)" 
    proof-
      (* The output of explain2 is bigger than the output of explain, but
all the equations that are in explain2 are also present in new_new_l *)
      have "output12 \<subseteq> output1 \<union> additional_uf_labels_set l (pf_labels cc)" 
        "output22 \<subseteq> output2 \<union> additional_uf_labels_set new_l (pf_labels cc)" 
        "output1 \<union> additional_uf_labels_set l (pf_labels cc) = 
additional_uf_labels_set new_l (pf_labels cc)" 
        using add_uf_new_l' explain_along_path_explain_along_path2_output_subset[OF 2(4) path(1) _ 2(9)] rec defs path 
          apply blast
        using add_uf_new_l' explain_along_path_explain_along_path2_output_subset[OF 2(4) path(2) _ eli] rec defs path 
         apply blast
        using add_uf_new_l' by blast
      then show ?thesis 
        using cc_explain_aux supset add_uf_new_l True by auto
    qed
    have "cc_explain_aux2 cc (pending12 @ pending22 @ xs2)
\<subseteq> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
      (* The pending list of explain2 is longer than the pending list of explain.
We can use the induction hypothesis to show the thesis. *)
    proof-
      have invar_eofip: "equations_of_l_in_pending_invar3 cc new_new_l (pending1 @ pending2 @ tl xs)"
        using equations_of_l_in_pending_invar3_invar c_def rec "2.prems" True by metis
(*TODO: What if (a, b) is in xs2 but not in tl xs ! !*)
      then show ?thesis
      proof(cases "(a, b) \<in> set (tl xs)")
        case True': True
        have "set xs = set (tl xs) \<union> {(a, b)}"
"set ((a, b) # xs2) = set xs2 \<union> {(a,b)}" using "2.prems"(8) True 
           apply (metis Un_insert_right list.simps(15) sup_bot_right)
          by auto
        then have "set xs2 \<subseteq> set (tl xs) \<union> additional_uf_pairs_set l (pf_labels cc)" 
          using "2.prems"(8) True True' by blast
have aups_n_l: "additional_uf_pairs_set new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pending1" sorry
        have aups_n_n_l: "additional_uf_pairs_set new_new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pending1 \<union> set pending2"
          sorry

        have pending_subset: "set pending12 \<subseteq> additional_uf_pairs_set new_l (pf_labels cc)"
"set pending22 \<subseteq> additional_uf_pairs_set new_new_l (pf_labels cc)"
          using explain_along_path_explain_along_path2_pending_subset[OF 2(4) path(1) defs(1)] 
          using "2.prems"(6) rec(1) apply blast
          using explain_along_path_explain_along_path2_pending_subset[OF 2(4) path(2) defs(2)] 
          using eli rec(2) by blast
        have pending_subseq: "subseq pending1 pending12" "subseq pending2 pending22" "subseq (tl xs) xs2"
          using explain_along_path_explain_along_path2_pending_subseq 2(4) path(1) defs(1) "2.prems"(6) rec(1) 
            apply blast
          using explain_along_path_explain_along_path2_pending_subseq 2(4) path(2) defs(2) eli rec(2) 
           apply blast
          using 2(12) by (metis True subseq_Cons2')
        have "set xs2 \<subseteq> set (tl xs) \<union> additional_uf_pairs_set l (pf_labels cc)" 
          using True 2(11) by (simp add: \<open>set xs2 \<subseteq> set (tl xs) \<union> additional_uf_pairs_set l (pf_labels cc)\<close>)
        then have "set (pending12 @ pending22 @ xs2)
    \<subseteq> set (pending1 @ pending2 @ tl xs) \<union> additional_uf_pairs_set new_new_l (pf_labels cc)" 
        "subseq (pending1 @ pending2 @ tl xs) (pending12 @ pending22 @ xs2)" 
          using pending_subset aups_n_l aups_n_n_l apply auto[1]
          using pending_subseq by (simp add: list_emb_append_mono)
        then have IH: "cc_explain_aux2 cc (pending12 @ pending22 @ xs2)
\<subseteq> cc_explain_aux cc new_new_l (pending1 @ pending2 @ tl xs) \<union> 
additional_uf_labels_set new_new_l (pf_labels cc)"
        using 2(3) c_def defs 2(4) in_bounds invar_eofip 
        by metis
      then show ?thesis 
        using IH True add_uf_new_l cc_explain_aux by auto
      next
        case False
        define xs2' where "xs2' = removeAll (a, b) xs2"
        have "cc_explain_aux2 cc ((a, b) # xs2') = cc_explain_aux2 cc ((a, b) # xs2)"
          sorry
        have "subseq xs xs2'" using False "2.prems"(9) xs2'_def sorry
have in_bounds': "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2') . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2') . are_congruent cc (a \<approx> b)" sorry
        then have "set (pending12 @ pending22 @ xs2')
    \<subseteq> set (pending1 @ pending2 @ tl xs) \<union> additional_uf_pairs_set new_new_l (pf_labels cc)" 
        "subseq (pending1 @ pending2 @ tl xs) (pending12 @ pending22 @ xs2')" 
          using "2.prems"(8) sorry
        then have IH: "cc_explain_aux2 cc (pending12 @ pending22 @ xs2')
\<subseteq> cc_explain_aux cc new_new_l (pending1 @ pending2 @ tl xs) \<union> 
additional_uf_labels_set new_new_l (pf_labels cc)"
          using 2(3)[OF ] c_def defs 2(4) in_bounds(3-) invar_eofip in_bounds' 
          sorry
      have "additional_uf_pairs_set new_new_l (pf_labels cc) = 
additional_uf_pairs_set l (pf_labels cc) \<union> set pending1 \<union> set pending2"
        sorry
      then show ?thesis 
        using IH True add_uf_new_l cc_explain_aux sorry
      qed



    qed
    then show ?thesis using defs c_def rec' "*" by blast
  next
    case False
      (* The current pair that we consider is only in xs2, and not in xs.
We must prove that the added output and the added elements in pending 
are also present in explain xs.

The invariant equations_of_l_in_pending_invar states that all the edges
that are present in explain2 and not in explain were already in the pending list
sometime before this point.
*)
    then have subset: "set xs2 \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)"
      using 2(11) by auto
    then have union: "cc_explain_aux2 cc ((a, b) # xs2) =
cc_explain_aux2 cc [(a, b)] \<union> cc_explain_aux2 cc xs2"
      using cc_explain_aux2_app[ of cc "[(a, b)]" xs2]
      using "2.prems"(1,2) Cons_eq_appendI in_set_conv_decomp_first list.sel(3) by auto
    have subseq: "subseq xs xs2" using "2.prems"(9) 
      by (metis False list.collapse list_emb.simps subseq_Cons2_neq)
    have *: "cc_explain_aux2 cc ((a, b) # xs2) \<subseteq> 
      cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
    proof-
      show ?thesis
      proof(cases "(a, b) \<in> set xs")
        (* (a,b) is also present in the remaining list xs2 *)
        case True
        then have "(a, b) \<in> set xs2" 
          by (meson subseq subseq_order.trans subseq_singleton_left)
        then have set_eq: "set ((a, b) # xs2) = set xs2" 
          by auto
        have "cc_explain_aux2 cc ((a, b) # xs2) = \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set ((a, b) # xs2)}"
          using cc_explain_aux2_union 2(4,5) 
          by blast
        also have "... = \<Union> {cc_explain_aux2 cc [x] |x. x \<in> set xs2}"
          using cc_explain_aux2_union 2(4,5) set_eq by auto
        also have "... = cc_explain_aux2 cc xs2"
          using cc_explain_aux2_union 2(4,5) by auto
        finally show ?thesis 
          using 2(2)[OF 2(4)] 
          using "2.prems"(2-7) Un_iff union subset set_subset_Cons subseq by auto 
      next
        case False
          (* (a, b) is in the pairs set. We can use the invariant to prove that (a, b) \<in> explain2 xs*)
          (*or show that we can use here new_new_l instead of l, the one derived ba eap with the first element of
              xs. then use IH somehow idk or not*)
          (* make l bigger so i can show that its in there, like explain2 (pairs) \<union> l for the right hand side of equality \<subseteq>*)
        then have "(a, b) \<in> additional_uf_pairs_set l (pf_labels cc)"
          using "2.prems"(8) by force
        with "2.prems"(7) have invariant: "output12 \<union> output22 \<subseteq> additional_uf_labels_set l (pf_labels cc) \<and>
         set pending12 \<union> set pending22 \<subseteq> additional_uf_pairs_set l (pf_labels cc)" 
          unfolding equations_of_l_in_pending_invar3_def was_already_in_pending3_def Let_def
          using False defs c_def by force
        then have subset: "set (pending12 @ pending22 @ xs2) \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)" 
          using subset by auto
        have subseq_xs: "subseq xs (pending12 @ pending22 @ xs2)" 
          by (simp add: subseq subseq_drop_many)
have *: "\<forall> (a, b) \<in> set pending12 . a < nr_vars cc \<and> b < nr_vars cc"
"\<forall> (a, b) \<in> set pending22 . a < nr_vars cc \<and> b < nr_vars cc"
"\<forall> (a, b) \<in> set pending12 . are_congruent cc (a \<approx> b)"
"\<forall> (a, b) \<in> set pending22 . are_congruent cc (a \<approx> b)"
        using 2(4) explain_along_path2_pending_in_bounds defs path explain_along_path2_pending_are_congruent
explain_along_path_pending_in_bounds 
        by blast+
      then have in_bounds: "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2) . a < nr_vars cc \<and> b < nr_vars cc"
        "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2) . are_congruent cc (a \<approx> b)"
        using 2(5,6) by auto
        have IH: "cc_explain_aux2 cc (pending12 @ pending22 @ xs2) 
\<subseteq> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)" using 2(3)[OF c_def _ _ _ _ 2(4) in_bounds] 
defs "2.prems" 
          using subset subseq_xs by metis
        then show ?thesis 
          using invariant rec' by auto
      qed
    qed
    then show ?thesis 
      using "2.prems"(2-7) Un_iff  set_subset_Cons by blast
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