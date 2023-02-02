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
(*
theorem cc_explain_aux2_app:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ys . a < nr_vars cc \<and> b < nr_vars cc"
    "set xs \<subseteq> set ys"
  shows "cc_explain_aux2 cc xs \<subseteq> cc_explain_aux2 cc ys"
  using assms proof(induction "mset xs" arbitrary: ys rule: wf_induct[of "mult {(x, y). x < y}"])
  case 1
  then show ?thesis sorry
next
  case 2
  then show ?case sorry
qed
  case empty
  then show ?case 
    using cc_explain_aux2_simp1 by simp
next
  case (add x1 x2)
  then show ?case sorry
qed
  case Nil
  then show ?case 
    using cc_explain_aux2_simp1 by simp
next
  case (Cons a xs)
  then have "cc_explain_aux2 cc (a # xs) = cc_explain_aux2 cc [a] \<union> cc_explain_aux2 cc xs"
    using cc_explain_aux2_app[of cc "[a]" xs] by simp
  then obtain ys1 ys2 where ys: "ys = ys1 @ [a] @ ys2"
      using Cons.prems(4) 
      by (metis append_Cons empty_append_eq_id in_set_conv_decomp_first insert_subset list.simps(15))
    then have "cc_explain_aux2 cc ys = cc_explain_aux2 cc ys1 \<union> cc_explain_aux2 cc ([a] @ ys2)"
      using cc_explain_aux2_app[of cc "ys1" "[a] @ ys2"] Cons by simp
    also have "... = 
cc_explain_aux2 cc ys1 \<union> cc_explain_aux2 cc [a] \<union> cc_explain_aux2 cc ys2"
      using cc_explain_aux2_app[of cc "[a]" "ys2"] Cons ys by auto
    also have **: "... = cc_explain_aux2 cc [a] \<union> cc_explain_aux2 cc (ys1 @ ys2)"
      using cc_explain_aux2_app[of cc "ys1" "ys2"] Cons ys by auto
    from Cons show ?case proof(induction "count_list xs a" arbitrary: xs)
    case 0
    then have "a \<notin> set xs"
        by (metis count_list_0_iff)
    then have *: "set xs \<subseteq> set (ys1 @ ys2)"
      using ys 0(6) by auto
    have " \<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
   "\<forall>a\<in>set (ys1 @ ys2). case a of (a, b) \<Rightarrow> a < nr_vars cc \<and> b < nr_vars cc"
      using 0(4,5) ys by auto
    with 0(2,3) * have "cc_explain_aux2 cc xs \<subseteq> cc_explain_aux2 cc (ys1 @ ys2)"
      by simp
    then have "cc_explain_aux2 cc (a # xs) = cc_explain_aux2 cc [a] \<union> cc_explain_aux2 cc xs"
      using cc_explain_aux2_app[of cc "[a]" xs] 0 by simp
    then show ?case 
      using ** \<open>cc_explain_aux2 cc xs \<subseteq> cc_explain_aux2 cc (ys1 @ ys2)\<close> calculation by auto
  next
    case (Suc x)
    then obtain xs1 xs2 where xs: "xs = xs1 @ [a] @ xs2"
      using Cons.prems(4) 
      by (metis Cons_eq_appendI Suc.hyps(2) Zero_not_Suc count_notin empty_append_eq_id in_set_conv_decomp_first)
    then have "set (a # xs1 @ xs2) \<subseteq> set ys"  using Suc 
      by simp
    let ?xs = "xs1 @ xs2"
    have "(\<And>ys. cc_invar cc \<Longrightarrow>
           \<forall>(a, b)\<in>set ?xs. a < nr_vars cc \<and> b < nr_vars cc \<Longrightarrow>
           \<forall>(a, b)\<in>set ys. a < nr_vars cc \<and> b < nr_vars cc \<Longrightarrow> set ?xs \<subseteq> set ys \<Longrightarrow> cc_explain_aux2 cc ?xs \<subseteq> cc_explain_aux2 cc ys)"
      sorry
    have "x = count_list (xs1 @ xs2) a" 
      using xs Suc(2) by simp
    then have "cc_explain_aux2 cc (a # xs1 @ xs2) \<subseteq> cc_explain_aux2 cc ys"
      using Suc 
    then show ?case sorry
    
    proof(cases x)
      case 0
     
     
        sorry
      then show ?thesis sorry
    next
      case (Suc nat)
      have "set (a # xs) \<subseteq> set (ys1 @ ys2)" sorry
have " cc_explain_aux2 cc (a # xs) \<subseteq> cc_explain_aux2 cc (ys1 @ ys2)"
      using Suc(1)[OF * _ Cons(2,3) _] Cons(1) Suc(6,7) sorry
      sorry
      then show ?thesis sorry
    qed
  qed
   
    
qed

TODO  ! *)

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

(*maybe output of explain_along path 2 \<in> output and pending*)

thm was_already_in_pending.domintros
  (*lemma that was_already_in_pending terminates if explain2 terminates*)

(*TODO: prove it the same way as cc_explain2_induct*)
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

definition equations_of_l_in_pending_invar where
  "equations_of_l_in_pending_invar cc l xs \<equiv>
  (\<forall> n a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b . n < length l \<longrightarrow> l ! n \<noteq> n 
    \<longrightarrow> (pf_labels cc) ! n = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))
    \<longrightarrow> was_already_in_pending cc l [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] xs
  )"

abbreviation was_already_in_pending2 where
  "was_already_in_pending2 cc l a b xs \<equiv> 
    (cc_explain_aux2 cc [(a, b)] \<subseteq> 
      cc_explain_aux2 cc xs \<union> additional_uf_labels_set l (pf_labels cc))"


definition equations_of_l_in_pending_invar2 where
  "equations_of_l_in_pending_invar2 cc l xs \<equiv>
  (\<forall> (a, b) \<in> additional_uf_pairs_set l (pf_labels cc).
      was_already_in_pending2 cc l a b xs
  )"

lemma equations_of_l_in_pending_invar2_a_b:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "equations_of_l_in_pending_invar2 cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows 
    "was_already_in_pending2 cc new_new_l a b (pending1 @ pending2 @ xs)"
proof
  fix x
  assume "x \<in> cc_explain_aux2 cc [(a, b)]"
  obtain output12 pending12 output22 pending22 where
    defs: "(output12, pending12) = explain_along_path2 cc a c"
    "(output22, pending22) = explain_along_path2 cc b c"
    by (metis old.prod.exhaust)
  have "cc_explain_aux2 cc [(a, b)] = output12 \<union> output22 \<union>
cc_explain_aux2 cc (pending12 @ pending22)"
    using cc_explain_aux2_domain cc_explain_aux2_simp2 defs assms(1,2,3,4) 
    by auto
  have "output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
    sorry
  have "cc_explain_aux2 cc (pending12 @ pending22) \<supseteq> 
cc_explain_aux2 cc (pending1 @ pending2)"
    sorry
  then show "x \<in> cc_explain_aux2 cc (pending1 @ pending2 @ xs) \<union>
              additional_uf_labels_set new_new_l (pf_labels cc)"
    sorry
qed

lemma equations_of_l_in_pending_invar2_invar:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "equations_of_l_in_pending_invar2 cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows 
    "equations_of_l_in_pending_invar2 cc new_new_l (pending1 @ pending2 @ xs)"
  unfolding equations_of_l_in_pending_invar2_def
proof(standard, standard, standard)
  fix x x\<^sub>1 x\<^sub>2 eq
  assume eq: "x \<in> additional_uf_pairs_set new_new_l (pf_labels cc)" "x = (x\<^sub>1, x\<^sub>2)" 
    "eq \<in> cc_explain2 cc x\<^sub>1 x\<^sub>2"
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
  then show "eq \<in> cc_explain_aux2 cc (pending1 @ pending2 @ xs) \<union> additional_uf_labels_set new_new_l (pf_labels cc)"
  proof(cases "l ! n = n")
    case True
    then have "(x\<^sub>1, x\<^sub>2) \<in> set (pending1 @ pending2)" sorry
    then have "set [(x\<^sub>1, x\<^sub>2)] \<subseteq> set (pending1 @ pending2 @ xs)"
      by auto
    then have "cc_explain_aux2 cc [(x\<^sub>1, x\<^sub>2)] \<subseteq> cc_explain_aux2 cc (pending1 @ pending2 @ xs)"
      sorry
    then show ?thesis using eq valid_eqs valid_eqs 
      by blast
  next
    case False
    then have a_b: "x \<in> additional_uf_pairs_set l (pf_labels cc)" using n same_length 
      unfolding additional_uf_pairs_set_def by auto
    then have 1: "was_already_in_pending2 cc l x\<^sub>1 x\<^sub>2 ((a, b) # xs)"
      using assms(2,3,7) n same_length eq unfolding equations_of_l_in_pending_invar2_def  
      by blast
    then have "cc_explain_aux2 cc [(x\<^sub>1, x\<^sub>2)] \<subseteq> 
cc_explain_aux2 cc ((a, b) # xs) \<union> additional_uf_labels_set l (pf_labels cc)"
      by blast
    have append: "cc_explain_aux2 cc ((a, b) # xs) = cc_explain_aux2 cc [(a, b)] \<union> cc_explain_aux2 cc xs"
      using cc_explain_aux2_app[of cc "[(a, b)]" xs] assms(1,2) 
      by auto
    have 0: "was_already_in_pending2 cc new_new_l a b (pending1 @ pending2 @ xs)"
      using equations_of_l_in_pending_invar2_a_b assms by blast
       (*! TODO*)
    then have "cc_explain_aux2 cc [(a, b)] \<subseteq> 
cc_explain_aux2 cc (pending1 @ pending2 @ xs) \<union> additional_uf_labels_set new_new_l (pf_labels cc)"
      by blast
    consider "eq \<in> cc_explain_aux2 cc [(a, b)]" | "eq \<in> cc_explain_aux2 cc xs" | "eq \<in> additional_uf_labels_set l (pf_labels cc)"
      using "1" append eq(3) by auto
    then show "eq \<in> cc_explain_aux2 cc (pending1 @ pending2 @ xs) \<union> additional_uf_labels_set new_new_l (pf_labels cc)"
    proof(cases)
      case 1
      then show ?thesis 
        using "0" by blast
    next
      case 2
      have "cc_explain_aux2 cc xs \<subseteq> cc_explain_aux2 cc (pending1 @ pending2 @ xs)"
        sorry
      then show ?thesis 
        by (simp add: "2" subsetD)
    next
      case 3
      have "additional_uf_labels_set l (pf_labels cc) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
        sorry
      then show ?thesis 
        using "3" by auto
    qed
  qed
qed

lemma was_already_in_pending_larger_l:
  assumes "was_already_in_pending_dom (cc, l1, xs, pend)"
    "was_already_in_pending_dom (cc, l2, xs, pend)"
    "additional_uf_labels_set l1 (pf_labels cc) \<subseteq> 
additional_uf_labels_set l2 (pf_labels cc)"
  shows "was_already_in_pending cc l1 xs pend
\<Longrightarrow> was_already_in_pending cc l2 xs pend"
  using assms proof(induction)
  case (1 cc l pend)
  then show ?case 
    by (simp add: was_already_in_pending.domintros(1) was_already_in_pending.psimps(1))
next
  case (2 cc l a b xs pend)
  define c where "c = lowest_common_ancestor (proof_forest cc) a b"
  obtain output1 pending1 output2 pending2 where
    defs: "(output1, pending1) = explain_along_path2 cc a c"
    "(output2, pending2) = explain_along_path2 cc b c"
    by (metis old.prod.exhaust)
  then show ?case 
  proof(cases "(a, b) \<in> set pend \<and> was_already_in_pending cc l xs pend")
    case True
    have "was_already_in_pending_dom (cc, l2, xs, pend)"
      using 2(5) was_already_in_pending.domintros sorry
        (*domintros show the implication in the wrong direction; you need to show it
with inductive_cases or whatever*)
    then have "was_already_in_pending cc l2 xs pend" 
      using 2(2,5,6) was_already_in_pending.domintros 
      by (simp add: True)
    then show ?thesis        
      using 2(1,5) was_already_in_pending.psimps by (simp add: True)
  next
    case False
    then have *: "(output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend"
      using 2(1,4) was_already_in_pending.psimps(2) defs c_def unfolding Let_def
      by auto
    have dom: "was_already_in_pending_dom (cc, l2, pending1 @ pending2 @ xs, pend)" sorry
    have "(output1 \<union> output2) \<subseteq> additional_uf_labels_set l2 (pf_labels cc)"
      "was_already_in_pending cc l2 (pending1 @ pending2 @ xs) pend"
      using 2(6) 2(3) defs c_def * dom by blast+
    then show ?thesis 
      using was_already_in_pending.psimps(2)[OF 2(5)] 
        defs unfolding Let_def c_def by force
  qed
qed

lemma was_already_in_pending_larger_pend:
  assumes "was_already_in_pending_dom (cc, l, xs, pend1)"
    "was_already_in_pending_dom (cc, l, xs, pend2)"
    "set pend1 \<subseteq> set pend2"
  shows "was_already_in_pending cc l xs pend1
\<Longrightarrow> was_already_in_pending cc l xs pend2"
  using assms proof(induction)
  case (1 cc l pend)
  then show ?case 
    by (simp add: was_already_in_pending.domintros(1) was_already_in_pending.psimps(1))
next
  case (2 cc l a b xs pend)
  define c where "c = lowest_common_ancestor (proof_forest cc) a b"
  obtain output1 pending1 output2 pending2 where
    defs: "(output1, pending1) = explain_along_path2 cc a c"
    "(output2, pending2) = explain_along_path2 cc b c"
    by (metis old.prod.exhaust)
  then show ?case 
  proof(cases "(a, b) \<in> set pend \<and> was_already_in_pending cc l xs pend")
    case True
    have "was_already_in_pending_dom (cc, l, xs, pend2)"
      using 2(5) was_already_in_pending.domintros sorry
        (*domintros show the implication in the wrong direction; you need to show it
with inductive_cases or whatever*)
    then have "was_already_in_pending cc l xs pend2" 
      using 2(2,5,6) was_already_in_pending.domintros 
      by (simp add: True)
    then show ?thesis        
      using 2(1,5) was_already_in_pending.psimps "2.prems"(3) True by blast
  next
    case False
    then have *: "(output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pending1 @ pending2 @ xs) pend"
      using 2(1,4) was_already_in_pending.psimps(2) defs c_def unfolding Let_def
      by auto
    have dom: "was_already_in_pending_dom (cc, l, pending1 @ pending2 @ xs, pend2)" sorry
    have "(output1 \<union> output2) \<subseteq> additional_uf_labels_set l (pf_labels cc)"
      "was_already_in_pending cc l (pending1 @ pending2 @ xs) pend2"
      using 2(6) 2(3) defs c_def * dom by blast+
    then show ?thesis 
      using was_already_in_pending.psimps(2)[OF 2(5)] 
        defs unfolding Let_def c_def by force
  qed
qed

lemma was_already_in_pending_larger_l':
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
    "explain_list_invar l1 (proof_forest cc)"
    "a < nr_vars cc" "b < nr_vars cc"
    "are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l1 a c"
    "(output2, l2, pending2) = explain_along_path cc new_l b c"
    "was_already_in_pending cc l1 xs pend"
  shows "was_already_in_pending cc l2 xs pend"
proof-
  have "rep_of (proof_forest cc) a = rep_of (proof_forest cc) b"
    using are_congruent_implies_proof_forest_rep_of_eq assms unfolding explain_list_invar_def 
    using are_congruent_rep_of(2) by presburger
  then obtain p1 p2 where "path (proof_forest cc) c p1 a"
    "path (proof_forest cc) c p2 b" 
    using assms lowest_common_ancestor_correct unfolding proof_forest_invar_def 
      same_length_invar_def by presburger
  have "was_already_in_pending_dom (cc, l1, xs, pend)"
    "was_already_in_pending_dom (cc, l2, xs, pend)"
    "additional_uf_labels_set l1 (pf_labels cc) \<subseteq> 
additional_uf_labels_set l2 (pf_labels cc)"
    using assms was_already_in_pending_domain apply blast
    using assms was_already_in_pending_domain apply blast
    using assms additional_uf_labels_set_explain_along_path 
    by (metis Un_upper1 \<open>path (proof_forest cc) c p1 a\<close> \<open>path (proof_forest cc) c p2 b\<close> explain_list_invar_explain_along_path'' length_explain_list_cc_list sup.coboundedI1)
  then show ?thesis using was_already_in_pending_larger_l assms(11) by blast
qed

lemma was_already_in_pending_larger_pend':
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
    "was_already_in_pending cc l xs (x # pend)"
  shows "was_already_in_pending cc l xs (x # zs @ pend)"
proof-
  have "was_already_in_pending_dom (cc, l, xs, (x # pend))"
    "was_already_in_pending_dom (cc, l, xs, (x # zs @ pend))"
    "set (x # pend) \<subseteq> set (x # zs @ pend)"
    using assms was_already_in_pending_domain apply blast
    using assms was_already_in_pending_domain apply blast
    by auto
  then show ?thesis using was_already_in_pending_larger_pend assms by presburger
qed

lemma was_already_in_pending_remove_from_pend:
  assumes 
    "was_already_in_pending_dom (cc, new_new_l, ys, (pending1 @ pending2 @ xs))"
    "was_already_in_pending cc l ys ((a, b) # xs)"
    "was_already_in_pending cc new_new_l [(a, b)] (pending1 @ pending2 @ xs)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "\<forall>(a, b)\<in>set ys. a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall>(a, b)\<in>set ys. are_congruent cc (a \<approx> b)"
    "cc_invar cc"
  shows "was_already_in_pending cc new_new_l ys (pending1 @ pending2 @ xs)"
  using assms proof(induction cc new_new_l ys "pending1 @ pending2 @ xs" 
    arbitrary: rule: was_already_in_pending.pinduct)
  case (1 cc l)
  then show ?case 
    by (simp add: was_already_in_pending.domintros(1) was_already_in_pending.psimps(1))
next
  case (2 cc new_new_l a' b' ys)
  define c where "c = lowest_common_ancestor (proof_forest cc) a' b'"
  obtain out1 pend1 out2 pend2
    where defs: "(out1, pend1) = explain_along_path2 cc a' c"
      "(out2, pend2) = explain_along_path2 cc b' c"
    by (metis old.prod.exhaust)
  have recursive: "was_already_in_pending cc new_new_l ((a', b') # ys) (pending1 @ pending2 @ xs)
= ((a', b') \<in> set (pending1 @ pending2 @ xs) \<and> was_already_in_pending cc new_new_l ys (pending1 @ pending2 @ xs)) \<or> 
         (out1 \<union> out2) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)
              \<and> was_already_in_pending cc new_new_l (pend1 @ pend2 @ ys) (pending1 @ pending2 @ xs)"
    using 2(1) was_already_in_pending.psimps(2) defs c_def unfolding Let_def 
    by auto
  have waip_ys: "was_already_in_pending cc l ys ((a, b) # xs)" 
    using 2(4,9,10,11) was_already_in_pending_append[of cc "[(a', b')]" ys] by auto
  then have "was_already_in_pending cc new_new_l ys (pending1 @ pending2 @ xs)" 
    using 2(2,5,6,7,8,9,10,11)
    by simp
  have dom: "was_already_in_pending_dom (cc, l, ((a', b') # ys), ((a, b) # xs))"
    sorry
  then have *: "((a', b') \<in> set ((a, b) # xs) \<and> was_already_in_pending cc l ys ((a, b) # xs)) \<or> 
         (out1 \<union> out2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pend1 @ pend2 @ ys) ((a, b) # xs)"
    using 2(1,4) was_already_in_pending.psimps(2) defs c_def unfolding Let_def
    by auto
  then show ?case 
  proof(cases "((a', b') \<in> set ((a, b) # xs) \<and> was_already_in_pending cc l ys ((a, b) # xs))")
    case True
    have "was_already_in_pending cc new_new_l ys (pending1 @ pending2 @ xs)"
      using 2(2,5,6,7,8,9,10,11) waip_ys by auto
    then show ?thesis 
    proof(cases "(a', b') = (a, b)")
      case True': True
      have "was_already_in_pending cc new_new_l ([(a', b')] @ ys) (pending1 @ pending2 @ xs) =
    (was_already_in_pending cc new_new_l [(a', b')] (pending1 @ pending2 @ xs) \<and>
     was_already_in_pending cc new_new_l ys (pending1 @ pending2 @ xs))"
        using 2(9,10,11) was_already_in_pending_append[of cc "[(a', b')]" ys new_new_l "pending1 @ pending2 @ xs"]
        by simp
      then show ?thesis using True' 2(5)  
        using \<open>was_already_in_pending cc new_new_l ys (pending1 @ pending2 @ xs)\<close> by auto
    next
      case False
      have "(a', b') \<in> set (pending1 @ pending2 @ xs)" 
        using False True by auto
      then show ?thesis 
        by (simp add: "2.hyps"(1) \<open>was_already_in_pending cc new_new_l ys (pending1 @ pending2 @ xs)\<close> was_already_in_pending.psimps(2))
    qed
  next
    case False
    then have *: "(out1 \<union> out2) \<subseteq> additional_uf_labels_set l (pf_labels cc)
              \<and> was_already_in_pending cc l (pend1 @ pend2 @ ys) ((a, b) # xs)"
      using * by blast
    moreover have "\<forall>(a, b)\<in>set (pend1 @ pend2 @ ys). a < nr_vars cc \<and> b < nr_vars cc"
      "\<forall>(a, b)\<in>set (pend1 @ pend2 @ ys). are_congruent cc (a \<approx> b)" sorry
    ultimately have pend_rec: "was_already_in_pending cc new_new_l (pend1 @ pend2 @ ys) (pending1 @ pending2 @ xs)"
      using 2(11,5,6,7,8) 2(3)[OF c_def] defs by blast
    have "additional_uf_labels_set l (pf_labels cc) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
      using 2(6,7,8) sorry
    then show ?thesis using 2(1,4) was_already_in_pending.psimps(2) defs c_def 
        pend_rec * unfolding Let_def
      by auto
  qed
qed

lemma equations_of_l_in_pending_invar_was_already_in_pending_ab:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "equations_of_l_in_pending_invar cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows "was_already_in_pending cc new_new_l [(a, b)] (pending1 @ pending2 @ xs)"
proof-
  have dom: "was_already_in_pending_dom (cc, new_new_l, [(a, b)], (pending1 @ pending2 @ xs))"
    sorry
  obtain output12 pending12 output22 pending22 where 
    defs: "(output12, pending12) = explain_along_path2 cc a c"
    "(output22, pending22) = explain_along_path2 cc b c"
    by (metis old.prod.exhaust)
  then have "was_already_in_pending cc new_new_l [(a, b)] (pending1 @ pending2 @ xs)
= (((a, b) \<in> set (pending1 @ pending2 @ xs) \<and> was_already_in_pending cc new_new_l [] (pending1 @ pending2 @ xs)) \<or> 
          (output12 \<union> output22) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)
              \<and> was_already_in_pending cc new_new_l (pending12 @ pending22 @ []) (pending1 @ pending2 @ xs)
        )"
    using assms(4) was_already_in_pending.psimps(2)[OF dom] defs dom unfolding Let_def 
    by auto
  then have "was_already_in_pending cc new_new_l [(a, b)] (pending1 @ pending2 @ xs)
= (((a, b) \<in> set (pending1 @ pending2 @ xs)) \<or> 
          (output12 \<union> output22) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)
              \<and> was_already_in_pending cc new_new_l (pending12 @ pending22) (pending1 @ pending2 @ xs)
        )"
    using was_already_in_pending.domintros was_already_in_pending.psimps(1) 
    by auto
  have "(output12 \<union> output22) \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)"
    sorry
  have dom2: "was_already_in_pending_dom (cc, new_new_l, (pending12 @ pending22), (pending1 @ pending2 @ xs))"
    sorry
  then have "was_already_in_pending cc new_new_l (pending12 @ pending22) (pending1 @ pending2 @ xs)"
  proof(induction "cc" "new_new_l" "(pending12 @ pending22)" "(pending1 @ pending2 @ xs)" 
      arbitrary: pending12 pending22 rule: was_already_in_pending.pinduct)
    case (1 cc l pend)
    then show ?case 
      using was_already_in_pending.psimps(1) 
      by auto
  next
    case (2 cc new_new_l a' b' list pending12)
    have IH: "was_already_in_pending cc new_new_l (tl (pending12 @ pending22)) (pending1 @ pending2 @ xs)"
      using 2(2,4) by (metis append_Nil2 list.sel(3))
    then show ?case 
    proof(cases "(a', b') \<in> set (pending1 @ pending2 @ xs)")
      case True
      then show ?thesis 
        using assms(4) was_already_in_pending.psimps(2) defs IH unfolding Let_def 
        by (metis "2.hyps"(1) "2.hyps"(4) list.sel(3))
    next
      case False
      then show ?thesis sorry
    qed
  qed

  then show ?thesis 
    using \<open>output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc)\<close> \<open>was_already_in_pending cc new_new_l [(a, b)] (pending1 @ pending2 @ xs) = ((a, b) \<in> set (pending1 @ pending2 @ xs) \<or> output12 \<union> output22 \<subseteq> additional_uf_labels_set new_new_l (pf_labels cc) \<and> was_already_in_pending cc new_new_l (pending12 @ pending22) (pending1 @ pending2 @ xs))\<close> by blast
qed

lemma equations_of_l_in_pending_invar_invar:
  assumes "cc_invar cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent cc (a \<approx> b)"
    "c = lowest_common_ancestor (proof_forest cc) a b"
    "(output1, new_l, pending1) = explain_along_path cc l a c"
    "(output2, new_new_l, pending2) = explain_along_path cc new_l b c"
    "equations_of_l_in_pending_invar cc l ((a, b) # xs)"
    "explain_list_invar l (proof_forest cc)"
  shows 
    "equations_of_l_in_pending_invar cc new_new_l (pending1 @ pending2 @ xs)"
  unfolding equations_of_l_in_pending_invar_def
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix n a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b'
  assume n: "n < length new_new_l" "new_new_l ! n \<noteq> n" 
    "pf_labels cc ! n = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a') (F b\<^sub>1 b\<^sub>2 \<approx> b'))"
  have same_length: "length l = length new_new_l" using assms sorry
  have dom: "was_already_in_pending_dom (cc, new_new_l, [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)], (pending1 @ pending2 @ xs))"
    using was_already_in_pending_domain sorry
  have 0: "was_already_in_pending cc new_new_l [(a, b)] (pending1 @ pending2 @ xs)"
    sorry (*! TODO*)
  have valid_eqs: "\<forall> (a, b) \<in> set [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] . are_congruent cc (a \<approx> b)" sorry
  then show "was_already_in_pending cc new_new_l [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)]
        (pending1 @ pending2 @ xs)"
  proof(cases "l ! n = n")
    case True
    then have a_b: "(a\<^sub>1, a\<^sub>2) \<in> set (pending1 @ pending2 @ xs)
\<and> (b\<^sub>1, b\<^sub>2) \<in> set (pending1 @ pending2 @ xs)" sorry (*TODO*)
    have dom: "was_already_in_pending_dom (cc, new_new_l, [(b\<^sub>1, b\<^sub>2)], (pending1 @ pending2 @ xs))"
      sorry
    then have "was_already_in_pending cc new_new_l [(b\<^sub>1, b\<^sub>2)] (pending1 @ pending2 @ xs)"
      using a_b was_already_in_pending.psimps(2)
      using was_already_in_pending.domintros(1) was_already_in_pending.psimps(1) by force
    then show ?thesis using valid_eqs a_b valid_eqs was_already_in_pending_simp1[OF assms(1) valid_eqs] 
      by blast
  next
    case False
    then have 1: "was_already_in_pending cc l [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] ((a, b) # xs)"
      using assms(2,3,7) n same_length unfolding equations_of_l_in_pending_invar_def  
      by metis
    then have "was_already_in_pending cc new_new_l [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] ((a, b) # xs)"
      using was_already_in_pending_larger_l' valid_eqs assms 1
      by auto
    then have 2: "was_already_in_pending cc new_new_l [(a\<^sub>1, a\<^sub>2), (b\<^sub>1, b\<^sub>2)] ((a, b) # pending1 @ pending2 @ xs)"
      using was_already_in_pending_larger_pend'[OF assms(1) valid_eqs, of new_new_l "(a, b)" xs "pending1 @ pending2"]
        valid_eqs assms by auto
    show ?thesis 
      using was_already_in_pending_remove_from_pend 1 0 assms valid_eqs dom by blast 
  qed
qed



subsection \<open>Equivalence proof of \<open>cc_explain2\<close> and \<open>cc_explain\<close>\<close>

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

thm was_already_in_pending.pinduct
lemma cc_explain_aux_cc_explain_aux2_equivalence:
  assumes "was_already_in_pending_dom (cc, l, xs2, xs)"
    "cc_invar cc"
    "\<forall> (a, b) \<in> set xs2 . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs2 . are_congruent cc (a \<approx> b)"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "explain_list_invar l (proof_forest cc)" 
    "equations_of_l_in_pending_invar2 cc l xs"
    "set xs2 \<subseteq> set xs \<union> additional_uf_pairs_set l (pf_labels cc)"
    "subseq xs xs2"
  shows "cc_explain_aux2 cc xs2 \<subseteq>
cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
proof
  fix x 
  assume *: "x \<in> cc_explain_aux2 cc xs2"
  show "x \<in> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)"
    using assms * proof(induction arbitrary: xs l rule: was_already_in_pending.pinduct)
    case (1 cc l pend)
    then show ?case by (simp add: cc_explain_aux2_simp1)
  next
    case (2 cc l a b xs2 xs)
    define c where "c = lowest_common_ancestor (proof_forest cc) a b"
    obtain output12 output22 pending12 pending22 where 
      defs: "(output12, pending12) = explain_along_path2 cc a c"
      "(output22, pending22) = explain_along_path2 cc b c"
      by (metis old.prod.exhaust)
    have are_congruent: 
      "\<forall>a\<in>set (pending12 @ pending12 @ xs). case a of (a, b) \<Rightarrow> are_congruent cc (a \<approx> b)"
      sorry
    have dom: "cc_explain_aux2_dom (cc, (a, b) # xs2)" using cc_explain_aux2_domain 
      by (simp add: "2.prems"(1) "2.prems"(2))
    then have rec': "cc_explain_aux2 cc ((a, b) # xs2) =
output12 \<union> output22 \<union> cc_explain_aux2 cc (pending12 @ pending22 @ xs2)"
      using 2(6) c_def defs cc_explain_aux2_simp2 by simp
    then show ?case 
    proof(cases "xs = (a, b) # tl xs")
      case True
        (*The current pair that we consider is both in xs and in xs2 *)
      from c_def explain_along_path_lowest_common_ancestor[OF 2(4) _ _ _ c_def] 2(4,5,6) 
      obtain p1 p2 where path: "path (proof_forest cc) c p1 a"
        "path (proof_forest cc) c p2 b" 
        by auto
      obtain output1 new_l pending1 output2 new_new_l pending2 where rec: 
        "explain_along_path cc l a c = (output1, new_l, pending1)"
        "explain_along_path cc new_l b c = (output2, new_new_l, pending2)"
        by (meson prod_cases3)
      have "cc_explain_aux_dom (cc, l, ((a, b) # tl xs))" 
        using cc_explain_aux_domain[OF 2(4,8)] 2(7) True by simp
      then have cc_explain_aux: "cc_explain_aux cc l ((a, b) # tl xs) = output1 \<union> output2
\<union> cc_explain_aux cc new_new_l (pending1 @ pending2 @ tl xs)" 
        using cc_explain_aux_simp2 2(1,7,8) rec "2.prems"(3) c_def case_prodD list.set_intros(1) by auto
      have supset: "output12 \<supseteq> output1" "output22 \<supseteq> output2" sorry
      have add_uf_new_l: "additional_uf_labels_set new_new_l (pf_labels cc)
= additional_uf_labels_set l (pf_labels cc) \<union> output1 \<union> output2" sorry
      show ?thesis proof(cases "x \<in> output12 \<union> output22")
        case True': True
(* The ouput of explain2 is bigger than the output of explain, but
all the equations that are in explain2 are also present in new_new_l *)
        have "output12 \<subseteq> output1 \<union> additional_uf_labels_set l (pf_labels cc)" 
          "output22 \<subseteq> output2 \<union> additional_uf_labels_set new_l (pf_labels cc)" 
          "output1 \<union> additional_uf_labels_set l (pf_labels cc) = 
additional_uf_labels_set new_l (pf_labels cc)" 
          sorry
        then show ?thesis 
          using cc_explain_aux supset add_uf_new_l True True' by auto
      next
        case False
(* The pending list of explain2 is longer than the pending list of explain.
We can use the inducion hypothesis to show the thesis. *)
        have *: "x \<in> cc_explain_aux2 cc (pending12 @ pending22 @ xs2)"
          using False rec' 2(11) "2.prems"(9) by auto
        have invar: "equations_of_l_in_pending_invar2 cc new_new_l (pending1 @ pending2 @ tl xs)"
(*TODO*)
          "set (pending12 @ pending22 @ xs2) \<subseteq> set (pending1 @ pending2 @ tl xs) 
\<union> additional_uf_pairs_set new_new_l (pf_labels cc)"
          "subseq (pending1 @ pending2 @ tl xs) (pending12 @ pending22 @ xs2)"
          using equations_of_l_in_pending_invar2_invar sorry
        have "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2) . a < nr_vars cc \<and> b < nr_vars cc"
          "\<forall> (a, b) \<in> set (pending12 @ pending22 @ xs2) . are_congruent cc (a \<approx> b)"
          "\<forall> (a, b) \<in> set (pending1 @ pending2 @ tl xs) . a < nr_vars cc \<and> b < nr_vars cc" 
          "explain_list_invar new_new_l (proof_forest cc)" sorry
        then show ?thesis 
          using * 2(3) c_def defs 2(4) rec' are_congruent add_uf_new_l 
          by (metis True Un_iff invar cc_explain_aux)
      qed
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
        using 2(10) by auto
      then have union: "cc_explain_aux2 cc ((a, b) # xs2) =
cc_explain_aux2 cc [(a, b)] \<union> cc_explain_aux2 cc xs2"
        using cc_explain_aux2_app[ of cc "[(a, b)]" xs2]
        using "2.prems"(1,2) Cons_eq_appendI in_set_conv_decomp_first list.sel(3) by auto
      have subseq: "subseq xs xs2" using "2.prems"(8) 
        by (metis False list.collapse list_emb.simps subseq_Cons2_neq)
      have invar: "equations_of_l_in_pending_invar2 cc l xs"
        using "2.prems"(6) by simp
      show ?thesis proof(cases "x \<in> cc_explain_aux2 cc [(a, b)]")
        case True
        then have "x \<in> cc_explain_aux2 cc xs2 \<union> additional_uf_labels_set l (pf_labels cc)"
        proof-
          show ?thesis
          proof(cases "(a, b) \<in> set xs")
(* (a,b) is also present in the remaining list xs2 *)
            case True
            then have "(a, b) \<in> set xs2" 
              by (meson subseq subseq_order.trans subseq_singleton_left)
            have "cc_explain_aux2 cc [(a, b)] \<subseteq> cc_explain_aux2 cc xs2"
              sorry (* prove by induction on xs, instead of recursive calls use "cc_explain_aux2 (a,b)#xs = 
cc_explain_aux2 (a,b) \<union> cc_explain_aux2 xs*)
            then show ?thesis 
              using "2.prems"(9) union by auto
          next
            case False
(* (a, b) is in the pairs set. We can use the invariant to prove that (a, b) \<in> explain2 xs*)
            then have "(a, b) \<in> additional_uf_pairs_set l (pf_labels cc)"
              using "2.prems"(7) by force
            then have "was_already_in_pending2 cc l a b xs"
              using invar unfolding equations_of_l_in_pending_invar2_def by simp
            then have "x \<in> cc_explain_aux2 cc xs \<union> additional_uf_labels_set l (pf_labels cc)"
              using True by auto
            have "set xs \<subseteq> set xs2" using subseq 
              by (meson subseq_order.trans subseq_singleton_left subsetI)
            then have "cc_explain_aux2 cc xs \<subseteq> cc_explain_aux2 cc xs2"
              sorry
            then show ?thesis 
              using True \<open>x \<in> cc_explain_aux2 cc xs \<union> additional_uf_labels_set l (pf_labels cc)\<close> by auto
          qed
        qed
        then show ?thesis using 2(2)[OF 2(4)] 
          using "2.prems"(2-8) Un_iff union subset set_subset_Cons subseq invar by auto 
      next
        case False
        then have "x \<in> cc_explain_aux cc l xs \<union> additional_uf_labels_set l (pf_labels cc)" 
          using 2(2)[OF 2(4)]
          using "2.prems"(2-9) Un_iff union subset set_subset_Cons subseq invar by auto
        then show ?thesis 
          by simp
      qed
    qed
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