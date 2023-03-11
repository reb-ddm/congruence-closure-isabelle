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

subsubsection \<open>Invariant which states, that the timestamps decrease during the execution of 
\<open>cc_explain\<close>\<close>

function (domintros) path_to_c :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "path_to_c pf a c = (if a = c then [] else (path_to_c pf (pf ! a) c) @ [a])"
  by pat_completeness auto

lemma path_to_c_domain:
  assumes "path l c p a"
  shows "path_to_c_dom (l, a, c)"
  using assms proof(induction "length p" arbitrary: p a)
  case 0
  then show ?case
    by (metis length_0_conv path_not_empty)
next
  case (Suc x)
  then show ?case
  proof(cases "a = c")
    case True
    then show ?thesis 
      using path_to_c.domintros by blast
  next
    case False
    from Suc obtain x' p' where "p = p' @ [x']"
      by (metis neq_Nil_rev_conv path_not_empty)
    then have "p' = butlast p" 
      by simp
    then have "path l c p' (l ! a)" 
      using path_butlast False Suc.prems by auto
    then show ?thesis 
      by (metis Suc.hyps(1) Suc.hyps(2) \<open>p = p' @ [x']\<close> diff_add_inverse length_append_singleton path_to_c.domintros plus_1_eq_Suc)
  qed
qed

lemma path_to_c_correct:
  assumes "path l c p a" "ufa_invar l"
  shows "path_to_c l a c = tl p"
  using assms proof(induction "length p" arbitrary: p a)
  case 0
  then show ?case
    by (metis length_0_conv path_not_empty)
next
  case (Suc x)
  then show ?case
  proof(cases "a = c")
    case True
    have "path l c [a] a" 
      using True assms path_nodes_lt_length_l single by auto
    then have "p = [a]" 
      using Suc.prems(1) assms(2) path_unique by auto
    then show ?thesis 
      using path_to_c.psimps path_to_c_domain Suc True list.sel(3) by force
  next
    case False
    from Suc obtain x' p' where "p = p' @ [x']"
      by (metis neq_Nil_rev_conv path_not_empty)
    then have "p' = butlast p" 
      by simp
    then have "path l c p' (l ! a)" 
      using path_butlast False Suc.prems by auto
    then have "path_to_c l (l ! a) c = tl p'" 
      using Suc.hyps(1) Suc.hyps(2) \<open>p' = butlast p\<close> assms(2) by auto
    have "x' = a" 
      using Suc.prems(1) \<open>p = p' @ [x']\<close> last_path by auto
    then show ?thesis 
      using path_to_c.psimps path_to_c_domain Suc False 
      by (metis \<open>p = p' @ [x']\<close> \<open>path_to_c l (l ! a) c = tl p'\<close> append_self_conv2 list.inject path.cases tl_append_if)
  qed
qed

fun elements_on_path :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
"elements_on_path pf a b = (let c = lowest_common_ancestor pf a b in 
      (path_to_c pf a c) @ (path_to_c pf b c)
)"

abbreviation timestamps_decrease_invar
  where 
"timestamps_decrease_invar ti pf pfl \<equiv> 
(\<forall> a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b k x
. k < length pf \<longrightarrow> pfl ! k = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b))
\<longrightarrow> x \<in> set (elements_on_path pf a\<^sub>1 b\<^sub>1) \<or> x \<in> set (elements_on_path pf a\<^sub>2 b\<^sub>2)
\<longrightarrow> ti ! x < ti ! k)"

definition timestamps_invar
  where
"timestamps_invar cc_t \<equiv> 
timestamps_decrease_invar (timestamps cc_t) (proof_forest cc_t) (pf_labels cc_t)"

definition time_invar
  where
"time_invar cc_t \<equiv> (length (timestamps cc_t) = length (cc_list cc_t)) \<and> (\<forall> k < length (timestamps cc_t). 
(timestamps cc_t) ! k < (time cc_t))"

abbreviation cc_invar_t
  where
"cc_invar_t cc_t \<equiv> cc_invar (congruence_closure.truncate cc_t) \<and> timestamps_invar cc_t
\<and> time_invar cc_t"

section \<open>Induction rules\<close>

thm propagate_t.pinduct
lemma propagate_t_induct[consumes 1]:
  assumes "propagate_t_dom a0"
"\<And>l u t pf pfl ip k ti  .
propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = [], proof_forest = pf,
 pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr> \<Longrightarrow>  
P \<lparr>cc_list = l, use_list = u, lookup = t, pending = [], proof_forest = pf,
 pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>"
"(\<And>l u t pe pf pfl ip k ti a b eq.
propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf,
 pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr> \<Longrightarrow>  
a = left eq \<Longrightarrow> b = right eq \<Longrightarrow>
rep_of l a = rep_of l b \<Longrightarrow>
P \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf,
 pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr> \<Longrightarrow>
P (\<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr>))"
"(\<And>l u t pe pf pfl ip k ti a b eq. 
propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr> \<Longrightarrow>  
a = left eq \<Longrightarrow> b = right eq \<Longrightarrow>
rep_of l a \<noteq> rep_of l b \<Longrightarrow>
P (propagate_step_t l u t pe pf pfl ip a b eq k ti)
\<Longrightarrow> P \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr>)"
shows "P a0"
  using assms proof(induction a0 rule: propagate_t.pinduct)
  case (1 cc_t)
  then show ?case proof(cases "pending cc_t")
    case Nil
    then show ?thesis 
      using 1 
      by (metis (full_types) congruence_closure_t.surjective old.unit.exhaust)
  next
    case (Cons eq list)
    obtain l u t pe pf pfl ip k ti
        where cc_t: "cc_t = \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr>" 
      using congruence_closure_t.cases by blast
    then show ?thesis
    proof(cases "rep_of (cc_list cc_t) (left eq) = rep_of (cc_list cc_t) (right eq)")
      case True
      have "P \<lparr>cc_list = l, use_list = u, lookup = t, pending = list, proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr>" 
        using 1(2) "1.prems" True Cons unfolding cc_t congruence_closure.select_convs congruence_closure_t.select_convs 
        by blast
      then show ?thesis using 1(1,5) cc_t True Cons by force
    next
      case False
      have "P (propagate_step_t l u t list pf pfl ip (left eq) (right eq) eq k ti)" 
        using 1(3) "1.prems" False Cons unfolding cc_t congruence_closure.select_convs congruence_closure_t.select_convs 
        by blast
      then show ?thesis using 1(1,6) cc_t False Cons by simp
    qed
  qed
qed

thm merge_t.induct
lemma merge_t_induct:
  assumes "(\<And>l u t pe pf pfl ip k ti a b. 
P \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr> (a \<approx> b))"
"(\<And>l u t pe pf pfl ip k ti a\<^sub>1 a\<^sub>2 a. P \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr> (F a\<^sub>1 a\<^sub>2 \<approx> a))"
shows "P a0 a1"
  using assms merge_t.induct congruence_closure_t.cases by metis


section \<open>Proof that all timestamps are smaller than \<open>time cc_t\<close>\<close>

lemma add_timestamp_new_labels:
  assumes "ufa_invar pf" "a < length pf" "b < length pf" "length l = length pf" "length ti = length l"
    "rep_of pf a \<noteq> rep_of pf b" "x<length (add_timestamp pf ti a b k)"
  shows "(\<exists> x'. add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti) \<or>
add_timestamp pf ti a b k ! x = k" 
proof-
  have dom: "add_timestamp_dom (pf, ti, a, b, k)"
    using add_timestamp_domain assms by blast
  show "(\<exists>x'. add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti) \<or> add_timestamp pf ti a b k ! x = k"
    using dom assms  proof(induction)
    case (1 pf ti a b k)
    then show ?case 
    proof(cases "pf ! a = a")
      case True
      then have rec: "add_timestamp pf ti a b k = ti[a := k]"
        using add_timestamp.psimps 1 by simp
      then show ?thesis 
        proof(cases "x = a")
          case True
          then show ?thesis 
            using \<open>x < length (add_timestamp pf ti a b k)\<close> local.rec 1(9) by fastforce
        next
          case False
          have *: "add_timestamp pf ti a b k ! x = ti ! x \<and> x < length ti" 
            using False local.rec "1.prems"(7) by auto
          then show ?thesis by blast
        qed
    next
      case False
      have 3: "length l = length (pf[a := b])" "pf ! a < length (pf[a := b])" 
        using "1.prems" ufa_invarD(2) by force+
      have 4: "ufa_invar (pf[a := b])" using ufa_invar_fun_upd' 
        by (simp add: "1.prems")
      have 5: "rep_of (pf[a := b]) (pf ! a) \<noteq> rep_of (pf[a := b]) a"  
        using "1.prems" False add_label_case_2_rep_of_neq by metis
      have "length (add_timestamp pf ti a b k) = length ti"
        using 1(1) apply induction 
        using add_timestamp.psimps by force
      have "x < length (add_timestamp (pf[a := b]) (ti[a := k]) (pf ! a) a (ti ! a))"
        by (metis "1.hyps" "1.prems"(5) "1.prems"(7) False \<open>length (add_timestamp pf ti a b k) = length ti\<close> add_timestamp.psimps assms(4))
      then have IH: "(\<exists>x'. add_timestamp (pf[a := b]) (ti[a := k]) (pf ! a) a (ti ! a) ! x = ti[a := k] ! x' \<and> x' < length (ti[a := k])) \<or>
    add_timestamp (pf[a := b]) (ti[a := k]) (pf ! a) a (ti ! a) ! x = ti ! a" 
        using 1(2)[OF False 4 3(2) _ 3(1) _ 5] "1.prems" 
        by simp
      moreover have "add_timestamp pf ti a b k = add_timestamp (pf[a := b]) (ti[a := k]) (pf ! a) a (ti ! a)"
        using 1(1) add_timestamp.psimps False by auto
      ultimately show ?thesis 
        by (metis "1.prems"(2,4,5) length_list_update nth_list_update_eq nth_list_update_neq)
    qed
  qed
qed

lemma time_invar_step:
  assumes "time_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>" 
"ufa_invar pf" "a < length pf" "b < length pf" "length l = length pf"
"rep_of pf a \<noteq> rep_of pf b"
shows "time_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)"
  unfolding time_invar_def congruence_closure_t.select_convs congruence_closure.select_convs
congruence_closure.extend_def 
proof
  have cc_list: "cc_list (propagate_step l u t pe pf pfl ip a b eq) = ufa_union l a b" 
    using cc_list_unchanged_step by fast
  have dom: "add_timestamp_dom (pf, ti, a, b, k)"
    using add_timestamp_domain assms(2,3,4,6) by blast
  then have "length (add_timestamp pf ti a b k) = length ti"
    apply induction 
    using add_timestamp.psimps by force
  then show "length (add_timestamp pf ti a b k) = nr_vars (propagate_step l u t pe pf pfl ip a b eq)"
    using assms cc_list unfolding time_invar_def by auto
next
  show "\<forall>ka<length (add_timestamp pf ti a b k). add_timestamp pf ti a b k ! ka < k + 1"
  proof(standard, standard)
    fix x assume "x < length (add_timestamp pf ti a b k)"
    then have "(\<exists> x'. add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti) \<or>
add_timestamp pf ti a b k ! x = k" using add_timestamp_new_labels assms 
      unfolding congruence_closure.select_convs congruence_closure_t.select_convs time_invar_def 
      by blast
    then show "add_timestamp pf ti a b k ! x < k + 1"
    proof
      assume "\<exists>x'. add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti"
      then obtain x' where "add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti"
        by blast
      then show "add_timestamp pf ti a b k ! x < k + 1"
        using assms unfolding congruence_closure.select_convs congruence_closure_t.select_convs time_invar_def 
        by auto
    next
      assume "add_timestamp pf ti a b k ! x = k"
      then show "add_timestamp pf ti a b k ! x < k + 1"
        by simp
    qed
  qed
qed

lemma time_invar_propagate_t:
  assumes "propagate_t_dom cc_t" "time_invar cc_t" 
    "proof_forest_invar (congruence_closure.truncate cc_t)" 
    "same_length_invar (congruence_closure.truncate cc_t) (length (cc_list cc_t))"
    "pending_invar (congruence_closure.truncate cc_t)"
    "lookup_invar (congruence_closure.truncate cc_t)"
    "use_list_invar (congruence_closure.truncate cc_t)"
    "ufa_invar (cc_list cc_t)"
    "same_eq_classes_invar (congruence_closure.truncate cc_t)"
  shows "time_invar (propagate_t cc_t)"
  using assms proof(induction rule: propagate_t_induct)
  case (1 l u t pf pfl ip k ti)
  then show ?case 
    by simp
next
  case (2 l u t pe pf pfl ip k ti a b eq)
  note IH = 2[unfolded congruence_closure.truncate_def same_eq_classes_invar_def congruence_closure.select_convs 
time_invar_def congruence_closure_t.select_convs pending_invar_def lookup_invar_def use_list_invar_def
same_length_invar_def proof_forest_invar_def]
  have "\<forall>i<length pe. valid_vars_pending (pe ! i) l" 
    using IH(9) by auto
  then show ?case 
    unfolding congruence_closure.truncate_def same_eq_classes_invar_def congruence_closure.select_convs 
time_invar_def congruence_closure_t.select_convs pending_invar_def lookup_invar_def use_list_invar_def
    using IH(5)[OF IH(6-8) _ IH(10-13)] IH(1,2,3,4) propagate_t_simps2 by presburger
next
  case (3 l u t pe pf pfl ip k ti a b eq)
  note IH = 3[unfolded congruence_closure.truncate_def  congruence_closure.select_convs
 congruence_closure_t.select_convs   ]
  from 3(9,8,3,2) have a_b: "a < length pf" "b < length pf" 
    unfolding pending_invar_def congruence_closure.select_convs congruence_closure.truncate_def 
same_length_invar_def
    using pending_left_right_valid' by fastforce+
  with 3(4,13) have rep: "rep_of pf a \<noteq> rep_of pf b" 
    unfolding congruence_closure.truncate_def same_eq_classes_invar_def congruence_closure.select_convs 
    by blast
  have  **: "\<lparr>cc_list = cc_list (propagate_step l u t pe pf pfl ip a b eq),
        use_list = use_list (propagate_step l u t pe pf pfl ip a b eq),
        lookup = lookup (propagate_step l u t pe pf pfl ip a b eq),
        pending = pending (propagate_step l u t pe pf pfl ip a b eq),
        proof_forest = proof_forest (propagate_step l u t pe pf pfl ip a b eq),
        pf_labels = pf_labels (propagate_step l u t pe pf pfl ip a b eq),
        input = input (propagate_step l u t pe pf pfl ip a b eq)\<rparr> =
(propagate_step l u t pe pf pfl ip a b eq)" 
    by simp
  have 
   *: "(proof_forest_invar (congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti)))"
    "same_length_invar (congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti))
(length (cc_list (propagate_step_t l u t pe pf pfl ip a b eq k ti)))"
    "pending_invar (congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti)) "
    "lookup_invar (congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti)) "
    "use_list_invar (congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti)) "
    "ufa_invar (cc_list (propagate_step_t l u t pe pf pfl ip a b eq k ti)) "
    "same_eq_classes_invar (congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti))"
    using  add_edge_ufa_invar_invar a_b rep 3(7) proof_forest_unchanged_step
    unfolding 
 congruence_closure.select_convs congruence_closure.extend_def congruence_closure.truncate_def
congruence_closure.select_convs congruence_closure_t.select_convs ** proof_forest_invar_def apply auto[1]
 using cc_list_unchanged_step proof_forest_unchanged_step same_length_invar_step 
  using IH(13,2-4,7-9) pending_left_right_valid apply force
  using pending_invar_step[OF IH(9,10,11,12)] a_b IH(8) 
  unfolding same_length_invar_def  congruence_closure.select_convs apply auto[1]
  using lookup_invar_step[OF IH(12)] a_b IH(8,10, 11) 
  unfolding same_length_invar_def  congruence_closure.select_convs apply simp
  using use_list_invar_step[OF IH(12)] a_b IH(8,10, 11) 
  unfolding same_length_invar_def  congruence_closure.select_convs apply simp
  using cc_list_unchanged_step IH(8)
  unfolding same_length_invar_def  congruence_closure.select_convs 
  using IH(12) a_b(1) a_b(2) ufa_union_invar apply presburger
  using same_eq_classes_invar_step IH(8,7) a_b
  unfolding same_length_invar_def proof_forest_invar_def congruence_closure.select_convs  
  using IH(12) IH(13) rep by auto 
  have time_invar: "time_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)" 
    using time_invar_step[OF 3(6)] IH unfolding congruence_closure.select_convs 
    using \<open>a < length pf\<close> \<open>b < length pf\<close> \<open>rep_of pf a \<noteq> rep_of pf b\<close> 
    unfolding same_length_invar_def proof_forest_invar_def congruence_closure.select_convs  
    by presburger
  have "proof_forest (propagate_step_t l u t pe pf pfl ip a b eq k ti) = add_edge pf a b" 
    unfolding congruence_closure.extend_def 
    by (simp add: proof_forest_unchanged_step)
  have "cc_list (propagate_step_t l u t pe pf pfl ip a b eq k ti) = ufa_union l a b"
    unfolding congruence_closure.extend_def 
    by (simp add: cc_list_unchanged_step)
  then show ?case 
    using 3(5)[OF time_invar *] 3(1-4) by force 
qed


lemma time_invar_merge_t:
  assumes "cc_invar_t cc_t" "valid_vars eq (length (cc_list cc_t))"
  shows "time_invar (merge_t cc_t eq)"
using assms proof(induction cc_t eq rule: merge_t_induct)
  case (1 l u t pe pf pfl ip k ti a b)
  then have *: "time_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
    by blast
  have dom: "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>" 
    using propagate_propagate_t_domain propagate_domain 1 congruence_closure.select_convs(1-7)
    unfolding congruence_closure.extend_def congruence_closure.truncate_def 
    by (metis cc_invar_merge1 valid_vars_imp_nr_vars_gt_0)
  have cc_invar: "cc_invar (congruence_closure.truncate \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>)" 
    using propagate_propagate_t_domain propagate_domain 1 congruence_closure.select_convs(1-7)
    unfolding congruence_closure.extend_def congruence_closure.truncate_def 
    by (metis cc_invar_merge1)
  then have ufa_invar: "ufa_invar (cc_list
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b) # pe, proof_forest = pf, pf_labels = pfl,
          input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>)"
    unfolding cc_list_invar_def congruence_closure.truncate_def congruence_closure_t.select_convs 
    by simp
  then have "merge_t
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip,
          time = k, timestamps = ti\<rparr>
       (a \<approx> b) = propagate_t 
    \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>" 
    by auto
  then show ?case using time_invar_propagate_t[OF dom *] cc_invar
ufa_invar unfolding congruence_closure.select_convs congruence_closure_t.select_convs congruence_closure.truncate_def 
    by metis
next
  case (2 l u t pe pf pfl ip k ti a\<^sub>1 a\<^sub>2 a)
  then show ?case proof(cases "(lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a))")
    case True
    from 2 have *: "time_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
    by blast
    have dom: "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>" 
      using propagate_propagate_t_domain propagate_domain 2 cc_invar_merge2 congruence_closure.select_convs(1-7)
    unfolding congruence_closure.extend_def congruence_closure.truncate_def  
    by (metis True propagate_domain')
have cc_invar: "cc_invar (congruence_closure.truncate \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>)" 
    using propagate_propagate_t_domain propagate_domain 2 cc_invar_merge2 True
    unfolding congruence_closure.extend_def congruence_closure.truncate_def congruence_closure.select_convs(1-7) 
    by presburger
  then have ufa_invar: "ufa_invar (cc_list
       \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>)"
    unfolding cc_list_invar_def congruence_closure.truncate_def congruence_closure_t.select_convs 
    by simp
then have "merge_t
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip,
          time = k, timestamps = ti\<rparr>
       (F a\<^sub>1 a\<^sub>2 \<approx> a) = propagate_t \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>" using True
  by auto
  then show ?thesis using time_invar_propagate_t * True cc_invar ufa_invar dom
 unfolding congruence_closure.select_convs congruence_closure_t.select_convs congruence_closure.truncate_def 
    by simp
  next
    case False
    from 2 have *: "time_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, 
          time = k, timestamps = ti\<rparr>"
      unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
      by blast
    then show ?thesis 
      using False by auto
  qed
qed

lemma timestamps_invar_step:
  assumes "timestamps_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>" 
"a = left eq" "b = right eq" "rep_of l a \<noteq> rep_of l b"
shows "timestamps_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)"
  unfolding timestamps_invar_def congruence_closure_t.select_convs congruence_closure.select_convs
congruence_closure.extend_def 
proof(standard)+
  fix a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 ba ka x
  assume "ka < length (proof_forest (propagate_step l u t pe pf pfl ip a b eq))"
       "pf_labels (propagate_step l u t pe pf pfl ip a b eq) ! ka = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> ba))"
       "x \<in> set (elements_on_path (proof_forest (propagate_step l u t pe pf pfl ip a b eq)) a\<^sub>1 b\<^sub>1) \<or>
        x \<in> set (elements_on_path (proof_forest (propagate_step l u t pe pf pfl ip a b eq)) a\<^sub>2 b\<^sub>2)"
  have "proof_forest (propagate_step l u t pe pf pfl ip a b eq) = add_edge pf a b" sorry
  show "add_timestamp pf ti a b k ! x < add_timestamp pf ti a b k ! ka"
    sorry
qed

lemma timestamps_invar_propagate_t:
  assumes "propagate_t_dom cc_t" "timestamps_invar cc_t" 
  shows "timestamps_invar (propagate_t cc_t)"
  using assms proof(induction rule: propagate_t_induct)
  case (1 l u t pf pfl ip k ti)
  then show ?case 
    by simp
next
  case (2 l u t pe pf pfl ip k ti a b eq)
  then show ?case 
    by (simp add: timestamps_invar_def)
next
  case (3 l u t pe pf pfl ip k ti a b eq)
  then have "timestamps_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)" 
    using timestamps_invar_step by presburger
  then show ?case 
    using 3 by fastforce
qed


lemma timestamps_invar_merge_t:
  assumes "cc_invar_t cc_t" "valid_vars eq (length (cc_list cc_t))"
  shows "timestamps_invar (merge_t cc_t eq)"
using assms proof(induction cc_t eq rule: merge_t_induct)
  case (1 l u t pe pf pfl ip k ti a b)
  then have *: "timestamps_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs timestamps_invar_def 
    by blast
  have "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>" 
    using propagate_propagate_t_domain propagate_domain 1 
    unfolding congruence_closure.extend_def congruence_closure.truncate_def 
    by (metis cc_invar_merge1 congruence_closure.select_convs(1) congruence_closure.select_convs(2) congruence_closure.select_convs(3) congruence_closure.select_convs(4) congruence_closure.select_convs(5) congruence_closure.select_convs(6) congruence_closure.select_convs(7) valid_vars_imp_nr_vars_gt_0)
  then show ?case using timestamps_invar_propagate_t * 
    by auto
next
  case (2 l u t pe pf pfl ip k ti a\<^sub>1 a\<^sub>2 a)
  then show ?case proof(cases "(lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a))")
    case True
    from 2 have *: "timestamps_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs timestamps_invar_def 
    by blast
    have "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>" 
      using propagate_propagate_t_domain propagate_domain 2 cc_invar_merge2 congruence_closure.select_convs(1-7)
    unfolding congruence_closure.extend_def congruence_closure.truncate_def  
    by (metis True propagate_domain')
  then show ?thesis using timestamps_invar_propagate_t * True
    by simp
  next
    case False
    from 2 have *: "timestamps_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, 
          time = k, timestamps = ti\<rparr>"
      unfolding congruence_closure_t.select_convs congruence_closure.select_convs timestamps_invar_def 
      by blast
    then show ?thesis 
      using False by auto
  qed
qed

section \<open>Proofs that the multiset of the recursive calls are less than the multiset of xs\<close>

fun timestamp_mset :: "(nat * nat) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat multiset"
  where
"timestamp_mset [] pf ti = {#}"
| "timestamp_mset ((a, b) # xs) pf ti = (
mset (map (\<lambda> x. ti ! x) (elements_on_path pf a b))
 + timestamp_mset xs pf ti)"

lemma recursive_calls_mset_less:
  assumes "cc_invar_t cc_t"
"explain_along_path2 (congruence_closure.truncate cc_t) a c = (output, pend)" 
"path (proof_forest cc_t) c p a"
shows "multp\<^sub>H\<^sub>O (<) (timestamp_mset (pend @ xs) (proof_forest cc_t) (timestamps cc_t)) 
(timestamp_mset xs (proof_forest cc_t) (timestamps cc_t))"
proof-
  show ?thesis sorry
qed

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
