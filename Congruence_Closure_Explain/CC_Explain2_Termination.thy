theory CC_Explain2_Termination
  imports CC_Explain2_Definition
begin 


section \<open>Termination of \<open>cc_explain2\<close>\<close>

subsection \<open>Invariant definition for \<open>timestamps\<close>\<close>
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
(timestamps cc_t) ! k < (time cc_t) \<and> (timestamps cc_t) ! k > 0) \<and> (time cc_t) > 0"

abbreviation cc_invar_t
  where
    "cc_invar_t cc_t \<equiv> cc_invar (congruence_closure.truncate cc_t) \<and> timestamps_invar cc_t
\<and> time_invar cc_t"

subsection \<open>Proof of invariants\<close>

text \<open>Proof that all timestamps are smaller than \<open>time cc_t\<close>\<close>

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
  show "(\<forall>ka<length (add_timestamp pf ti a b k). add_timestamp pf ti a b k ! ka < k + 1 \<and> 0 < add_timestamp pf ti a b k ! ka) \<and> 0 < k + 1"
  proof(standard, standard, standard)
    fix x assume "x < length (add_timestamp pf ti a b k)"
    then have "(\<exists> x'. add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti) \<or>
add_timestamp pf ti a b k ! x = k" using add_timestamp_new_labels assms 
      unfolding congruence_closure.select_convs congruence_closure_t.select_convs time_invar_def 
      by blast
    then show "add_timestamp pf ti a b k ! x < k + 1 \<and> 0 < add_timestamp pf ti a b k ! x"
    proof
      assume "\<exists>x'. add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti"
      then obtain x' where "add_timestamp pf ti a b k ! x = ti ! x' \<and> x' < length ti"
        by blast
      then show "add_timestamp pf ti a b k ! x < k + 1 \<and> 0 < add_timestamp pf ti a b k ! x"
        using assms unfolding congruence_closure.select_convs congruence_closure_t.select_convs time_invar_def 
        by auto
    next
      assume "add_timestamp pf ti a b k ! x = k"
      then show "add_timestamp pf ti a b k ! x < k + 1 \<and> 0 < add_timestamp pf ti a b k ! x"
        using assms unfolding time_invar_def by auto
    qed
  qed simp
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

lemma add_timestamp_list_unchanged: 
  assumes "ufa_invar l"
    "path l (rep_of l li) p\<^sub>1 li" "x < length l"
    "i \<notin> set p\<^sub>1" "rep_of l li \<noteq> rep_of l x" "length l = length ti"
  shows "ti ! i = add_timestamp l ti li x k ! i"
proof-
  from assms have dom: "add_timestamp_dom (l, ti, li, x, k)" 
    using add_timestamp_domain path_nodes_lt_length_l by blast
  from dom assms show ?thesis 
  proof(induction arbitrary: p\<^sub>1 rule: add_timestamp.pinduct)
    case (1 pf ti e e' k)
    then have invar: "ufa_invar (add_edge pf e e')" 
      using add_edge_ufa_invar_invar path_nodes_lt_length_l by blast
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then have add_timestamp: "add_timestamp pf ti e e' k = ti[e := k]" 
        by (simp add: "1.hyps" add_timestamp.psimps)
      from 1 have "i \<noteq> e" 
        by (metis True list.set_intros(1) path_no_cycle path_nodes_lt_length_l rep_of_refl)
      then show ?thesis 
        by (simp add: add_timestamp "1.prems")
    next
      case False
      then have add_edge: 
        "add_timestamp pf ti e e' k = add_timestamp (pf[e := e']) (ti[e := k]) (pf ! e) e (ti ! e)" 
        by (simp add: "1.hyps" add_timestamp.psimps)
      from ufa_invar_fun_upd' 1 have invar: "ufa_invar (pf[e := e'])" 
        by blast
      from 1 have "last p\<^sub>1 = e" 
        using path_last by blast
      with 1 have "i \<noteq> e" 
        by (metis Misc.last_in_set path_not_empty)
      from 1 have path_to_parent: "path pf (rep_of pf (pf ! e)) (butlast p\<^sub>1) (pf ! e)"
        by (metis False path_butlast path_nodes_lt_length_l rep_of_min rep_of_step)
      with 1 have "path (pf[e := e']) (rep_of (pf[e := e']) (pf ! e)) (butlast p\<^sub>1) (pf ! e)"
        using path_fun_upd path_remove_right rep_of_fun_upd in_set_tlD by metis
      have "rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)" 
        using "1.prems" path_to_parent path_remove_right rep_of_fun_upd by auto
      from invar path_to_root_correct 
      have "path (pf[e := e']) (rep_of (pf[e := e']) e) (path_to_root (pf[e := e']) e) e" 
        using "1.prems" path_nodes_lt_length_l 
        by (metis length_list_update)
      then have "path (pf[e := e']) (rep_of (pf[e := e']) e') (butlast (path_to_root (pf[e := e']) e)) e'" 
        using "1.prems" path_nodes_lt_length_l 
        by (metis invar nth_list_update_eq path_butlast rep_of_idx rep_of_root)
      then have "e \<notin> set (butlast (path_to_root (pf[e := e']) e))" 
        using \<open>path (pf[e := e']) (rep_of (pf[e := e']) e) (path_to_root (pf[e := e']) e) e\<close> invar path_remove_right by presburger
      have "rep_of (pf[e := e']) e' = rep_of pf e'" 
        by (metis \<open>e \<notin> set (butlast (path_to_root (pf[e := e']) e))\<close> \<open>path (pf[e := e']) (rep_of (pf[e := e']) e') (butlast (path_to_root (pf[e := e']) e)) e'\<close> invar list_update_id list_update_overwrite rep_of_fun_upd)
      have "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        by (metis "1.prems"(1) "1.prems"(2) "1.prems"(5) \<open>rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)\<close> \<open>rep_of (pf[e := e']) e' = rep_of pf e'\<close> invar length_list_update nth_list_update_eq path_nodes_lt_length_l rep_of_idx)
      with 1 invar have "ti[e := k] ! i = add_timestamp (pf[e := e']) (ti[e := k]) (pf ! e) e (ti ! e) ! i" 
        by (metis \<open>path (pf[e := e']) (rep_of (pf[e := e']) (pf ! e)) (butlast p\<^sub>1) (pf ! e)\<close> in_set_butlastD length_list_update path_nodes_lt_length_l)
      then show ?thesis 
        using \<open>i \<noteq> e\<close> add_edge by force
    qed
  qed
qed

lemma nth_add_timestamp_e_eq_e': 
  assumes "ufa_invar pf" "e < length pf" "e' < length pf"
    "rep_of pf e \<noteq> rep_of pf e'" "length ti = length pf"
  shows "(add_timestamp pf ti e e' k) ! e = k"
proof-
  from assms have dom: "add_timestamp_dom (pf, ti, e, e', k)" 
    by (simp add: add_timestamp_domain)
  from dom assms show ?thesis 
  proof(induction rule: add_timestamp.pinduct)
    case (1 pf ti e e' k)
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then show ?thesis 
        by (simp add: "1.hyps" "1.prems" add_timestamp.psimps)
    next
      case False
      have invar: "ufa_invar (pf[e := e'])" 
        using "1.prems" ufa_invar_fun_upd' by auto
      have "path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)" 
        by (simp add: "1.prems"(1) "1.prems"(2) \<open>ufa_invar (pf[e := e'])\<close> path_to_root_correct ufa_invarD(2)) 
      with 1(3,4) invar path_remove_child[of "pf" "rep_of (pf[e := e']) (pf ! e)" "path_to_root (pf[e := e']) (pf ! e)" e]
      have "e \<notin> set (path_to_root pf (pf ! e))" 
        using False path_remove_child by blast
      have "path (pf[e := e']) (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)" 
        by (metis in_set_tlD \<open>e \<notin> set (path_to_root pf (pf ! e))\<close> \<open>path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)\<close> path_fun_upd)
      with "1.prems" add_edge_list_unchanged[of "pf[e := e']" "pf ! e" _ e e] 
      have *: "add_timestamp (pf[e := e']) (ti[e := k]) (pf ! e) e (ti ! e) ! e = k" using add_timestamp_list_unchanged 
        by (metis False \<open>e \<notin> set (path_to_root pf (pf ! e))\<close> \<open>path pf (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)\<close> add_label_case_2_rep_of_neq invar length_list_update nth_list_update_eq rep_of_fun_upd)
      with 1 have "add_timestamp (pf[e := e']) (ti[e := k]) (pf ! e) e (ti ! e) ! (pf ! e) = ti ! e"
        by (metis False \<open>path (pf[e := e']) (rep_of pf (pf ! e)) (path_to_root pf (pf ! e)) (pf ! e)\<close> add_label_case_2_rep_of_neq invar length_list_update path_nodes_lt_length_l)
      with 1 show ?thesis 
        using "*" False add_timestamp.psimps by presburger
    qed
  qed
qed

lemma add_timestamp_path_to_root_a: 
  assumes "ufa_invar pf" "a < length pf" "b < length pf" "rep_of pf a \<noteq> rep_of pf b"
    "length ti = length pf"
  shows "map ((!) ti) (tl (path_to_root pf a)) 
= map ((!) (add_timestamp pf ti a b k)) (butlast (path_to_root pf a))"
proof-
  from add_timestamp_domain assms have "add_timestamp_dom (pf, ti, a, b, k)" 
    by blast
  then show ?thesis 
    using assms proof(induction rule: add_timestamp.pinduct)
    case (1 pf ti a b k)
    then show ?case proof(cases "pf ! a = a")
      case True
      then have "path_to_root pf a = [a]" 
        using "1.prems"(1,2) path_to_root_correct path_to_root_has_length_1 by blast
      then show ?thesis 
        by simp
    next
      case False
      have prems: "ufa_invar (pf[a := b])"
        "pf ! a < length (pf[a := b])"
        "a < length (pf[a := b])"
        "rep_of (pf[a := b]) (pf ! a) \<noteq> rep_of (pf[a := b]) a"
        "length (ti[a := k]) = length (pf[a := b])"
            apply (simp add: "1.prems" ufa_invar_fun_upd')
        using "1.prems"(1) "1.prems"(2) ufa_invar_def apply auto[1]
          apply (simp add: "1.prems"(2))
         apply (metis "1.prems"(1) "1.prems"(2) "1.prems"(3) "1.prems"(4) False add_label_case_2_rep_of_neq)
        by (simp add: "1.prems"(5))
      then have IH: "map ((!) (ti[a := k])) (tl (path_to_root (pf[a := b]) (pf ! a))) =
    map ((!) (add_timestamp (pf[a := b]) (ti[a := k]) (pf ! a) a (ti ! a))) (butlast (path_to_root (pf[a := b]) (pf ! a)))"
        using False 1 by blast
      have "path_to_root pf (pf ! a) = butlast (path_to_root pf a)" using assms False
        by (metis "1.prems"(1,2)  \<open>pf ! a < length (pf[a := b])\<close> length_list_update path_butlast path_to_root_correct path_unique rep_of_idx rep_of_min)
      then have 2: "path_to_root (pf[a := b]) (pf ! a) = butlast (path_to_root pf a)" using assms False
        using path_to_root_fun_upd' 
        by (metis "1.prems"(1,2) \<open>pf ! a < length (pf[a := b])\<close> \<open>ufa_invar (pf[a := b])\<close> length_list_update path_remove_child path_to_root_correct path_to_root_fun_upd)
      have 3: "path_to_root pf a = butlast (path_to_root pf a) @ [a]" 
        by (metis "1.prems"(1,2) append_butlast_last_id path_last path_not_empty path_to_root_correct)
      have "map ((!) ti) (tl (path_to_root pf a)) = 
map ((!) ti) (tl (butlast (path_to_root pf a))) @ [ti ! a]" 
        by (metis "1.prems"(1) "3" \<open>path_to_root pf (pf ! a) = butlast (path_to_root pf a)\<close> \<open>pf ! a < length (pf[a := b])\<close> gr0I len_greater_imp_nonempty length_list_update list.simps(8) list.simps(9) map_append path_to_root_length tl_append2)
      have 3: "butlast (path_to_root pf a) = butlast (butlast (path_to_root pf a)) @ [pf ! a]" 
        by (metis "1.prems"(1) \<open>path_to_root pf (pf ! a) = butlast (path_to_root pf a)\<close> \<open>pf ! a < length (pf[a := b])\<close> append_butlast_last_id len_greater_imp_nonempty length_list_update path_last path_to_root_correct path_to_root_length)
      then have "map ((!) (add_timestamp pf ti a b k)) (butlast (path_to_root pf a))
= map ((!) (add_timestamp pf ti a b k)) (butlast (butlast (path_to_root pf a))) @ [add_timestamp pf ti a b k ! (pf ! a)]"
        by (metis list.simps(8) map_append map_consI(1))
      have "add_timestamp pf ti a b k = add_timestamp (pf[a := b]) (ti[a := k]) (pf ! a) a (ti ! a)" 
        using add_timestamp.psimps 1(1) False by auto
      moreover have "add_timestamp (pf[a := b]) (ti[a := k]) (pf ! a) a (ti ! a) ! (pf ! a) = ti ! a" 
        using nth_add_timestamp_e_eq_e' prems by blast
      ultimately have "add_timestamp pf ti a b k ! (pf ! a) = ti ! a" 
        by auto
      have "a \<notin> set (tl (path_to_root (pf[a := b]) (pf ! a)))" 
        by (metis "1.prems"(1) "2" False \<open>path_to_root pf (pf ! a) = butlast (path_to_root pf a)\<close> in_set_tlD length_list_update path_remove_child path_to_root_correct prems(2) prems(3))
      then have "map ((!) (ti[a := k])) (tl (path_to_root (pf[a := b]) (pf ! a)))
= map ((!) ti) (tl (path_to_root (pf[a := b]) (pf ! a)))" 
        by (metis (mono_tags, lifting) map_eq_conv nth_list_update_neq)
      then show ?thesis using IH 2 
        by (metis "1.hyps" False \<open>add_timestamp pf ti a b k ! (pf ! a) = ti ! a\<close> \<open>map ((!) (add_timestamp pf ti a b k)) (butlast (path_to_root pf a)) = map ((!) (add_timestamp pf ti a b k)) (butlast (butlast (path_to_root pf a))) @ [add_timestamp pf ti a b k ! (pf ! a)]\<close> \<open>map ((!) ti) (tl (path_to_root pf a)) = map ((!) ti) (tl (butlast (path_to_root pf a))) @ [ti ! a]\<close> add_timestamp.psimps)
    qed
  qed
qed

lemma add_edge_path:
  assumes "path pf c p1 x"
    "c \<notin> set (path_to_root pf a)"
    "ufa_invar pf"
    "a < length pf" "b < length pf"
    "rep_of pf a \<noteq> rep_of pf b"
  shows "path (add_edge pf a b) c p1 x" 
  using assms proof(induction)
  case (single n l)
  then show ?case 
    by (simp add: add_edge_preserves_length' path.single)
next
  case (step r l u p v)
  have "u \<notin> set (path_to_root l a)" 
  proof
    assume "u \<in> set (path_to_root l a)"
    then obtain i where i: "path_to_root l a ! i = u" "i < length (path_to_root l a)"
      by (meson in_set_conv_nth)
    have p_root: "path l (rep_of l a) (path_to_root l a) a" 
      by (simp add: path_to_root_correct step.prems(2) step.prems(3))
    then have *: "path_to_root l a ! 0 = rep_of l a" "l ! rep_of l a = rep_of l a"
       apply (metis nth_Cons_0 path.cases)
      using rep_of_min step.prems(2) step.prems(3) by blast
    then have "length (path_to_root l a) > 0" "i \<noteq> 0"
       apply (meson path_to_root_length step.prems(2) step.prems(3))
      using step(3) i * by metis
    then have "i - 1 < length (path_to_root l a) - 1" using i 
      by auto
    have "path_to_root l a ! (i - 1)  = r" using step path_previous_node[OF p_root] i  
      by (metis \<open>i \<noteq> 0\<close> not_gr_zero p_root path_parent)
    then show False 
      using i(2) less_imp_diff_less nth_mem step.prems(1) by blast
  qed
  then have "path (add_edge l a b) u p v"
    using step by blast
  moreover have "add_edge l a b ! u = r" 
    by (metis \<open>u \<notin> set (path_to_root l a)\<close> add_edge_list_unchanged path_to_root_correct step.hyps(2) step.prems(2) step.prems(3) step.prems(4) step.prems(5))
  ultimately show ?case 
    using step path.step add_edge_preserves_length' by auto
qed

lemma add_edge_path_to_c:
  assumes "path pf c p1 x"
    "c \<notin> set (path_to_root pf a)"
    "ufa_invar pf"
    "a < length pf" "b < length pf"
    "rep_of pf a \<noteq> rep_of pf b"
  shows "path_to_c pf x c = path_to_c (add_edge pf a b) x c" 
proof-
  have "path_to_c_dom (pf, x, c)"
    using path_to_c_domain assms by simp
  then show ?thesis
    using assms proof(induction arbitrary: p1 rule: path_to_c.pinduct)
    case (1 pf x c)
    then show ?case proof(cases "x = c")
      case True
      have "path_to_c pf x c = []" 
        using "1.hyps" True path_to_c.psimps by auto
      have "length pf = length (add_edge pf a b)" 
        using add_edge_preserves_length add_edge_domain 1 by force
      have "path (add_edge pf a b) x [x] c" 
        by (metis "1.prems"(1) True \<open>length pf = length (add_edge pf a b)\<close> path.simps path_nodes_lt_length_l)
      then show ?thesis 
        using True \<open>path_to_c pf x c = []\<close> path_to_c.psimps path_to_c_domain by auto
    next
      case False
      then have "path pf c (butlast p1) (pf ! x)" using "1.prems" 
        using path_butlast by blast
      then have 2: "path_to_c pf (pf ! x) c = path_to_c (add_edge pf a b) (pf ! x) c" 
        using 1 False by blast
      have 3: "path_to_c pf x c = path_to_c pf (pf ! x) c @ [x]" 
        by (metis (no_types, lifting) "1.prems"(1,3) False \<open>path pf c (butlast p1) (pf ! x)\<close> append_butlast_last_id hd_Nil_eq_last last_path list.sel(1) list_e_eq_lel(2) path_hd path_to_c_correct tl_append2)
      have "path (add_edge pf a b) c p1 x"
        using "1.prems" add_edge_path by auto
      then have 4: "path_to_c (add_edge pf a b) x c = path_to_c (add_edge pf a b) ((add_edge pf a b) ! x) c @ [x]"
        using path_to_c.psimps path_to_c_domain False by simp
      have "add_edge pf a b ! x = pf ! x" 
        by (metis False \<open>path (add_edge pf a b) c p1 x\<close> \<open>path pf c (butlast p1) (pf ! x)\<close> last_path path_butlast)
      then show ?thesis using 2 3 4 by simp
    qed
  qed
qed

lemma longest_common_prefix_empty:
  assumes "hd xs \<noteq> hd ys"
  shows "longest_common_prefix xs ys = []"
  using assms
  by (smt (verit) list.sel(1) longest_common_prefix.elims)

lemma longest_common_prefix_empty2:
  assumes "xs = [] \<or> ys = []"
  shows "longest_common_prefix xs ys = []"
  using assms 
  using longest_common_prefix.simps(2) longest_common_prefix.simps(3) by blast

lemma lowest_common_ancestor_if_last_equal_element:
  assumes "ufa_invar l" 
    "rep_of l x = rep_of l y" "x < length l" "y < length l"
    "path l (rep_of l x) (p1 @ [c] @ p2) x"
    "path l (rep_of l y) (p1 @ [c] @ p3) y"
    "hd p2 \<noteq> hd p3"
  shows "lowest_common_ancestor l x y = c"
proof-
  have "path_to_root l x = p1 @ [c] @ p2" "path_to_root l y = p1 @ [c] @ p3"
    using assms path_to_root_correct path_unique by blast+
  then have prefix: "prefix (p1 @ [c]) (path_to_root l x)"
    "prefix (p1 @ [c]) (path_to_root l y)" by auto
  then have "longest_common_prefix (path_to_root l x) (path_to_root l y) = p1 @ [c]"
    using longest_common_prefix_empty longest_common_prefix_concat assms 
    by (metis (no_types, lifting) \<open>path_to_root l x = p1 @ [c] @ p2\<close> \<open>path_to_root l y = p1 @ [c] @ p3\<close> append.right_neutral)
  then show ?thesis 
    by simp
qed

lemma lowest_common_ancestor_then_last_equal_element:
  assumes "ufa_invar l" 
    "rep_of l x = rep_of l y" "x < length l" "y < length l"
    "lowest_common_ancestor l x y = c"
    "path l (rep_of l x) (p1 @ [c] @ p2) x"
    "path l (rep_of l y) (p1 @ [c] @ p3) y"
    "p2 \<noteq> []" "p3 \<noteq> []"
  shows "hd p2 \<noteq> hd p3"
proof
  assume hd_eq: "hd p2 = hd p3"
  have p: "path_to_root l x = p1 @ [c] @ p2" "path_to_root l y = p1 @ [c] @ p3"
    using assms path_to_root_correct path_unique by blast+
  then have prefix: "prefix (p1 @ [c] @ [hd p2]) (path_to_root l x)"
    "prefix (p1 @ [c] @ [hd p2]) (path_to_root l y)" using hd_eq assms 
    by (metis append_one_prefix empty_append_eq_id hd_conv_nth hd_in_set length_pos_if_in_set list.size(3) prefixI same_prefix_prefix)+
  then have "prefix (p1 @ [c] @ [hd p2]) (longest_common_prefix (path_to_root l x) (path_to_root l y))"
    using longest_common_prefix_max_prefix by blast
  then obtain p4 where 
    "longest_common_prefix (path_to_root l x) (path_to_root l y) = p1 @ [c] @ [hd p2] @ p4" 
    by (metis Cons_eq_appendI append_assoc empty_append_eq_id prefixE)
  have "last ([hd p2] @ p4) = c" using assms 
    by (simp add: \<open>longest_common_prefix (path_to_root l x) (path_to_root l y) = p1 @ [c] @ [hd p2] @ p4\<close>)
  then obtain p5 where 
    "longest_common_prefix (path_to_root l x) (path_to_root l y) = p1 @ [c] @ p5 @ [c]"
    by (simp add: \<open>longest_common_prefix (path_to_root l x) (path_to_root l y) = p1 @ [c] @ [hd p2] @ p4\<close> snoc_eq_iff_butlast')
  then obtain p6 where "path_to_root l x = p1 @ [c] @ p5 @ [c] @ p6" 
    by (metis append_assoc longest_common_prefix_prefix1 prefixE)
  then have "path l c ([c] @ p5 @ [c]) c" 
    by (smt (verit) append_assoc append_is_Nil_conv assms(6) hd_append2 list.sel(1) p(1) path_divide2 prefix_code(2) same_prefix_nil)
  then show False 
    using p path_no_cycle assms path_nodes_lt_length_l by blast
qed

lemma add_edge_lowest_common_ancestor:
  assumes "ufa_invar l" "a < length l" "b < length l" "rep_of l a \<noteq> rep_of l b"
    "lowest_common_ancestor l x y \<notin> set (path_to_root l a)" 
    "rep_of l x = rep_of l y" "x < length l" "y < length l"
  shows "lowest_common_ancestor l x y = lowest_common_ancestor (add_edge l a b) x y"
proof-
  obtain p1 p2 where paths: "path l (lowest_common_ancestor l x y) p1 x"
    "path l (lowest_common_ancestor l x y) p2 y" using assms
    by (meson lowest_common_ancestor_correct)
  then have paths': "path (add_edge l a b) (lowest_common_ancestor l x y) p1 x"
    "path (add_edge l a b) (lowest_common_ancestor l x y) p2 y" using assms add_edge_path by auto
  then obtain p3 p4 where paths2: "path_to_root (add_edge l a b) x = p3 @ p1" 
    "path_to_root (add_edge l a b) y = p4 @ p2" using paths 
    by (smt (verit, ccfv_SIG) add_edge_ufa_invar_invar assms path_concat2 path_nodes_lt_length_l path_rep_eq path_to_root_correct path_unique)
  then obtain p5 p6 where paths3: "path_to_root l x = p5 @ p1" 
    "path_to_root l y = p6 @ p2" using paths 
    by (smt (verit, ccfv_SIG) add_edge_ufa_invar_invar assms path_concat2 path_nodes_lt_length_l path_rep_eq path_to_root_correct path_unique)
  have hd: "hd p1 = lowest_common_ancestor l x y" "hd p2 = lowest_common_ancestor l x y"
    using paths by (metis hd_path)+
  then have "path (add_edge l a b) (rep_of (add_edge l a b) x) (p3 @ [lowest_common_ancestor l x y])  (lowest_common_ancestor l x y)"
    "path (add_edge l a b) (rep_of (add_edge l a b) y) (p4 @ [lowest_common_ancestor l x y])  (lowest_common_ancestor l x y)"
    using paths2 paths'
    by (metis add_edge_ufa_invar_invar assms(1-4) list.discI path.cases path_divide2 path_nodes_lt_length_l path_to_root_correct)+
  then have eq: "p3 = p4" using assms
    by (metis add_edge_ufa_invar_invar append_same_eq path_unique rep_of_add_edge_invar)
  have invar: "ufa_invar (add_edge l a b)" "length (add_edge l a b) = length l" 
    "rep_of (add_edge l a b) x = rep_of (add_edge l a b) y" 
      apply (simp add: add_edge_ufa_invar_invar assms(1-4))
     apply (simp add: add_edge_preserves_length' assms(1-4))
    using rep_of_add_edge_aux assms by presburger
  have ptr_add_edge: "path_to_root (add_edge l a b) x = (p3 @ [lowest_common_ancestor l x y] @ tl p1)"
    "path_to_root (add_edge l a b) y = (p4 @ [lowest_common_ancestor l x y] @ tl p2)"
     apply (metis Cons_eq_appendI empty_append_eq_id hd(1) list.collapse path_not_empty paths(1) paths2(1))
    by (metis append_Cons append_Nil hd(2) list.exhaust_sel path_not_empty paths'(2) paths2(2))
  then have path_add_edge: 
    "path (add_edge l a b) (rep_of (add_edge l a b) x) (p3 @ [lowest_common_ancestor l x y] @ tl p1) x"
    "path (add_edge l a b) (rep_of (add_edge l a b) y) (p3 @ [lowest_common_ancestor l x y] @ tl p2) y"
    using paths2 path_to_root_correct[OF invar(1)] hd assms(1,7,8) invar eq by metis+
  have *: "path l (rep_of l x) (p5 @ [lowest_common_ancestor l x y] @ tl p1) x"
    "path l (rep_of l y) (p6 @ [lowest_common_ancestor l x y] @ tl p2) y"
     apply (metis Cons_eq_appendI append_Nil assms(1) assms(7) hd(1) hd_Cons_tl path_not_empty path_to_root_correct paths(1) paths3(1))
    by (metis \<open>path_to_root (add_edge l a b) y = p4 @ [lowest_common_ancestor l x y] @ tl p2\<close> assms(1) assms(8) path_to_root_correct paths2(2) paths3(2) same_append_eq)
  then have **: "p5 = p6" 
    by (smt (verit) \<open>path_to_root (add_edge l a b) x = p3 @ [lowest_common_ancestor l x y] @ tl p1\<close> \<open>path_to_root (add_edge l a b) y = p4 @ [lowest_common_ancestor l x y] @ tl p2\<close> append_same_eq assms(1) assms(6) hd(1) hd(2) not_Cons_self2 path_divide2 path_unique paths2(1) paths2(2) same_append_eq self_append_conv tl_Nil)  
  then show ?thesis 
  proof(cases "tl p1 = [] \<or> tl p2 = []")
    case False
    then have hd2: "hd (tl p1) \<noteq> hd (tl p2)"
      using lowest_common_ancestor_then_last_equal_element[OF assms(1,6,7,8) _ *(1)] * ** by blast 
    then show ?thesis using hd hd2 paths2 lowest_common_ancestor_if_last_equal_element assms 
      by (metis \<open>path (add_edge l a b) (rep_of (add_edge l a b) x) (p3 @ [lowest_common_ancestor l x y] @ tl p1) x\<close> \<open>path (add_edge l a b) (rep_of (add_edge l a b) y) (p3 @ [lowest_common_ancestor l x y] @ tl p2) y\<close> invar(1) invar(2) invar(3))
  next
    case True
    have "prefix (p3 @ [lowest_common_ancestor l x y]) (path_to_root (add_edge l a b) x)"
      "prefix (p3 @ [lowest_common_ancestor l x y]) (path_to_root (add_edge l a b) y)" 
      by (auto simp add: eq ptr_add_edge)
    have "longest_common_prefix (path_to_root (add_edge l a b) x) (path_to_root (add_edge l a b) y)
= p3 @ [lowest_common_ancestor l x y]"
      using longest_common_prefix_empty2 ptr_add_edge longest_common_prefix_concat 
      by (metis (no_types, opaque_lifting) True append.right_neutral eq)
    then show ?thesis
      by fastforce
  qed
qed

lemma add_edge_elements_on_path:
  assumes "c = lowest_common_ancestor pf x y"
    "c \<notin> set (path_to_root pf a)"
    "ufa_invar pf"
    "x < length pf" "y < length pf"
    "rep_of pf x = rep_of pf y"
    "a < length pf" "b < length pf"
    "rep_of pf a \<noteq> rep_of pf b"
  shows "elements_on_path pf x y = elements_on_path (add_edge pf a b) x y" 
proof-
  obtain p1 p2 where paths: "path pf c p1 x" "path pf c p2 y" 
    using assms lowest_common_ancestor_correct by presburger
  have "c = lowest_common_ancestor (add_edge pf a b) x y" using add_edge_lowest_common_ancestor 
    using assms by blast
  then have "elements_on_path (add_edge pf a b) x y = path_to_c (add_edge pf a b) x c @ path_to_c (add_edge pf a b) y c" 
    "elements_on_path pf x y = path_to_c pf x c @ path_to_c pf y c" 
    using elements_on_path.simps assms unfolding Let_def apply simp 
    using elements_on_path.simps assms unfolding Let_def by simp 
  then have "path_to_c pf x c = path_to_c (add_edge pf a b) x c"
    "path_to_c pf y c = path_to_c (add_edge pf a b) y c"
    using assms add_edge_path_to_c paths by blast+
  then show ?thesis using assms add_edge_path_to_c 
    by (metis \<open>c = lowest_common_ancestor (add_edge pf a b) x y\<close> elements_on_path.simps)
qed

lemma lowest_common_ancestor_notin_elements_on_path:
  assumes "ufa_invar pf"
    "x < length pf" "y < length pf"
    "rep_of pf x = rep_of pf y"
    "a \<in> set (elements_on_path pf x y)"
    "c = lowest_common_ancestor pf x y"
  shows "a \<noteq> c" 
proof- 
  obtain p1 p2 where "path pf c p1 x" "path pf c p2 y"
    using lowest_common_ancestor_correct assms by blast
  then have p: "path pf c (c # path_to_c pf x c) x" 
    "path pf c (c # path_to_c pf y c) y" 
    using lowest_common_ancestor_correct path_to_c_correct 
    by (metis assms(1) list.collapse path_hd path_not_empty)+
  then have "a \<in> set (path_to_c pf x c) \<or> a \<in> set (path_to_c pf y c)"
    using assms elements_on_path.simps unfolding Let_def by auto
  then show ?thesis 
    using p assms(1) path_remove_left by blast
qed

lemma elements_on_path_valid:
  assumes "ufa_invar pf"
    "x < length pf" "y < length pf"
    "rep_of pf x = rep_of pf y"
    "a \<in> set (elements_on_path pf x y)"
  shows "a < length pf"
proof-
  define c where "c = lowest_common_ancestor pf x y"
  then have "a \<in> set (path_to_c pf x c) \<or> a \<in> set (path_to_c pf y c)"
    using assms elements_on_path.simps unfolding Let_def by auto
  obtain p1 p2 where "path pf c p1 x" "path pf c p2 y"
    using lowest_common_ancestor_correct assms c_def by blast
  then have p: "path pf c (c # path_to_c pf x c) x" 
    "path pf c (c # path_to_c pf y c) y" 
    using lowest_common_ancestor_correct path_to_c_correct c_def
    by (metis assms(1) list.collapse path_hd path_not_empty)+
  then show ?thesis 
    by (metis \<open>a \<in> set (path_to_c pf x c) \<or> a \<in> set (path_to_c pf y c)\<close> in_set_conv_nth length_pos_if_in_set less_numeral_extra(3) list.size(3) list_tail_coinc nodes_path_lt_length_l path.cases)
qed

(* TODO : show that timestamps_invar holds after "add_timestamp pf ti a b k"*)
lemma timestamps_invar_step:
  assumes "cc_invar_t \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>"
    "a = left eq" "b = right eq" "rep_of l a \<noteq> rep_of l b"
  shows "timestamps_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)"
  unfolding timestamps_invar_def congruence_closure_t.select_convs congruence_closure.select_convs
    congruence_closure.extend_def 
proof(standard)+
  fix a\<^sub>1 a\<^sub>2 aa b\<^sub>1 b\<^sub>2 ba ka x
  assume assms2: "ka < length (proof_forest (propagate_step l u t pe pf pfl ip a b eq))"
    "pf_labels (propagate_step l u t pe pf pfl ip a b eq) ! ka = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> ba))"
    "x \<in> set (elements_on_path (proof_forest (propagate_step l u t pe pf pfl ip a b eq)) a\<^sub>1 b\<^sub>1) \<or>
        x \<in> set (elements_on_path (proof_forest (propagate_step l u t pe pf pfl ip a b eq)) a\<^sub>2 b\<^sub>2)"
  have "proof_forest (propagate_step l u t pe pf pfl ip a b eq) = add_edge pf a b" 
"cc_list (propagate_step l u t pe pf pfl ip a b eq) = ufa_union l a b" 
     apply (meson proof_forest_unchanged_step)
    by (simp add: cc_list_unchanged_step)
  then have valid: "ufa_invar pf" "rep_of pf a \<noteq> rep_of pf b" "length pf = length ti" 
     "a < length pf" "b < length pf"  "a < length l" "b < length l" "ufa_invar l"
"length pf = length l"
    using assms unfolding proof_forest_invar_def congruence_closure.truncate_def same_eq_classes_invar_def
pending_invar_def same_length_invar_def time_invar_def cc_list_invar_def
    using assms(1) pending_left_right_valid congruence_closure_t.select_convs pending_invar_def 
    by auto
  then have "length (proof_forest (propagate_step l u t pe pf pfl ip a b eq)) = length pf"
  by (simp add: \<open>proof_forest (propagate_step l u t pe pf pfl ip a b eq) = add_edge pf a b\<close> add_edge_preserves_length')
  then have "ka < length pf" 
    using assms2(1) by force
  then have "pf_labels_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using pf_labels_invar_step[OF valid(1,6,7) assms(2,3)] valid assms 
    unfolding same_length_invar_def congruence_closure.truncate_def 
    by fastforce
  then have valid_labels_invar_step: "valid_labels_invar (pf_labels (propagate_step l u t pe pf pfl ip a b eq)) 
(proof_forest (propagate_step l u t pe pf pfl ip a b eq))
(cc_list (propagate_step l u t pe pf pfl ip a b eq))"
    using assms same_eq_classes_invar_def pf_labels_invar_def same_length_invar_def 
    by simp
  then have valid2: "rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) b\<^sub>1"
"rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) b\<^sub>2"
    using assms same_eq_classes_invar_def pf_labels_invar_def same_length_invar_def 
    by (smt (verit) \<open>cc_list (propagate_step l u t pe pf pfl ip a b eq) = ufa_union l a b\<close> assms2(1) assms2(2) option.discI option.sel valid_vars_pending.simps(2))+
  have "valid_vars_pending (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> ba)) (ufa_union l a b)" 
    using valid_labels_invar_step assms2 
    by (metis \<open>cc_list (propagate_step l u t pe pf pfl ip a b eq) = ufa_union l a b\<close> option.distinct(1) option.sel)
  then have *: "a\<^sub>1 < length (ufa_union l a b)"
    "b\<^sub>1 < length (ufa_union l a b)"
    "a\<^sub>2 < length (ufa_union l a b)"
    "b\<^sub>2 < length (ufa_union l a b)"
"length (ufa_union l a b) = length (add_edge pf a b)"
    apply (meson valid_vars.simps(2) valid_vars_pending.simps(2))+
    by (simp add: add_edge_preserves_length' valid(1) valid(2) valid(6) valid(7) valid(9))
  have "same_eq_classes_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using same_eq_classes_invar_step same_length_invar_def valid assms(1) 
    unfolding same_length_invar_def congruence_closure.truncate_def 
    by simp
  then have "rep_of (add_edge pf a b) a\<^sub>1 = rep_of (add_edge pf a b) b\<^sub>1"
"rep_of (add_edge pf a b) a\<^sub>2 = rep_of (add_edge pf a b) b\<^sub>2"
    using * valid2 unfolding same_eq_classes_invar_def 
    by (metis \<open>cc_list (propagate_step l u t pe pf pfl ip a b eq) = ufa_union l a b\<close> \<open>proof_forest (propagate_step l u t pe pf pfl ip a b eq) = add_edge pf a b\<close>)+
  have "x < length (proof_forest (propagate_step l u t pe pf pfl ip a b eq))"
    using elements_on_path_valid assms2 valid *
    by (metis (no_types, lifting) \<open>proof_forest (propagate_step l u t pe pf pfl ip a b eq) = add_edge pf a b\<close> \<open>rep_of (add_edge pf a b) a\<^sub>1 = rep_of (add_edge pf a b) b\<^sub>1\<close> \<open>rep_of (add_edge pf a b) a\<^sub>2 = rep_of (add_edge pf a b) b\<^sub>2\<close> add_edge_ufa_invar_invar)
  then have valid3: "x < length pf" 
    using \<open>length (proof_forest (propagate_step l u t pe pf pfl ip a b eq)) = length pf\<close> by presburger
  define c\<^sub>1 where "c\<^sub>1 = lowest_common_ancestor pf a\<^sub>1 b\<^sub>1"
  define c\<^sub>2 where "c\<^sub>2 = lowest_common_ancestor pf a\<^sub>2 b\<^sub>2"
  show "add_timestamp pf ti a b k ! x < add_timestamp pf ti a b k ! ka"
  proof(cases "c\<^sub>1 \<in> set (path_to_root pf a)")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis 
    proof(cases "c\<^sub>2 \<in> set (path_to_root pf a)")
      case True
      then show ?thesis sorry
    next
      case False
      have "rep_of pf a\<^sub>1 = rep_of pf b\<^sub>1"
"rep_of pf a\<^sub>2 = rep_of pf b\<^sub>2"
        sorry
      then have "elements_on_path pf a\<^sub>2 b\<^sub>2 = elements_on_path (add_edge pf a b) a\<^sub>2 b\<^sub>2" 
using add_edge_elements_on_path[OF c\<^sub>2_def False valid(1)] * 
  by (metis length_list_update valid(2) valid(4) valid(5) valid(9))
      then show ?thesis sorry
    qed

  qed
qed

lemma timestamps_invar_propagate_t:
  assumes "propagate_t_dom cc_t" "cc_invar_t cc_t" 
  shows "timestamps_invar (propagate_t cc_t)"
  using assms proof(induction rule: propagate_t_induct)
  case (1 l u t pf pfl ip k ti)
  then show ?case 
    by simp
next
  case (2 l u t pe pf pfl ip k ti a b eq)
  then have "cc_invar (congruence_closure.truncate 
     \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip,
        time = k, timestamps = ti\<rparr>)"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
      congruence_closure.truncate_def by (metis cc_invar_step2 congruence_closure.select_convs(1))
  then have "cc_invar_t
     \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip,
        time = k, timestamps = ti\<rparr>" using 2 
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def  
      timestamps_invar_def by blast
  then show ?case using timestamps_invar_def time_invar_def 2 
    by auto
next
  case (3 l u t pe pf pfl ip k ti a b eq)
  then have "timestamps_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)" 
    using timestamps_invar_step by presburger
  from 3(2,3,6) have a_b: "a < length pf" "b < length pf" "length l = length pf" "ufa_invar pf"
    unfolding  congruence_closure.select_convs congruence_closure.truncate_def pending_invar_def same_length_invar_def
    using pending_left_right_valid'  proof_forest_invar_def by auto
  with 3 have rep: "rep_of pf a \<noteq> rep_of pf b" 
    unfolding congruence_closure.truncate_def same_eq_classes_invar_def congruence_closure.select_convs 
    by blast
  then have "time_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)" 
    using time_invar_step 3 a_b by blast
  have "congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti) = 
propagate_step l u t pe pf pfl ip a b eq"
    using propagate_propagate_t_equivalence propagate_step_propagate_step_t_equivalence by auto
  with 3 have "cc_invar (congruence_closure.truncate 
     (propagate_step_t l u t pe pf pfl ip a b eq k ti))"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
      congruence_closure.truncate_def using cc_invar_step 
    by (metis cc_list_loop cc_list_unchanged_loop)
  then show ?case 
    using 3 
    by (metis CC_Definition2.propagate_simps3 \<open>time_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)\<close> \<open>timestamps_invar (propagate_step_t l u t pe pf pfl ip a b eq k ti)\<close>)
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
  from 1 have **: "time_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
    by blast
  from 1 have ***: "cc_invar (congruence_closure.truncate \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>)"
    unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
      congruence_closure.truncate_def 
    using cc_invar_merge1 by auto       
  have "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>" 
    using propagate_propagate_t_domain propagate_domain 1 
    unfolding congruence_closure.extend_def congruence_closure.truncate_def 
    by (metis cc_invar_merge1 congruence_closure.select_convs(1) congruence_closure.select_convs(2) congruence_closure.select_convs(3) congruence_closure.select_convs(4) congruence_closure.select_convs(5) congruence_closure.select_convs(6) congruence_closure.select_convs(7) valid_vars_imp_nr_vars_gt_0)
  then show ?case using timestamps_invar_propagate_t * ** *** 
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
    from 2 have **: "time_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>"
      unfolding congruence_closure_t.select_convs congruence_closure.select_convs time_invar_def 
      by blast
    from 2 have ***: "cc_invar (congruence_closure.truncate \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>)"
      unfolding congruence_closure_t.select_convs congruence_closure.select_convs  
        congruence_closure.truncate_def 
      using cc_invar_merge2 True by auto
    have "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>" 
      using propagate_propagate_t_domain propagate_domain 2 cc_invar_merge2 congruence_closure.select_convs(1-7)
      unfolding congruence_closure.extend_def congruence_closure.truncate_def  
      by (metis True propagate_domain')
    then show ?thesis using timestamps_invar_propagate_t * True ** ***
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

subsection \<open>Proofs that the multiset of the recursive calls are less than the multiset of xs\<close>

fun timestamp_mset :: "(nat * nat) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat multiset"
  where
    "timestamp_mset [] pf ti = {#}"
  | "timestamp_mset ((a, b) # xs) pf ti = 
  (let eop = elements_on_path pf a b in 
    (case eop of 
      [] \<Rightarrow> {#0#} | 
      (e1 # eop') \<Rightarrow> mset (map ((!) ti) (e1 # eop')))
 + timestamp_mset xs pf ti)"

lemmas timestamp_mset_simps[simp] = timestamp_mset.simps(2)[unfolded Let_def]

lemma timestamp_mset_app:
  "timestamp_mset (xs @ ys) pf ti = timestamp_mset xs pf ti + timestamp_mset ys pf ti"
  apply(induction xs pf ti rule: timestamp_mset.induct)
  by auto

lemma path_to_c_empty:
  assumes "path pf c p a"
  shows "path_to_c pf a c = [] \<longleftrightarrow> a = c"
proof
  have dom: "path_to_c_dom (pf, a, c)" using assms path_to_c_domain 
    by auto
  then show "path_to_c pf a c = [] \<Longrightarrow> a = c"
    using assms apply (induction rule: path_to_c.pinduct)
    by (metis append_is_Nil_conv not_Cons_self2 path_to_c.psimps)
  show "a = c \<Longrightarrow> path_to_c pf a c = []" 
    using path_to_c.psimps dom by simp
qed

lemma lowest_common_ancestor_a_a:
  assumes "ufa_invar pf" "a < length pf"
  shows "lowest_common_ancestor pf a a = a"
proof-
  from path_to_root_domain have "path_to_root_dom (pf, a)" 
    using assms(1) assms(2) ufa_invarD(1) by auto
  then obtain p where "path_to_root pf a = p @ [a]" 
    using path_to_root.psimps by fastforce
  then show ?thesis 
    by (simp add: longest_common_prefix_concat)
qed

lemma elements_on_path_empty: 
  assumes "ufa_invar pf"
    "a < length pf" "b < length pf"
    "rep_of pf a = rep_of pf b"
  shows "elements_on_path pf a b = [] \<longleftrightarrow> a = b"
proof
  assume elements_empty: "elements_on_path pf a b = []"
  define c where "c = lowest_common_ancestor pf a b"
  then have "c < length pf" 
    by (metis assms lowest_common_ancestor_correct path_nodes_lt_length_l)
  from c_def have "path_to_c pf a c = []" "path_to_c pf b c = []"
    using elements_on_path.simps elements_empty unfolding Let_def by auto
  from lowest_common_ancestor_correct assms c_def 
  obtain p1 p2 where "path pf c p1 a" "path pf c p2 b"
    by blast
  then show "a = b" using path_to_c_empty 
    using \<open>path_to_c pf a c = []\<close> \<open>path_to_c pf b c = []\<close> by auto
next
  assume a_b: "a = b"
  define c where "c = lowest_common_ancestor pf a b"
  then have "c = a"
    using lowest_common_ancestor_a_a a_b assms(1,3) by auto
  from lowest_common_ancestor_correct assms c_def 
  obtain p1 p2 where p: "path pf c p1 a" "path pf c p2 b"
    by blast
  then have "c < length pf" 
    by (metis path_nodes_lt_length_l)
  from c_def have "path_to_c pf a c = []" "path_to_c pf b c = []"
    using path_to_c_empty a_b p \<open>c = a\<close> by auto
  then show "elements_on_path pf a b = []" 
    using elements_on_path.simps c_def by force
qed

lemma timestamp_mset_empty:
  assumes "ufa_invar pf" "\<forall> (a, b) \<in> set xs . a < length pf \<and> b < length pf"
    "\<forall> (a, b) \<in> set xs . rep_of pf a = rep_of pf b" "xs \<noteq> []"
  shows "timestamp_mset xs pf ti \<noteq> {#}"
  using assms proof(induction xs pf ti rule: timestamp_mset.induct)
  case (2 a b xs pf ti)
  then show ?case proof(cases "elements_on_path pf a b")
    case (Cons k list)
    then show ?thesis 
      using Cons elements_on_path_empty timestamp_mset.simps unfolding Case_def Let_def 
      by simp
  qed simp
qed simp

lemma mset_less_if_sum:
  assumes "ms2 = ms1 + a" "a \<noteq> {#}"
  shows "ms1 < ms2"
  using assms  
  by auto

lemma tl_list_mset_less:
  assumes "cc_invar_t cc_t"
    "a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
  shows "(timestamp_mset xs (proof_forest cc_t) (timestamps cc_t)) <
(timestamp_mset ((a, b) # xs) (proof_forest cc_t) (timestamps cc_t))"
proof-
  have *: "ufa_invar (proof_forest cc_t)" 
    "length (cc_list cc_t) = length (proof_forest cc_t)"
    "\<forall> (a,b) \<in> set [(a,b)]. rep_of (proof_forest cc_t) a = rep_of (proof_forest cc_t) b"
    "[(a, b)] \<noteq> []"
    using assms unfolding proof_forest_invar_def congruence_closure.truncate_def same_eq_classes_invar_def
    apply simp
    using assms unfolding proof_forest_invar_def congruence_closure.truncate_def same_eq_classes_invar_def
    by (auto simp add: same_length_invar_def)
  have "timestamp_mset ((a, b) # xs) (proof_forest cc_t) (timestamps cc_t)
= timestamp_mset [(a, b)] (proof_forest cc_t) (timestamps cc_t)
+ timestamp_mset xs (proof_forest cc_t) (timestamps cc_t)"
    using timestamp_mset_app 
    by (metis Cons_eq_appendI append_Nil)
  moreover have "timestamp_mset [(a, b)] (proof_forest cc_t) (timestamps cc_t) \<noteq> {#}"
    using * assms timestamp_mset_empty 
    by fastforce
  ultimately show ?thesis using mset_less_if_sum 
    by (metis ab_semigroup_add_class.add.commute)
qed

lemma removeAll_timestamp_mset_less:
  "(timestamp_mset (removeAll x xs) pf ti) < (timestamp_mset xs pf ti) 
\<or> (timestamp_mset (removeAll x xs) pf ti) = (timestamp_mset xs pf ti)" 
proof(induction xs pf ti rule: timestamp_mset.induct)
  case (2 a b xs pf ti)
  then show ?case proof(cases "elements_on_path pf a b")
    case Nil
    then have rec: "timestamp_mset ((a, b) # xs) pf ti = {#0#} + timestamp_mset xs pf ti" 
      using timestamp_mset.simps unfolding Let_def by simp
    then show ?thesis using 2 proof(cases "x = (a, b)")
      case True
      then have "removeAll x xs = removeAll x ((a, b) # xs)" 
        by fastforce
      then show ?thesis using 2 rec 
        by (metis le_multiset_plus_left_nonempty le_multiset_right_total multi_self_add_other_not_self pos_add_strict)
    next
      case False
      then have "removeAll x ((a, b) # xs) = (a, b) # removeAll x xs" 
        by simp
      then have "timestamp_mset (removeAll x ((a, b) # xs)) pf ti 
= {#0#} + timestamp_mset (removeAll x xs) pf ti" 
        using timestamp_mset.simps Nil unfolding Let_def by simp
      then show ?thesis using 2 rec 
        by (metis add_mono_thms_linordered_field(2))
    qed
  next
    case (Cons e1 eop')
    define added_mset where "added_mset = mset (map ((!) ti) (elements_on_path pf a b))"
    have rec: "timestamp_mset ((a, b) # xs) pf ti = added_mset + timestamp_mset xs pf ti" 
      using timestamp_mset.simps Cons unfolding Let_def added_mset_def by simp
    have "elements_on_path pf a b \<noteq> []" 
      using local.Cons by auto
    then have not_empty: "added_mset \<noteq> {#}" using added_mset_def by auto
    then show ?thesis using 2 proof(cases "x = (a, b)")
      case True
      then have "removeAll x xs = removeAll x ((a, b) # xs)" 
        by fastforce
      then show ?thesis using 2 rec not_empty 
        by (metis le_multiset_empty_left le_multiset_plus_left_nonempty pos_add_strict)
    next
      case False
      then have "removeAll x ((a, b) # xs) = (a, b) # removeAll x xs" 
        by simp
      then have "timestamp_mset (removeAll x ((a, b) # xs)) pf ti 
= added_mset + timestamp_mset (removeAll x xs) pf ti" 
        using timestamp_mset.simps Nil unfolding Let_def added_mset_def 
        using add_right_imp_eq added_mset_def local.rec by auto
      then show ?thesis using 2 rec 
        by (metis add_mono_thms_linordered_field(2))
    qed
  qed
qed auto

lemma append_timestamp_mset_less:
  assumes "(timestamp_mset xs pf ti) < (timestamp_mset ys pf ti)" 
  shows  "(timestamp_mset (ks @ xs)  pf ti) < (timestamp_mset (ks @ ys) pf ti)"
  using assms by (simp add: timestamp_mset_app)

lemma labels_mset_less:
  assumes "cc_invar_t cc_t"
    "congruence_closure.truncate cc_t = cc"
    "a < nr_vars cc" 
    "pf_labels cc ! a = Some (Two x21 x22)"
    "x21 = F x\<^sub>1 x\<^sub>2 \<approx> x'" "x22 = F y\<^sub>1 y\<^sub>2 \<approx> y"
  shows "timestamp_mset [(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)] (proof_forest cc_t) (timestamps cc_t) < 
{#((timestamps cc_t) ! a)#}"
proof-
  have "cc_list cc = cc_list cc_t" unfolding assms(2)[symmetric] congruence_closure.truncate_def 
    by simp
  have timestamps_length: "nr_vars cc = length (timestamps cc_t)" 
    "nr_vars cc = length (proof_forest cc_t)" "pf_labels cc = pf_labels cc_t" 
    using assms unfolding assms(2)[symmetric] congruence_closure.truncate_def 
      congruence_closure.select_convs time_invar_def same_length_invar_def  
    by auto
  then have element_g_0: "(timestamps cc_t) ! a > 0" using assms unfolding time_invar_def 
    by simp
  have timestamp_mset1: "\<forall> l \<in># (mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1))).
l < (timestamps cc_t) ! a" 
  proof
    fix l
    assume "l \<in># mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1))"
    then obtain k where k: "k \<in> set (elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1)"
      "l = (timestamps cc_t) ! k" by auto
    then show "l < timestamps cc_t ! a" using assms
        timestamps_length unfolding timestamps_invar_def by metis
  qed
  have timestamp_mset2: "\<forall> l \<in># (mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2))).
l < (timestamps cc_t) ! a" 
  proof
    fix l
    assume "l \<in># mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2))"
    then obtain k where k: "k \<in> set (elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2)"
      "l = (timestamps cc_t) ! k" by auto
    then show "l < timestamps cc_t ! a" using assms
        timestamps_length unfolding timestamps_invar_def by metis
  qed
  show ?thesis 
  proof(cases "elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2")
    case Nil
    then have "timestamp_mset [(x\<^sub>2, y\<^sub>2)] (proof_forest cc_t) (timestamps cc_t)
= {#0#}" 
      by auto
    then show ?thesis 
    proof(cases "elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1")
      case Nil': Nil
      then have "timestamp_mset ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)]) (proof_forest cc_t) (timestamps cc_t)
= {#0, 0#}" using Nil by auto
      then show ?thesis using element_g_0 
        by auto
    next
      case Cons
      then have *: "timestamp_mset ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)]) (proof_forest cc_t) (timestamps cc_t)
= mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1)) + {#0#}" 
        using Nil by simp
      have "(mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1))) 
< {#timestamps cc_t ! a#}"
        using timestamp_mset1 by auto
      then show ?thesis 
        using element_g_0 * by auto
    qed
  next
    case Cons
    then show ?thesis 
    proof(cases "elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1")
      case Nil
      then have *: "timestamp_mset ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)]) (proof_forest cc_t) (timestamps cc_t)
= {#0#} + mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2))" 
        using Cons by auto
      have "(mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2))) 
< {#timestamps cc_t ! a#}"
        using timestamp_mset2 by auto
      then show ?thesis using element_g_0 *
        by auto
    next
      case Cons': Cons
      then have *: "timestamp_mset ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)]) (proof_forest cc_t) (timestamps cc_t)
= mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1)) + 
mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2))" 
        using Cons by simp
      have "(mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>1 y\<^sub>1))) < {#timestamps cc_t ! a#}"
        "(mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) x\<^sub>2 y\<^sub>2))) < {#timestamps cc_t ! a#}"
        using timestamp_mset1 timestamp_mset2 by auto
      then show ?thesis 
        using element_g_0 * by auto
    qed
  qed
qed

lemma pending_mset_less:
  assumes "cc_invar_t cc_t"
    "path (proof_forest cc) c p a"
    "explain_along_path2 cc a c = (output, pend)" 
    "congruence_closure.truncate cc_t = cc"
    "a < nr_vars cc" 
    "a \<noteq> c"
  shows "(timestamp_mset pend (proof_forest cc_t) (timestamps cc_t)) <
(mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) a c)))"
proof-
  have "cc_invar cc" using assms 
    by auto
  then show ?thesis using assms(2-,1) proof(induction rule: explain_along_path2_induct)
    case (base cc a c p)
    then show ?case by simp
  next
    case (One cc a c p1 p2 x x1 x11 x12 "output" pend)
    have *: "proof_forest cc = proof_forest cc_t" "cc_list cc = cc_list cc_t" 
      unfolding One(14)[symmetric] congruence_closure.truncate_def by fastforce+
    then have path_to_c_dom: "path_to_c_dom ((proof_forest cc_t), a, c)" 
      using path_to_c_domain One(3) by simp
    then show ?case proof(cases "x = c")
      case True
      then have "path_to_c (proof_forest cc_t) a c = [a]" 
        using One(7,4,16) path_to_c_dom path_to_c.psimps \<open>proof_forest cc = proof_forest cc_t\<close> path_to_c_empty by fastforce
      then have mset_a_c: "mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) a c)) 
= {#((timestamps cc_t) ! a)#}" 
        by fastforce
      have "a < length (timestamps cc_t)" 
        using One * unfolding time_invar_def by simp
      then have "(timestamps cc_t) ! a > 0" 
        using One(17) unfolding time_invar_def by blast
      have "pend = []" 
        using One.hyps(5) True explain_along_path2_simp1 by auto
      then have "timestamp_mset pend (proof_forest cc_t) (timestamps cc_t) = {#}"
        by simp
      then show ?thesis 
        using mset_a_c by force
    next
      case False
      have IH: "timestamp_mset pend (proof_forest cc_t) (timestamps cc_t) 
< mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) x c))"
        using One by (metis False)
      have "path_to_c (proof_forest cc_t) a c 
= (path_to_c (proof_forest cc_t) x c) @ [a]" 
        using path_to_c_dom path_to_c.psimps "*"(1) One.hyps(7) One.prems(3) by auto
      then have mset_a_c: "mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) a c))
= {#((timestamps cc_t) ! a)#} + (mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) x c)))" 
        by fastforce
      then show ?thesis 
        using IH mset_le_trans by fastforce
    qed
  next
    case (Two cc a c p1 p2 x x21 x22 x\<^sub>1 x\<^sub>2 x' y\<^sub>1 y\<^sub>2 y "output" pend)
    have *: "proof_forest cc = proof_forest cc_t" "cc_list cc = cc_list cc_t" 
      unfolding Two(19)[symmetric] congruence_closure.truncate_def by fastforce+
    then have path_to_c_dom: "path_to_c_dom ((proof_forest cc_t), a, c)" 
      using path_to_c_domain Two(3) by simp
    then show ?case proof(cases "x = c")
      case True
      then have "path_to_c (proof_forest cc_t) a c = [a]" 
        using Two(7,4,21) path_to_c_dom path_to_c.psimps \<open>proof_forest cc = proof_forest cc_t\<close> path_to_c_empty by fastforce
      then have mset_a_c: "mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) a c)) 
= {#((timestamps cc_t) ! a)#}" 
        by fastforce
      have "a < length (timestamps cc_t)" 
        using Two(20,22) * unfolding time_invar_def by simp
      then have "(timestamps cc_t) ! a > 0" 
        using Two(22) unfolding time_invar_def by blast
      have "pend = []" 
        using Two.hyps(5) True explain_along_path2_simp1 by auto
      then have "timestamp_mset pend (proof_forest cc_t) (timestamps cc_t) = {#}"
        by simp
      have "timestamp_mset ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)]) (proof_forest cc_t) (timestamps cc_t) < 
{#((timestamps cc_t) ! a)#}" 
        using labels_mset_less Two by blast
      then show ?thesis 
        using mset_a_c timestamp_mset_app \<open>pend = []\<close> by fastforce
    next
      case False
      have IH: "timestamp_mset pend (proof_forest cc_t) (timestamps cc_t) 
< mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) x c))"
        using Two by (metis False)
      have "path_to_c (proof_forest cc_t) a c 
= (path_to_c (proof_forest cc_t) x c) @ [a]" 
        using path_to_c_dom path_to_c.psimps "*"(1) Two.hyps(7) Two.prems(3) by auto
      then have mset_a_c: "mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) a c))
= {#((timestamps cc_t) ! a)#} + (mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) x c)))" 
        by fastforce
      have "timestamp_mset ([(x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)]) (proof_forest cc_t) (timestamps cc_t) < 
{#((timestamps cc_t) ! a)#}" 
        using labels_mset_less Two by blast
      then show ?thesis 
        using IH mset_le_trans mset_a_c timestamp_mset_app union_less_mono 
        by (smt (verit))
    qed
  qed
qed

lemma pending_mset_less':
  assumes "cc_invar_t cc_t"
    "c = lowest_common_ancestor (proof_forest cc_t) a b"
    "explain_along_path2 cc a c = (output1, pend1)" 
    "explain_along_path2 cc b c = (output2, pend2)" 
    "congruence_closure.truncate cc_t = cc"
    "are_congruent cc (a \<approx> b)" "a < nr_vars cc" "b < nr_vars cc"
    "a \<noteq> b"
  shows "(timestamp_mset (pend1 @ pend2) (proof_forest cc_t) (timestamps cc_t)) <
(mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) a b)))"
proof-
  have *: "proof_forest cc = proof_forest cc_t" 
    unfolding assms(5)[symmetric] congruence_closure.truncate_def by simp
  then obtain p1 p2 where paths: "path (proof_forest cc_t) c p1 a" "path (proof_forest cc_t) c p2 b"
    using assms(1,5,6,7,8,2) explain_along_path_lowest_common_ancestor by metis
  then show ?thesis
  proof(cases "a = c")
    case True
    then have "b \<noteq> c" 
      using assms(9) by blast
    with pending_mset_less paths assms
    have pend2_mset_less: "(timestamp_mset pend2 (proof_forest cc_t) (timestamps cc_t)) <
(mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) b c)))" 
      using * by metis
    have "pend1 = []" 
      using assms by (simp add: True explain_along_path2_simp1)
    have "path_to_c (proof_forest cc_t) a c = []" 
      using path_to_c_domain path_to_c.psimps paths * True by auto
    then show ?thesis 
      using "*" \<open>pend1 = []\<close> pend2_mset_less append_self_conv2 assms(2) by auto
  next
    case False
    with pending_mset_less paths assms
    have pend1_mset_less: "(timestamp_mset pend1 (proof_forest cc_t) (timestamps cc_t)) <
(mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) a c)))" 
      using * by metis
    then show ?thesis proof(cases "b = c")
      case True
      have "pend2 = []" 
        using assms  by (simp add: True explain_along_path2_simp1)
      have "path_to_c (proof_forest cc_t) b c = []" 
        using path_to_c_domain path_to_c.psimps paths * True by auto
      then show ?thesis 
        using "*" \<open>pend2 = []\<close> pend1_mset_less append_self_conv2 assms(2) by auto
    next
      case False
      with pending_mset_less paths assms
      have pend2_mset_less: "(timestamp_mset pend2 (proof_forest cc_t) (timestamps cc_t)) <
(mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) b c)))" 
        using * by metis
      have t_mset_app: "timestamp_mset (pend1 @ pend2) (proof_forest cc_t) (timestamps cc_t)
= timestamp_mset pend1 (proof_forest cc_t) (timestamps cc_t) +
timestamp_mset pend2 (proof_forest cc_t) (timestamps cc_t)"
        by (simp add: timestamp_mset_app)
      have "elements_on_path (proof_forest cc_t) a b = 
path_to_c (proof_forest cc_t) a c @ path_to_c (proof_forest cc_t) b c"
        using assms(2) elements_on_path.simps * unfolding Let_def by auto
      then have "(mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) a b)))
= (mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) a c)))
+ (mset (map ((!) (timestamps cc_t)) (path_to_c (proof_forest cc_t) b c)))"
        by force
      then show ?thesis using pend1_mset_less t_mset_app pend2_mset_less 
        by (simp add: add_strict_mono)
    qed
  qed
qed

theorem recursive_calls_mset_less:
  assumes "cc_invar_t cc_t"
    "explain_along_path2 (congruence_closure.truncate cc_t) a c = (output1, pend1)" 
    "explain_along_path2 (congruence_closure.truncate cc_t) b c = (output2, pend2)" 
    "c = lowest_common_ancestor (proof_forest cc_t) a b"
    "congruence_closure.truncate cc_t = cc"
    "are_congruent cc (a \<approx> b)" "a < nr_vars cc" "b < nr_vars cc"
  shows "(timestamp_mset (pend1 @ pend2 @ xs) (proof_forest cc_t) (timestamps cc_t)) <
(timestamp_mset ((a, b) # xs) (proof_forest cc_t) (timestamps cc_t))"
proof-
  have "proof_forest cc_t = proof_forest cc"
    unfolding assms(5)[symmetric] congruence_closure.truncate_def by simp
  then have invars: "ufa_invar (proof_forest cc_t)" "a < length (proof_forest cc_t)" 
    "b < length (proof_forest cc_t)" "rep_of (proof_forest cc_t) a = rep_of (proof_forest cc_t) b" 
    using assms proof_forest_invar_def same_length_invar_def  apply auto[3]
    using \<open>proof_forest cc_t = proof_forest cc\<close> are_congruent_rep_of(2) assms by auto
  show ?thesis proof(cases "a = b")
    case True
    then have "elements_on_path (proof_forest cc_t) a b = []"
      using elements_on_path_empty invars by blast
    then have *: "(timestamp_mset ((a, b) # xs) (proof_forest cc_t) (timestamps cc_t))
= {#0#} + (timestamp_mset xs (proof_forest cc_t) (timestamps cc_t))"
      using timestamp_mset_simps by simp
    have "c = a" "c = b" 
      using True invars assms(4) lowest_common_ancestor_a_a by auto
    then have "pend1 = []" "pend2 = []" 
      using assms(2,3) explain_along_path2_simp1 by auto
    then show ?thesis 
      using * by fastforce
  next
    case False
    then have *: "(timestamp_mset (pend1 @ pend2) (proof_forest cc_t) (timestamps cc_t)) <
(mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) a b)))"
      using assms pending_mset_less' by blast
    from False obtain x1 xs2 where eop: "elements_on_path (proof_forest cc_t) a b
= x1 # xs2" using elements_on_path_empty 
      by (meson invars list_encode.cases)
    have "timestamp_mset (pend1 @ pend2 @ xs) (proof_forest cc_t) (timestamps cc_t)
= timestamp_mset (pend1 @ pend2) (proof_forest cc_t) (timestamps cc_t) +
timestamp_mset xs (proof_forest cc_t) (timestamps cc_t)" 
      by (simp add: timestamp_mset_app)
    moreover have "timestamp_mset ((a, b) # xs) (proof_forest cc_t) (timestamps cc_t)
= (mset (map ((!) (timestamps cc_t)) (elements_on_path (proof_forest cc_t) a b)))
+ timestamp_mset xs (proof_forest cc_t) (timestamps cc_t)"
      using False eop by simp
    ultimately show ?thesis using * 
      by fastforce
  qed
qed

theorem recursive_calls_mset_less':
  assumes "cc_invar_t cc_t"
    "explain_along_path2 (congruence_closure.truncate cc_t) a c = (output1, pend1)" 
    "explain_along_path2 (congruence_closure.truncate cc_t) b c = (output2, pend2)" 
    "c = lowest_common_ancestor (proof_forest cc_t) a b"
    "are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)" 
    "a < length (cc_list cc_t)" "b < length (cc_list cc_t)"
  shows "(timestamp_mset (pend1 @ pend2 @ xs) (proof_forest cc_t) (timestamps cc_t)) <
(timestamp_mset ((a, b) # xs) (proof_forest cc_t) (timestamps cc_t))"
proof-
  have "cc_list (congruence_closure.truncate cc_t) = cc_list cc_t"
    unfolding congruence_closure.truncate_def by simp
  with recursive_calls_mset_less assms show ?thesis 
    by metis
qed

lemma equivalent_assumptions:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
  shows "cc_invar cc"
    "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
  using assms(1,4) apply simp
  using assms(2) 
  unfolding assms(4) congruence_closure.truncate_def congruence_closure.select_convs 
  apply blast
  using assms(3) congruence_closure.truncate_def by metis

lemma equivalent_assumptions2:
  assumes "\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc"
    "\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
  shows
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
  using assms(1,2) 
  unfolding assms(3) congruence_closure.truncate_def congruence_closure.select_convs 
  by auto

subsection \<open>Termination of \<open>cc_explain2\<close>\<close>

lemma cc_explain_aux2_domain:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
  shows "cc_explain_aux2_dom (congruence_closure.truncate cc_t, xs)"
  using assms proof (induction "timestamp_mset xs (proof_forest cc_t) (timestamps cc_t)" 
    arbitrary: xs rule: less_induct)
  case less
  then show ?case proof(cases "xs")
    case Nil
    then show ?thesis 
      using cc_explain_aux2.domintros by auto
  next
    case (Cons x xs')
    obtain a b where a_b: "x = (a, b)"
      using prod_decode_aux.cases by blast
    then show ?thesis proof(cases "are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)")
      case True
      have *: "proof_forest (congruence_closure.truncate cc_t) = proof_forest cc_t" 
        using congruence_closure_t.cases congruence_closure.truncate_def congruence_closure.select_convs(5) by metis
      define c where "c = lowest_common_ancestor (proof_forest cc_t) a b"
      have valid: "a < length (proof_forest cc_t)" "b < length (proof_forest cc_t)" 
        "rep_of (proof_forest cc_t) a = rep_of (proof_forest cc_t) b"
        using "less.prems" a_b Cons 
        unfolding same_length_invar_def congruence_closure.truncate_def congruence_closure.select_convs
          same_eq_classes_invar_def
        by auto
      then obtain p1 p2 where paths: "path (proof_forest cc_t) c p1 a" "path (proof_forest cc_t) c p2 b"
        using lowest_common_ancestor_correct less(2) unfolding congruence_closure.truncate_def proof_forest_invar_def 
          c_def * by force
      obtain output1 pending1 output2 pending2 where defs: 
        "(output1, pending1) = explain_along_path2 (congruence_closure.truncate cc_t) a c"
        "(output2, pending2) = explain_along_path2 (congruence_closure.truncate cc_t) b c"
        by (metis old.prod.exhaust)
      have mset_less: "(timestamp_mset (pending1 @ pending2 @ xs') (proof_forest cc_t) (timestamps cc_t))
     < (timestamp_mset xs (proof_forest cc_t) (timestamps cc_t))" 
        using recursive_calls_mset_less'[OF less(2) defs[symmetric] c_def] Cons a_b less.prems 
        by simp
      have "\<forall>(a, b)\<in>set pending1. a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
        "\<forall>(a, b)\<in>set pending1. are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)" 
        "\<forall>(a, b)\<in>set pending2. a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
        "\<forall>(a, b)\<in>set pending2. are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)" 
        using explain_along_path2_pending_in_bounds [of "congruence_closure.truncate cc_t"]
          explain_along_path2_pending[of "congruence_closure.truncate cc_t"]
          paths defs "less.prems"(1)
        unfolding congruence_closure.select_convs congruence_closure.truncate_def 
        by (metis congruence_closure.select_convs(1) congruence_closure.select_convs(5)
            case_prodI2 pending_set_explain_set)+
      then have "\<forall>(a, b)\<in>set (pending1 @ pending2 @ xs'). a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
        "\<forall>(a, b)\<in>set (pending1 @ pending2 @ xs'). are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)" 
        using paths "less.prems" Cons by auto
      then have dom: "cc_explain_aux2_dom (congruence_closure.truncate cc_t, (pending1 @ pending2 @ xs'))"
        using less mset_less by blast
      show ?thesis using cc_explain_aux2.domintros(2)[of "congruence_closure.truncate cc_t" a b xs'] 
        using defs dom True a_b Cons unfolding lowest_common_ancestor.simps c_def * 
        by (metis prod.inject)+
    next
      case False
      then show ?thesis using less a_b Cons
        by simp
    qed
  qed  
qed

subsection \<open>Induction rule on \<open>cc_explain2\<close>\<close>

lemma cc_explain_aux2_induct[consumes 4, case_names base congruent]:
  assumes "cc_invar_t cc_t"
    "\<forall> (a, b) \<in> set xs . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t)"
    "\<forall> (a, b) \<in> set xs . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b)"
    "cc = congruence_closure.truncate cc_t"
    "(\<And>cc . cc_explain_aux2_dom (cc, []) \<Longrightarrow>
cc = congruence_closure.truncate cc_t \<Longrightarrow>
cc_invar cc 
 \<Longrightarrow> P cc [])" 
    "\<And>cc a b xs c output1 pending1 output2  pending2.
    cc_explain_aux2_dom (cc, (a, b) # xs) \<Longrightarrow>
 cc_invar cc \<Longrightarrow>
cc = congruence_closure.truncate cc_t \<Longrightarrow>
(\<forall> (a, b) \<in> set xs . a < nr_vars cc \<and> b < nr_vars cc) \<Longrightarrow>
(\<forall> (a, b) \<in> set xs . are_congruent cc (a \<approx> b)) \<Longrightarrow> 
 a < nr_vars cc \<Longrightarrow> b < nr_vars cc \<Longrightarrow>
        are_congruent cc (a \<approx> b) \<Longrightarrow>
       c = lowest_common_ancestor (proof_forest cc) a b \<Longrightarrow>
    (output1, pending1) = explain_along_path2 cc a c \<Longrightarrow>
    (output2, pending2) = explain_along_path2 cc b c
\<Longrightarrow> P cc (pending1 @ pending2 @ xs)
\<Longrightarrow> cc_invar_t cc_t \<Longrightarrow>
    \<forall> (a, b) \<in> set ((a, b) # xs) . a < length (cc_list cc_t) \<and> b < length (cc_list cc_t) \<Longrightarrow>
    \<forall> (a, b) \<in> set ((a, b) # xs) . are_congruent (congruence_closure.truncate cc_t) (a \<approx> b) 
\<Longrightarrow> P cc ((a, b) # xs)" 
  shows "P cc xs"
proof-
  have "cc_explain_aux2_dom ((congruence_closure.truncate cc_t), xs)" 
    using assms(1-4) cc_explain_aux2_domain 
    by blast
  then show ?thesis using assms 
  proof(induction "congruence_closure.truncate cc_t" xs rule: cc_explain_aux2.pinduct)
    case (2 a b xs)
    define cc where "cc = congruence_closure.truncate cc_t"
    have in_bounds: "a < nr_vars cc" "b < nr_vars cc" using 2(5) 
      unfolding cc_def congruence_closure.truncate_def 
      by auto
    show ?case proof(cases "are_congruent cc (a \<approx> b)")
      case True
      define c where "c = lowest_common_ancestor (proof_forest cc) a b"
      obtain output1 pending1 output2 pending2
        where eap: "(output1, pending1) = explain_along_path2 cc a c" 
          "(output2, pending2) = explain_along_path2 cc b c"
        by (metis old.prod.exhaust)
      obtain p1 p2 where p: "path (proof_forest cc) c p1 a"
        "path (proof_forest cc) c p2 b"  
        using "2.prems"(1) True c_def explain_along_path_lowest_common_ancestor in_bounds
        unfolding cc_def congruence_closure.select_convs proof_forest_invar_def 
        by blast
      then have " \<forall>(k, j)\<in>set (pending1). k < nr_vars cc \<and> j < nr_vars cc" 
        " \<forall>(k, j)\<in>set (pending2). k < nr_vars cc \<and> j < nr_vars cc" 
        " \<forall>(k, j)\<in>set (xs). k < nr_vars cc \<and> j < nr_vars cc" 
        " \<forall>(k, j)\<in>set (pending1). are_congruent cc (k \<approx> j)" 
        " \<forall>(k, j)\<in>set (pending2). are_congruent cc (k \<approx> j)" 
        " \<forall>(k, j)\<in>set (xs). are_congruent cc (k \<approx> j)" 
        using explain_along_path2_pending_in_bounds eap 
        apply (metis "2.prems"(1) cc_def)
        using "2.prems"(1) p(2) 2(5) explain_along_path2_pending_in_bounds eap 
        apply (metis "2.prems"(1) cc_def)
        subgoal using 2(5) 
          unfolding cc_def congruence_closure.select_convs congruence_closure.truncate_def by simp
        using "2.prems"(1) p(1) explain_along_path2_pending_are_congruent eap 
        unfolding cc_def apply (metis "2.prems"(1) cc_def)
        using "2.prems"(1) p(2) 2(5) explain_along_path2_pending_are_congruent eap unfolding cc_def
        apply (metis) using 2(6) by simp 
      then have *: " \<forall>(k, j)\<in>set (pending1 @ pending2 @ xs). k < nr_vars cc \<and> j < nr_vars cc"
        " \<forall>(k, j)\<in>set (pending1 @ pending2 @ xs). are_congruent cc (k \<approx> j)"
        "length (cc_list cc_t) = nr_vars cc"
        apply auto[2]  unfolding cc_def congruence_closure.truncate_def congruence_closure.select_convs 
        by simp
      then have "P cc (pending1 @ pending2 @ xs)"
        using 2(2)[OF True[unfolded cc_def] c_def[unfolded cc_def] eap(1)[unfolded cc_def]
            _ eap(2)[unfolded cc_def] _ 2(4), of output1 pending1 output2 pending2]  
          eap 2 True c_def unfolding cc_def by simp
      then show ?thesis using "2.prems"(6)[OF 2(1)[unfolded cc_def[symmetric]]] 2(1,3,4,5,6,7) 2(1,4)
        using True c_def eap(1) eap(2) in_bounds(1) in_bounds(2) list.set_intros(2) cc_def 
        using \<open>\<forall>(k, j)\<in>set xs. k < nr_vars cc \<and> j < nr_vars cc\<close> by auto
    next
      case False
      then show ?thesis using 2(6) 
        using cc_def by auto
    qed
  qed blast
qed

end