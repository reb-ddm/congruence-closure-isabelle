theory CC_Explain2_Termination
  imports CC_Explain2_Definition
begin 


section \<open>Termination of \<open>cc_explain2\<close>\<close>

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

subsection \<open>Proof that all timestamps are smaller than \<open>time cc_t\<close>\<close>

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
  have "proof_forest (propagate_step l u t pe pf pfl ip a b eq) = add_edge pf a b" 
    by (meson proof_forest_unchanged_step)
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

subsection \<open>Proofs that the multiset of the recursive calls are less than the multiset of xs\<close>

fun timestamp_mset :: "(nat * nat) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat multiset"
  where
    "timestamp_mset [] pf ti = {#}"
  | "timestamp_mset ((a, b) # xs) pf ti = 
  (let eop = elements_on_path pf a b in 
    (case eop of 
      [] \<Rightarrow> (add_mset 0 {#}) | 
      (e1 # eop') \<Rightarrow> mset (map ((!) ti) (e1 # eop')))
 + timestamp_mset xs pf ti)"

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
    then have rec: "timestamp_mset ((a, b) # xs) pf ti = (add_mset 0 {#}) + timestamp_mset xs pf ti" 
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
= (add_mset 0 {#}) + timestamp_mset (removeAll x xs) pf ti" 
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

lemma recursive_calls_mset_less:
  assumes "cc_invar_t cc_t"
    "explain_along_path2 (congruence_closure.truncate cc_t) a c = (output1, pend1)" 
    "explain_along_path2 (congruence_closure.truncate cc_t) b c = (output2, pend2)" 
    "c = lowest_common_ancestor (proof_forest cc_t) a b"
  shows "(timestamp_mset (pend1 @ pend2 @ xs) (proof_forest cc_t) (timestamps cc_t)) <
(timestamp_mset ((a, b) # xs) (proof_forest cc_t) (timestamps cc_t))"
proof-
  define max_timestamp_ab_b where 
    "max_timestamp_ab_b = Max (set_mset (timestamp_mset [(a, b)] (proof_forest cc_t) (timestamps cc_t)))"
  have 
    "\<forall> x \<in># (timestamp_mset pend1 (proof_forest cc_t) (timestamps cc_t)).
x < max_timestamp_ab_b"
    using assms(1) unfolding timestamps_invar_def sorry
  show ?thesis sorry
qed

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
      have "a < length (proof_forest cc_t)" "b < length (proof_forest cc_t)" 
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
        using recursive_calls_mset_less defs[symmetric] c_def less(2) * Cons a_b by blast 
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

subsubsection \<open>Induction rule on \<open>cc_explain2\<close>\<close>

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