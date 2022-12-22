theory CC_Invars
  imports CC_Abstraction
begin

subsection \<open>The invariants remain invariant after the loop of propagate\<close>

paragraph \<open>Invariants after a step in the loop\<close>

lemma lookup_invar_loop2:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar ?base")  
    "u1 = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l"
  shows
    "lookup_invar \<lparr>cc_list = l, use_list = u[rep_b := u1 # u ! rep_b], lookup = update_lookup t l u1,
             pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    (is "lookup_invar ?step")  
  unfolding lookup_invar_def
proof(standard, standard, standard, standard, standard, standard)
  fix i j
  assume i_j: "i < nr_vars ?step" "j < nr_vars ?step"
    "cc_list ?step ! i = i \<and> cc_list ?step ! j = j"
  show "lookup_valid_element (lookup ?step) (cc_list ?step) i j"
  proof(cases "rep_of l a\<^sub>1 = i \<and> rep_of l a\<^sub>2 = j")
    case True
    let ?new_t = "upd t (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) (Some (F a\<^sub>1 a\<^sub>2 \<approx> aa))"
    from assms i_j nth_list_update_eq nth_update_invalid show ?thesis 
      unfolding congruence_closure.select_convs lookup_invar_def assms(2) update_lookup.simps
      apply(cases "rep_of l a\<^sub>1 < length ?new_t")
       apply(cases "rep_of l a\<^sub>2 < length (?new_t ! rep_of l a\<^sub>1)")
      using True by auto
  next
    case False
    then have "lookup ?base ! i ! j = lookup ?step ! i ! j" 
      using assms(2) update_lookup_unchanged by force
    from i_j assms have "lookup_valid_element (update_lookup t l u1) l i j" 
      unfolding lookup_invar_def congruence_closure.select_convs
      using False update_lookup_unchanged by presburger
    with assms show ?thesis unfolding lookup_invar_def congruence_closure.select_convs
      by blast
  qed
next
  from assms show "quadratic_table (lookup ?step)"
    unfolding lookup_invar_def congruence_closure.select_convs
    by (metis (no_types, lifting) length_list_update nth_list_update_eq nth_list_update_neq update_lookup.simps(1))
qed

lemma use_list_invar_loop2:
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar ?base")  
    "u1 = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l"
    "rep_b < length u"
    "rep_of l a\<^sub>1 = rep_b \<or> rep_of l a\<^sub>2 = rep_b" 
  shows
    "use_list_invar \<lparr>cc_list = l, use_list = u[rep_b := u1 # u ! rep_b], lookup = update_lookup t l u1,
             pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    (is "use_list_invar ?step")  
  unfolding use_list_invar_def
proof(standard, standard, standard, standard, standard)
  fix i j
  assume i_j: "i < nr_vars ?step" "j < length (use_list ?step ! i)" "cc_list ?step ! i = i"
  show "use_list_valid_element (use_list ?step ! i ! j) (cc_list ?step) i"
  proof(cases "i = rep_b")
    case True
    then show ?thesis proof(cases j)
      case 0
      with True assms(6) have "use_list ?step ! i ! j = u1" 
        by simp
      then show ?thesis 
        using True assms(2) assms(3) assms(4) assms(5) assms(7) by force
    next
      case (Suc nat)
      with True assms(6) have "use_list ?step ! i ! j = u ! i ! (j - 1)"  
        by simp
      with assms i_j True show ?thesis unfolding use_list_invar_def
        by (simp add: Suc)
    qed
  next
    case False
    then have "u ! i ! j = use_list ?step ! i ! j" 
      by fastforce
    with assms i_j False show ?thesis unfolding use_list_invar_def 
      by force
  qed
qed

lemma pending_invar_loop1:
  assumes "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "pending_invar ?base")
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l"
    "u1 = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l"
    "lookup_Some t l u1" 
  shows
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l u1#pe,
            proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    (is "pending_invar ?step")  
  unfolding pending_invar_def
proof(standard)+
  fix i j
  assume i_j: "i < length (pending ?step)"
  show "valid_vars_pending (pending ?step ! i) (cc_list ?step)"
  proof(cases i)
    case 0
    then have *: "(link_to_lookup t l u1 # pe) ! i = link_to_lookup t l u1"
      by simp
    have **: "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> aa) (length l)" 
      by (simp add: assms)
    have "lookup_entry t l a\<^sub>1 a\<^sub>2 \<noteq> None"  "l ! rep_of l a\<^sub>1 = rep_of l a\<^sub>1" "l ! rep_of l a\<^sub>2 = rep_of l a\<^sub>2"
      using assms 
        apply (metis is_none_simps(1) lookup_Some.simps(1))
      by (simp_all add: assms rep_of_min)
    with assms obtain c\<^sub>1 c\<^sub>2 c where "lookup_entry t l a\<^sub>1 a\<^sub>2 = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)" and
      "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l" "rep_of l a\<^sub>1 = rep_of l c\<^sub>1 \<and> rep_of l a\<^sub>2 = rep_of l c\<^sub>2"
      unfolding lookup_invar_def congruence_closure.select_convs
      by (metis rep_of_less_length_l)
    with 0 ** show ?thesis 
      unfolding congruence_closure.select_convs * assms link_to_lookup.simps
      by simp
  next
    case (Suc nat)
    then have "pending ?step ! i = pending ?base ! (i - 1)"
      by simp
    then show ?thesis using assms unfolding pending_invar_def 
      using Suc i_j by force
  qed
qed

lemma correctness_invar_loop1:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l"
    "lookup_Some t l u1" 
    "u1 = (F a\<^sub>1 a\<^sub>2 \<approx> a)" "a\<^sub>1 < length l" "a\<^sub>2 < length l" 
  shows "Congruence_Closure
     (representativeE
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
          input = ip\<rparr> \<union>
      pending_set pe \<union> set (u1 # urest)) = 
Congruence_Closure
      (representativeE
        \<lparr>cc_list = l, use_list = u, lookup = t, pending = link_to_lookup t l u1 # pe,
                 proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
       pending_set
        (link_to_lookup t l u1 # pe) \<union>
       set urest)"
    (is "Congruence_Closure ?base = Congruence_Closure ?step")
proof-
  from assms have entry_not_none: "t ! rep_of l a\<^sub>1 ! rep_of l a\<^sub>2 \<noteq> None" 
    by (metis is_none_simps(1) lookup_Some.simps(1))
  have valid: "l ! rep_of l a\<^sub>1 = rep_of l a\<^sub>1 \<and> l ! rep_of l a\<^sub>2 = rep_of l a\<^sub>2"
    "rep_of l a\<^sub>1 < length l \<and> rep_of l a\<^sub>2 < length l" using assms 
    by (simp add: rep_of_min rep_of_less_length_l)+
  with assms entry_not_none 
  obtain b\<^sub>1 b\<^sub>2 b where entry: "lookup_entry t l a\<^sub>1 a\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b)" 
    "b\<^sub>1 < length l" "b\<^sub>2 < length l" "b < length l" "rep_of l a\<^sub>1 = rep_of l b\<^sub>1 \<and> rep_of l a\<^sub>2 = rep_of l b\<^sub>2"
    unfolding lookup_invar_def congruence_closure.select_convs 
    by metis
  from entry CC_lookup_entry_in_CC 
  have f2: "(F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> Congruence_Closure ?base" using valid
    by (metis Congruence_Closure_split_rule assms(1) congruence_closure.select_convs(1) congruence_closure.select_convs(3))
  from assms(1) have "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
pending = link_to_lookup t l u1 # pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    unfolding lookup_invar_def by simp
  with entry CC_lookup_entry_in_CC 
  have f2': "(F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> Congruence_Closure ?step" using assms(4) valid
    by (metis Congruence_Closure_split_rule congruence_closure.select_convs(1,3))
  from entry CC_same_rep assms have a_c: "(a\<^sub>1 \<approx> b\<^sub>1) \<in> Congruence_Closure ?base"
    "(a\<^sub>2 \<approx> b\<^sub>2) \<in> Congruence_Closure ?base" 
    by (metis Congruence_Closure_split_rule congruence_closure.select_convs(1))+
  from entry CC_same_rep assms have c_a: "(b\<^sub>1 \<approx> a\<^sub>1) \<in> Congruence_Closure ?step" 
    "(b\<^sub>2 \<approx> a\<^sub>2) \<in> Congruence_Closure ?step " 
    by (metis Congruence_Closure_split_rule congruence_closure.select_convs(1))+
  have "u1 \<in> ?base"
    by simp
  have *: "u1 \<in> ?base"
    by simp
  then have f1: "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> Congruence_Closure ?base" 
    using * assms(4) by auto
  show ?thesis 
  proof(rule Congruence_Closure_eq)
    fix eq
    assume "eq \<in> ?step"
    then consider
      (rep) c where "eq = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
    | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
      "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    | (pending) "eq \<in> pending_set pe"
    | (new_pending) "eq \<in> pending_set [link_to_lookup t l u1]"
    | (urest) "eq \<in> set urest"
      unfolding representativeE_def using pending_set_union
      by fastforce
    then show "eq \<in> Congruence_Closure ?base"
    proof(cases)
      case new_pending
      with new_pending assms(4) entry have eq: "eq = (a \<approx> b)" 
        by auto
      with eq f1 f2 a_c monotonic show ?thesis 
        by blast
    qed (auto simp add: representativeE_def)
  next
    fix eq' 
    assume  "eq' \<in> ?base"
    then consider
      (rep) c where "eq' = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
    | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq' = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
      "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    | (pending) "eq' \<in> pending_set pe"
    | (new_pending) "eq' = u1"
    | (urest) "eq' \<in> set urest" 
      unfolding representativeE_def congruence_closure.select_convs
      by fastforce
    then show "eq' \<in> Congruence_Closure ?step"
    proof(cases)
      case pending
      with pending_set_union' have "eq' \<in> pending_set (link_to_lookup t l u1 # pe)"
        by (metis append_Cons append_eq_append_conv2 )
      with base show ?thesis 
        using Congruence_Closure_union by blast
    next
      case new_pending
      then have "(a \<approx> b) \<in> pending_set (link_to_lookup t l u1 # pe)"
        using assms(4) entry by fastforce
      then have a_b: "(a \<approx> b) \<in> Congruence_Closure ?step"
        using Congruence_Closure_union base by auto
      then have "(F a\<^sub>1 a\<^sub>2 \<approx> b) \<in> Congruence_Closure ?step"
        using c_a(1) c_a(2) f2' by blast
      with base show ?thesis 
        using assms(4) a_b new_pending by blast
    qed (auto simp add: representativeE_def)
  qed
qed

lemma correctness_invar_loop2:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>" 
    "length l = length t" "ufa_invar l" 
    "\<not> lookup_Some t l u1"
    "u1 = (F a\<^sub>1 a\<^sub>2 \<approx> a)" "a\<^sub>1 < length l" "a\<^sub>2 < length l" "a < length l" 
  shows "Congruence_Closure
     (representativeE
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
          input = ip\<rparr> \<union> pending_set pe \<union> set (u1 # urest)) = 
Congruence_Closure
     (representativeE
       \<lparr>cc_list = l, use_list = u[rep_b := u1 # u ! rep_b],
                lookup = update_lookup t l u1, pending = pe, proof_forest = pf, pf_labels = pfl,
                input = ip\<rparr> \<union>
      pending_set pe \<union> set urest) "
    (is "Congruence_Closure ?base = Congruence_Closure ?step")
proof(rule Congruence_Closure_eq)
  fix eq
  assume "eq \<in> ?step"
  then consider
    (rep) c where "eq = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
  | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
    "c < length l" "l ! a' = a'" "l ! b' = b'" "update_lookup t l u1 ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "\<not> (a' = rep_of l a\<^sub>1 \<and> b' = rep_of l a\<^sub>2)"
  | (new_lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
    "c < length l" "l ! a' = a'" "l ! b' = b'" "update_lookup t l u1 ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "a' = rep_of l a\<^sub>1 \<and> b' = rep_of l a\<^sub>2"
  | (pending) "eq \<in> pending_set pe"
  | (urest) "eq \<in> set urest"
    unfolding representativeE_def using pending_set_union
    by force
  then show "eq \<in> Congruence_Closure ?base"
  proof(cases)
    case lookup
    with assms have "update_lookup t l u1 ! a' ! b' = t ! a' ! b'"
      by (metis lookup(8) update_lookup_unchanged)
    with lookup have "eq \<in> (representativeE
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
          input = ip\<rparr>)" unfolding representativeE_def congruence_closure.select_convs 
      by auto
    with assms lookup show ?thesis unfolding representativeE_def congruence_closure.select_convs
      using Congruence_Closure_split_rule base by presburger
  next
    case new_lookup
    from assms have "length t = length l " "length (t ! a') = length l" 
       apply simp using assms new_lookup(2) unfolding lookup_invar_def by auto
    with new_lookup have lookup_entry: "update_lookup t l u1 ! a' ! b' = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)"
      unfolding assms(5) update_lookup.simps by fastforce
    then have cc1: "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> Congruence_Closure ?base" using assms(5)
      by auto
    have "c = a" 
      using lookup_entry new_lookup(7) by simp
    with new_lookup(8,4) a_eq_rep_of_a_in_CC assms(6,7)
    have cc2: "(a\<^sub>1 \<approx> a') \<in> Congruence_Closure ?base" "(a\<^sub>2 \<approx> b') \<in> Congruence_Closure ?base" 
      "(c \<approx> rep_of l c) \<in> Congruence_Closure ?base" 
      by (metis Congruence_Closure_split_rule congruence_closure.select_convs(1))+
    then have "(F a' b' \<approx> c) \<in> Congruence_Closure ?base" 
      using assms(5) by (metis \<open>c = a\<close> cc1 transitive3)
    then show ?thesis 
      using cc2(3) new_lookup(1) transitive2 by blast
  qed (auto simp add: base representativeE_def)
next
  fix eq'
  assume  "eq' \<in> ?base"
  then consider
    (rep) c where "eq' = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
  | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq' = (F a' b' \<approx> rep_of l c)" "a' < length l" "b' < length l"
    "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "\<not> (a' = rep_of l a\<^sub>1 \<and> b' = rep_of l a\<^sub>2)"
  | (new_lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq' = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
    "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "a' = rep_of l a\<^sub>1 \<and> b' = rep_of l a\<^sub>2"
  | (pending) "eq' \<in> pending_set pe"
  | (new_pending) "eq' = u1"
  | (urest) "eq' \<in> set urest" 
    unfolding representativeE_def congruence_closure.select_convs
    by force
  then show "eq' \<in> Congruence_Closure ?step"
  proof(cases)
    case lookup
    then have "update_lookup t l u1 ! a' ! b' = t ! a' ! b'"
      by (metis assms(5) lookup(8) update_lookup_unchanged)
    with lookup show ?thesis unfolding representativeE_def congruence_closure.select_convs
      using Congruence_Closure_split_rule mem_Collect_eq by fastforce
  next
    case new_lookup
    then have "lookup_Some t l u1" 
      by (simp add: assms(5))
    with assms(4) have "False" 
      by simp
    then show ?thesis by simp
  next
    case new_pending
    with assms have "length t = length l" "length (t ! rep_of l a\<^sub>1) = length l" 
       apply simp using assms rep_of_less_length_l unfolding lookup_invar_def 
      by fastforce
    then have "lookup_entry (update_lookup t l u1) l a\<^sub>1 a\<^sub>2 = Some u1" 
      by (simp add: assms(3,5,6,7)  rep_of_less_length_l)
    with assms have "(F (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) \<approx> rep_of l a) \<in> representativeE
       \<lparr>cc_list = l, use_list = u[rep_b := u1 # u ! rep_b], lookup = update_lookup t l u1,
          pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      unfolding representativeE_def congruence_closure.select_convs 
      using rep_of_less_length_l rep_of_min by fastforce
    then show ?thesis using CC_F_rep_of_a_imp_F_a base assms
      by (simp add: Congruence_Closure_split_rule new_pending)      
  qed (auto simp add: representativeE_def)
qed

lemma in_set_Cons_use_list:
  assumes "rep_b' < length u" 
    "i \<noteq> rep_of l a" "eq \<in> set (u ! i)"
  shows "i \<noteq> rep_of l a
\<Longrightarrow> eq \<in> set (u ! i) \<Longrightarrow> eq \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! i)"
proof(cases "i = rep_b'")
  case True
  from True have "u[rep_b' := u1' # u ! rep_b'] ! i = u1' # u ! rep_b'"
    by (simp add: assms)
  with True assms show ?thesis 
    by force
next
  case False
  from False have "u[rep_b' := u1' # u ! rep_b'] ! i = u ! i"
    by auto
  then show ?thesis 
    using assms by auto
qed

lemma lookup_invar2_loop1:
  assumes "lookup_invar2 \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar2 ?base")
    "lookup_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l"
    "a < length l" "b < length l" 
    "rep_of l a \<noteq> rep_of l b"
    "lookup_Some t (ufa_union l a b) u1'"
    "u1' = (F d\<^sub>1 d\<^sub>2 \<approx> d)" "d\<^sub>1 < length l" "d\<^sub>2 < length l" 
  shows "lookup_invar2
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
        pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar2 ?loop1")
  unfolding lookup_invar2_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  have ufa_invar_mini_step: "ufa_invar (ufa_union l a b)"
    using assms(3-6) ufa_union_invar by simp
  fix a' b' c c\<^sub>1 c\<^sub>2
  assume prems: "a' < length (ufa_union l a b)"
    "b' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "ufa_union l a b ! b' = b'"
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)" 
  from prems have *: "l ! a' = a'" "l ! b' = b'" "a' < length l" "b' < length l" 
    using assms(3-6) ufa_invar_mini_step ufa_union_root apply blast+
    using prems by auto
  with prems assms have "a' \<noteq> rep_of l a" "b' \<noteq> rep_of l a" 
    by (metis nth_list_update_eq)+
  with assms * prems obtain b\<^sub>1 b\<^sub>2 cb a\<^sub>1 a\<^sub>2 ca where use_list: 
    "(F a\<^sub>1 a\<^sub>2 \<approx> ca) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ca \<approx> c) \<in> Congruence_Closure
            (cc_list_set (cc_list ?base) \<union> pending_set pe)"
    "(F b\<^sub>1 b\<^sub>2 \<approx> cb) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (cb \<approx> c) \<in> Congruence_Closure
            (cc_list_set (cc_list ?base) \<union> pending_set pe)" 
    unfolding lookup_invar2_def congruence_closure.select_convs by blast
  with assms * use_list_invar_less_n_in_set use_list
    prems * lookup_invar_less_n length_list_update
  have length_b: "b\<^sub>1 < length l" "b\<^sub>2 < length l" "cb < length l" "a\<^sub>1 < length l" "a\<^sub>2 < length l" 
    "ca < length l" "c\<^sub>1 < length l" "c\<^sub>2 < length l"
    by (metis (no_types, lifting))+
  with rep_of_ufa_union_invar assms(1,2,3) use_list
  have "rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
    "rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    " rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
    "rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    by metis+
  with use_list length_b have *: "(F a\<^sub>1 a\<^sub>2 \<approx> ca) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ca \<approx> c) \<in> Congruence_Closure
            (cc_list_set (cc_list ?loop1) \<union> pending_set pe)"
    "(F b\<^sub>1 b\<^sub>2 \<approx> cb) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (cb \<approx> c) \<in> Congruence_Closure
            (cc_list_set (cc_list ?loop1) \<union> pending_set pe)"
    unfolding congruence_closure.select_convs
    by blast+
  have **: "({(aa \<approx> rep_of (ufa_union l a b) aa) |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe)) =
(cc_list_set (cc_list ?loop1) \<union> pending_set pe) \<union> pending_set ([link_to_lookup t (ufa_union l a b) u1'])"
    unfolding congruence_closure.select_convs 
    by auto
  with * show " (\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({(aa \<approx> rep_of (ufa_union l a b) aa) |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))
            ) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe)))"
    unfolding ** using assms Congruence_Closure_split_rule   by meson
qed

lemma lookup_invar2_loop2:
  assumes "lookup_invar2
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar2 ?base")
    "lookup_invar
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>"
    "length l = length t"
    "ufa_invar l" "a < length l" "b < length l" 
    "rep_of l a \<noteq> rep_of l b"
    "\<not> lookup_Some t (ufa_union l a b) u1'"
    "u1' = (F d\<^sub>1 d\<^sub>2 \<approx> d)" "d\<^sub>1 < length l" "d\<^sub>2 < length l"  "d < length l"
    "rep_b' < length u"
    "(rep_of l d\<^sub>1 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l d\<^sub>1) d\<^sub>1 d\<^sub>2 d)
\<and> 
(rep_of l d\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l d\<^sub>2) d\<^sub>1 d\<^sub>2 d)"
    "rep_of l a = rep_of l d\<^sub>1 \<or> rep_of l a = rep_of l d\<^sub>2"
    "rep_b' = rep_of l b"
  shows "lookup_invar2
     \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar2 ?loop2")
  unfolding lookup_invar2_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  have ufa_invar_mini_step: "ufa_invar (ufa_union l a b)"
    by (simp add: assms(5,6,7) ufa_union_invar)
  fix a' b' c c\<^sub>1 c\<^sub>2
  assume prems: "a' < length (ufa_union l a b)"
    "b' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "ufa_union l a b ! b' = b'"
    "update_lookup t (ufa_union l a b) u1' ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)" 
  from prems have *: "l ! a' = a'" "l ! b' = b'" "a' < length l" "b' < length l" 
    using assms(5-7) ufa_union_root apply blast+
    using prems by auto
  with prems assms have "a' \<noteq> rep_of l a" "b' \<noteq> rep_of l a" 
    by (metis nth_list_update_eq)+
  have "update_lookup t (ufa_union l a b) u1' ! a' ! b' \<noteq> None" 
    using prems by fast
  with assms(2) prems obtain k\<^sub>1 k\<^sub>2 k where 
    "t ! a' ! b' = Some (F k\<^sub>1 k\<^sub>2 \<approx> k)" 
    "rep_of (ufa_union l a b) k\<^sub>1 = a'" "rep_of (ufa_union l a b) k\<^sub>2 = b'"
  if "t ! a' ! b' \<noteq> None" 
    unfolding lookup_invar_def congruence_closure.select_convs 
    by blast
  with assms(2) prems(1-3) ufa_invar_mini_step obtain k\<^sub>1 k\<^sub>2 k where 
    "update_lookup t (ufa_union l a b) u1' ! a' ! b' = Some (F k\<^sub>1 k\<^sub>2 \<approx> k)" 
    "rep_of (ufa_union l a b) k\<^sub>1 = a'" "rep_of (ufa_union l a b) k\<^sub>2 = b'"
    unfolding lookup_invar_def congruence_closure.select_convs apply(cases "t ! a' ! b'")
     apply (metis "*"(3) "*"(4) \<open>update_lookup t (ufa_union l a b) u1' ! a' ! b' \<noteq> None\<close> assms(4,10) nth_list_update_eq update_lookup.simps(1) update_lookup_unchanged)
    using assms(9,10) update_lookup_unchanged' by auto
  then have a_b: "rep_of (ufa_union l a b) c\<^sub>1 = a'" "rep_of (ufa_union l a b) c\<^sub>2 = b'"
    using prems(5) by auto
  show "(\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! a') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({(aa \<approx> (rep_of (ufa_union l a b) aa)) |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set pe)
            ) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({(aa \<approx> (rep_of (ufa_union l a b) aa)) |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set pe))"
  proof(cases "update_lookup t (ufa_union l a b) u1' ! a' ! b' = t ! a' ! b'")
    case True
    with assms * prems obtain b\<^sub>1 b\<^sub>2 cb a\<^sub>1 a\<^sub>2 ca where use_list: 
      "(F a\<^sub>1 a\<^sub>2 \<approx> ca) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ca \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list ?base) \<union>
             pending_set (pe))"
      "(F b\<^sub>1 b\<^sub>2 \<approx> cb) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (cb \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list ?base) \<union>
             pending_set pe)" 
      unfolding lookup_invar2_def congruence_closure.select_convs True by blast
    with assms * use_list_invar_less_n_in_set use_list
      prems True * lookup_invar_less_n length_list_update
    have length_b: "b\<^sub>1 < length l" "b\<^sub>2 < length l" "cb < length l" "a\<^sub>1 < length l" "a\<^sub>2 < length l" 
      "ca < length l" "c\<^sub>1 < length l" "c\<^sub>2 < length l"
      by (metis (no_types, lifting))+
    with rep_of_ufa_union_invar assms(1,2,3) use_list
    have "rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
      "rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
      " rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
      "rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
      by metis+
    with use_list length_b have *: "(F a\<^sub>1 a\<^sub>2 \<approx> ca) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ca \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list ?loop2) \<union>
             pending_set pe)"
      "(F b\<^sub>1 b\<^sub>2 \<approx> cb) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (cb \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list ?loop2) \<union>
             pending_set pe)" 
      unfolding congruence_closure.select_convs by blast+
    have "i \<noteq> rep_of l a 
\<Longrightarrow> eq \<in> set (u ! i) \<Longrightarrow> eq \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! i)"
      for eq i using assms(14) in_set_Cons_use_list 
      by fast 
    with * show ?thesis
      using \<open>a' \<noteq> rep_of l a\<close> \<open>b' \<noteq> rep_of l a\<close> 
      unfolding congruence_closure.select_convs 
      by blast
  next
    case False
    with prems(5) have u1': "u1' = (F c\<^sub>1 c\<^sub>2 \<approx> c)" 
      unfolding assms(10) update_lookup.simps by (metis nth_list_update' option.inject)
    have u1_in_set: "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! rep_of l b)" 
      using assms(10,14,17) u1' by auto
    have eq_rep_l_b: "eq \<in> set (u ! rep_of l b)
\<Longrightarrow> eq \<in> set (u[rep_b' := u1' # u ! rep_b'] ! rep_of l b)" for eq 
      by (metis assms(14,8) in_set_Cons_use_list)
    have eq_not_rep_l_b: "rep_of l b \<noteq> kk \<Longrightarrow> eq \<in> set (u ! kk)
\<Longrightarrow> eq \<in> set (u[rep_b' := u1' # u ! rep_b'] ! kk)" for eq kk
      by (metis assms(14,8) in_set_Cons_use_list)
    consider "rep_of l a = rep_of l c\<^sub>1" "rep_of l a \<noteq> rep_of l c\<^sub>2"
      | "rep_of l a = rep_of l c\<^sub>1" "rep_of l a = rep_of l c\<^sub>2"
      | "rep_of l a \<noteq> rep_of l c\<^sub>1" "rep_of l a = rep_of l c\<^sub>2"
      using \<open>u1' = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> assms(16,10) by fastforce
    then show ?thesis proof(cases)
      case 1
      with a_b have "a' = rep_of l b"
        using \<open>u1' = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> assms ufa_union_aux by simp
      then have "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! a') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?loop2) \<union>
          pending_set pe))" 
        using Congruence_Closure.reflexive u1_in_set by blast
      from assms have *: "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! b') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?base) \<union>
          pending_set pe))" 
        unfolding congruence_closure.select_convs 
        by (metis (no_types, lifting) "1"(2) \<open>rep_of (ufa_union l a b) k\<^sub>2 = b'\<close> \<open>update_lookup t (ufa_union l a b) u1' ! a' ! b' = Some (F k\<^sub>1 k\<^sub>2 \<approx> k)\<close> equation.inject(2) option.inject prems(5) u1' ufa_union_aux)
      then have "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! b') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?loop2) \<union>
          pending_set pe))" 
        apply(cases "b' \<noteq> rep_of l b")
        using * unfolding congruence_closure.select_convs 
         apply (metis (no_types, lifting) eq_not_rep_l_b)
        using * unfolding congruence_closure.select_convs 
        by (metis (no_types, lifting) eq_rep_l_b)
      then show ?thesis unfolding congruence_closure.select_convs
        using Congruence_Closure.reflexive \<open>a' = rep_of l b\<close> u1_in_set by blast
    next
      case 2
      with a_b have "a' = rep_of l b"
        using \<open>u1' = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> assms ufa_union_aux by simp
      then have "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! a') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?loop2) \<union>
          pending_set pe))" 
        using Congruence_Closure.reflexive u1_in_set by blast
      from a_b 2 have "b' = rep_of l b"
        using \<open>u1' = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> assms ufa_union_aux 
        by auto
      then have *: "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! b') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?loop2) \<union>
          pending_set pe))" 
        using Congruence_Closure.reflexive u1_in_set 
        by fast
      then show ?thesis unfolding congruence_closure.select_convs
        using Congruence_Closure.reflexive \<open>a' = rep_of l b\<close> u1_in_set by blast
    next
      case 3
      with a_b have "b' = rep_of l b"
        using \<open>u1' = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> assms ufa_union_aux by simp
      then have "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! b') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?loop2) \<union>
          pending_set pe))" 
        using Congruence_Closure.reflexive u1_in_set by blast
      from assms have *: "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! a') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?base) \<union>
          pending_set pe))" 
        unfolding congruence_closure.select_convs
        by (metis (no_types, lifting) "3"(1) \<open>rep_of (ufa_union l a b) k\<^sub>1 = a'\<close> \<open>update_lookup t (ufa_union l a b) u1' ! a' ! b' = Some (F k\<^sub>1 k\<^sub>2 \<approx> k)\<close> equation.inject(2) option.inject prems(5) u1' ufa_union_aux)
      then have "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! a') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        (ba \<approx> c) \<in> Congruence_Closure
         (cc_list_set
           (cc_list ?loop2) \<union>
          pending_set pe))" 
        apply(cases "a' \<noteq> rep_of l b")
        using * unfolding congruence_closure.select_convs 
         apply (metis (no_types, lifting) eq_not_rep_l_b)
        using * unfolding congruence_closure.select_convs 
        by (metis (no_types, lifting) eq_rep_l_b)
      then show ?thesis unfolding congruence_closure.select_convs
        using Congruence_Closure.reflexive \<open>b' = rep_of l b\<close> u1_in_set by blast
    qed
  qed
qed

lemma lookup_invar2_prems_loop1:
  assumes "\<forall>eq'\<in>set (u1' # urest').
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)"
  shows "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
               pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
               input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
               pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
               input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)"
proof
  fix eq'
  let ?loop1 = "\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, 
                pf_labels = pfl, input = ip\<rparr>"
  let ?base = "\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
                pf_labels = pfl, input = ip\<rparr>"
  assume "eq' \<in> set urest'"
  then have "eq' \<in> set (u1' # urest')"
    by fastforce
  with assms obtain c\<^sub>1 c\<^sub>2 c where *: "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           (\<exists>b\<^sub>1 b\<^sub>2 ba.
               (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>1) \<and>
               rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
               rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
               (ba \<approx> c) \<in> Congruence_Closure
                (cc_list_set
                  (cc_list ?base) \<union>
                 pending_set pe)
                )) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           (\<exists>b\<^sub>1 b\<^sub>2 ba.
               (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>2) \<and>
               rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
               rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
               (ba \<approx> c) \<in> Congruence_Closure
                (cc_list_set
                  (cc_list ?base) \<union>
                 pending_set pe)))" 
    unfolding congruence_closure.select_convs by fast
  have **: "({(aa \<approx> rep_of (ufa_union l a b) aa) |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe)) =
(cc_list_set (cc_list ?loop1)
 \<union> pending_set pe) \<union> pending_set ([link_to_lookup t (ufa_union l a b) u1'])"
    unfolding congruence_closure.select_convs 
    by auto
  then have CC_loop1: "Congruence_Closure
                (cc_list_set
                  (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) \<union>
                 pending_set pe )            
 \<subseteq> Congruence_Closure
                    (cc_list_set
                  (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
               pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
               input = ip\<rparr>) \<union>
                 pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))" 
    using Congruence_Closure_union unfolding ** congruence_closure.select_convs by fast 
  then have "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>1) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                   (ba \<approx> c) \<in> Congruence_Closure
                    (cc_list_set
                      (cc_list ?loop1) \<union>
                     pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))
                    )) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>2) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                   (ba \<approx> c) \<in> Congruence_Closure
                    (cc_list_set
                      (cc_list ?loop1) \<union>
                     pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))))"
    using "*" by blast
  then show "\<exists>c\<^sub>1 c\<^sub>2 c.
              eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                   pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
                   input = ip\<rparr>
                (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                   pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
                   input = ip\<rparr>
                (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)" 
    unfolding congruence_closure.select_convs by blast
qed

lemma lookup_invar2_prems_loop2:
  assumes "\<forall>eq'\<in>set (u1' # urest').
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)"
    "rep_b' < length u"
  shows "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
        lookup = update_lookup t (ufa_union l a b) u1', 
        pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
        lookup = update_lookup t (ufa_union l a b) u1', 
        pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)"
proof
  fix eq'
  assume "eq' \<in> set urest'"
  then have "eq' \<in> set (u1' # urest')"
    by fastforce
  with assms obtain c\<^sub>1 c\<^sub>2 c where *: "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           (\<exists>b\<^sub>1 b\<^sub>2 ba.
               (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>1) \<and>
               rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
               rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
               (ba \<approx> c) \<in> Congruence_Closure
                (cc_list_set
                  (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) \<union>
                 pending_set pe)
                )) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           (\<exists>b\<^sub>1 b\<^sub>2 ba.
               (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>2) \<and>
               rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
               rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
               (ba \<approx> c) \<in> Congruence_Closure
                (cc_list_set
                  (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) \<union>
                 pending_set pe)))" 
    unfolding congruence_closure.select_convs by fast
  have "i \<noteq> rep_of l a 
\<Longrightarrow> eq \<in> set (u ! i) \<Longrightarrow> eq \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! i)"
    for eq i 
    using assms in_set_Cons_use_list by fast
  then have "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! rep_of l c\<^sub>1) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                   (ba \<approx> c) \<in> Congruence_Closure
                    (cc_list_set
                      (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>) \<union>
                     pending_set pe))) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! rep_of l c\<^sub>2) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                    (ba \<approx> c) \<in> Congruence_Closure
                    (cc_list_set
                      (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>) \<union>
                     pending_set pe)
                    ))"
    using "*" unfolding congruence_closure.select_convs 
    by blast
  then show "\<exists>c\<^sub>1 c\<^sub>2 c.
              eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
        lookup = update_lookup t (ufa_union l a b) u1', 
        pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
                (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
        lookup = update_lookup t (ufa_union l a b) u1', 
        pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
                (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)" 
    unfolding congruence_closure.select_convs by blast
qed

lemma F_in_set_imp_valid:
  assumes "(F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set xs" 
    "\<forall>j<length xs. use_list_valid_element (xs ! j) (ufa_union l a b) rep_b'"
  shows "b\<^sub>1 < length l" "b\<^sub>2 < length l" "ba < length l" 
proof-
  obtain j where "j < length xs" "(F b\<^sub>1 b\<^sub>2 \<approx> ba) = xs ! j" 
    using assms(1) by (metis in_set_conv_nth)
  then show "b\<^sub>1 < length l" "b\<^sub>2 < length l" "ba < length l" 
    using assms(2) by (metis equation.inject(2) length_list_update)+
qed

lemma use_list_invar2_loop1:
  assumes "ufa_invar l" "a < length l" "b < length l" 
    "use_list_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
     (u1' # urest')"
    (is "use_list_invar2' ?base (u1' # urest')")
    "rep_of l a \<noteq> rep_of l b"
    "lookup_Some t (ufa_union l a b) u1'"
    "u1' = (F d\<^sub>1 d\<^sub>2 \<approx> d)" "d\<^sub>1 < length l" "d\<^sub>2 < length l" 
    "\<forall>j<length (u1' # urest').
       use_list_valid_element ((u1' # urest') ! j) (ufa_union l a b) rep_b'"
  shows "use_list_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
        pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr> urest'"
    (is "use_list_invar2' ?loop1 urest'")
  unfolding use_list_invar2'_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard)
  have ufa_invar_mini_step: "ufa_invar (ufa_union l a b)" 
    by (simp add: assms(1,2,3) ufa_union_invar)
  have **: "({(aa \<approx> rep_of (ufa_union l a b) aa) |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe)) =
(cc_list_set (cc_list ?loop1) \<union> pending_set pe) \<union> pending_set ([link_to_lookup t (ufa_union l a b) u1'])"
    unfolding congruence_closure.select_convs 
    by auto
  then have CC_loop1: "Congruence_Closure
                (cc_list_set (cc_list ?base) \<union> pending_set pe) 
              \<subseteq> Congruence_Closure
                    (cc_list_set (cc_list ?loop1) \<union>
                 pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))" 
    using Congruence_Closure_union unfolding ** congruence_closure.select_convs 
    by fast 
  fix a' c\<^sub>1 c\<^sub>2 c
  assume prems: "a' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u ! a')" 
  from prems have *: "l ! a' = a'" "a' < length l" 
    using assms(1-3) ufa_union_root apply blast
    using prems by auto
  with prems assms have "a' \<noteq> rep_of l a"
    by (metis nth_list_update_eq)+
  with assms * prems obtain b\<^sub>1 b\<^sub>2 ba where lookup: 
    "lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            (cc_list_set (cc_list ?base) \<union> pending_set pe)
             \<or>
           ((F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u1' # urest')
 \<and> rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2\<and>
           (ba \<approx> c) \<in> Congruence_Closure
            (cc_list_set (cc_list ?base) \<union> pending_set pe)
            )" 
    unfolding use_list_invar2'_def congruence_closure.select_convs
    by blast
  from use_list_invar_less_n_in_set assms(9) have c_length: "c\<^sub>1 < length l" "c\<^sub>2 < length l" 
    by (metis assms(4) length_list_update prems(1) prems(2) prems(3))+
  have ***: "rep_of (ufa_union l a b) c\<^sub>1 < length (ufa_union l a b)" 
    "rep_of (ufa_union l a b) c\<^sub>2 < length (ufa_union l a b)"
    "l ! rep_of (ufa_union l a b) c\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
    "l ! rep_of (ufa_union l a b) c\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    using c_length assms(1,2,3) length_list_update rep_of_bound ufa_invar_mini_step rep_of_min ufa_union_aux by auto
  with assms * use_list_invar_less_n_in_set lookup
    prems * lookup_invar_less_n length_list_update
  have b_length: "b\<^sub>1 < length l \<and> b\<^sub>2 < length l \<and> ba < length l" 
  proof(cases "(F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u1' # urest')")
    case True
    then have  "ba < length l" using assms(12) F_in_set_imp_valid(3)[OF True assms(12)]
      by blast
    then show ?thesis using assms(12) F_in_set_imp_valid(1,2) True  
      by blast
  next
    case False
    then have "lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba)"
      using lookup by blast
    with *** show ?thesis using assms(5) lookup_invar_less_n 
      by (smt (verit, ccfv_SIG) c_length length_list_update rep_of_min ufa_invar_mini_step)
  qed 
  from lookup show "(\<exists>b\<^sub>1 b\<^sub>2 ba.
          lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<and>
          (ba \<approx> c) \<in> Congruence_Closure
           ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
             aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
            pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))
            \<or>
          ((F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set urest' \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2) \<and>
          (ba \<approx> c) \<in> Congruence_Closure
           ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
             aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
            pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))
           )"
  proof
    assume "lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<and>
    (ba \<approx> c) \<in> Congruence_Closure
     (cc_list_set (cc_list ?base) \<union> pending_set pe)"
    then show ?thesis
      using CC_loop1 by force
  next
    assume *: "(F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u1' # urest') \<and>
    rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
    rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
    (ba \<approx> c) \<in> Congruence_Closure
     (cc_list_set (cc_list ?base) \<union> pending_set pe)"
    then show ?thesis proof(cases "(F b\<^sub>1 b\<^sub>2 \<approx> ba) = u1'")
      case False
      with * have "(F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set urest'" 
        by simp
      then show ?thesis 
        using "*" CC_loop1 unfolding congruence_closure.select_convs 
        by blast
    next
      case True
      from assms(8) have "t ! rep_of (ufa_union l a b) d\<^sub>1 ! rep_of (ufa_union l a b) d\<^sub>2 \<noteq> None"
        by (metis assms(9) is_none_simps(1) lookup_Some.simps(1))
      with assms(5) obtain e\<^sub>1 e\<^sub>2 e where e:
        "t ! rep_of (ufa_union l a b) d\<^sub>1 ! rep_of (ufa_union l a b) d\<^sub>2 =
Some (F e\<^sub>1 e\<^sub>2 \<approx> e)"
        "rep_of (ufa_union l a b) e\<^sub>1 = rep_of (ufa_union l a b) d\<^sub>1"
        "rep_of (ufa_union l a b) e\<^sub>2 = rep_of (ufa_union l a b) d\<^sub>2"
        unfolding lookup_invar_def congruence_closure.select_convs
        using assms(10, 11) length_list_update rep_of_bound rep_of_min ufa_invar_mini_step by metis
      then have "(d \<approx> e) \<in>
         (pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))" 
        unfolding assms(9) by auto     
      then have "(d \<approx> e) \<in> Congruence_Closure
        (cc_list_set (cc_list ?loop1) \<union>
         pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))" 
        using Congruence_Closure_split_rule by blast
      then have e_d: "(e \<approx> d) \<in> Congruence_Closure
        (cc_list_set (cc_list ?loop1) \<union>
         pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))" 
        using Congruence_Closure.symmetric by blast
      from * CC_loop1 Congruence_Closure_monotonic have "(ba \<approx> c) \<in> Congruence_Closure
     (cc_list_set (cc_list ?loop1) \<union>
         pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))"
        unfolding congruence_closure.select_convs pending_set_Cons[of _ pe] by auto
      then have "(e \<approx> c) \<in> Congruence_Closure
        (cc_list_set (cc_list ?loop1) \<union>
         pending_set (link_to_lookup t (ufa_union l a b) u1' # pe))" 
        using e_d * unfolding congruence_closure.select_convs using True assms(9) by blast
      then show ?thesis unfolding congruence_closure.select_convs
        by (metis (no_types, lifting) "*" True assms(9) e(1) equation.inject(2))
    qed
  qed
qed

lemma use_list_invar2_loop2:
  assumes "ufa_invar l" 
    "a < length l" "b < length l" 
    "use_list_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
     (u1' # urest')"
    (is "use_list_invar2' ?base (u1' # urest')")
    "rep_of l a \<noteq> rep_of l b"
    "\<not> lookup_Some t (ufa_union l a b) u1'"
    "u1' = (F d\<^sub>1 d\<^sub>2 \<approx> d)" "d\<^sub>1 < length l" "d\<^sub>2 < length l"  "d < length l"
    "length l = length t"
    "rep_b' < length u"
    "rep_b' = rep_of l b"
    "\<forall>j<length (u1' # urest'). use_list_valid_element ((u1' # urest') ! j) (ufa_union l a b) rep_b'"
  shows "use_list_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr> urest'"
    (is "use_list_invar2' ?loop2 urest'")
  unfolding use_list_invar2'_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard)
  have ufa_invar_mini_step: "ufa_invar (ufa_union l a b)" 
    by (simp add: assms(1,2,3) ufa_union_invar)
  fix a' c c\<^sub>1 c\<^sub>2
  assume prems: "a' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! a')" 
  from prems have *: "l ! a' = a'" "a' < length l" 
    using assms(1-3) ufa_union_root apply blast+
    using prems by auto
  with prems assms have "a' \<noteq> rep_of l a"
    by (metis nth_list_update_eq)
  show "(\<exists>b\<^sub>1 b\<^sub>2 ba.
          lookup_entry (update_lookup t (ufa_union l a b) u1')
           (ufa_union l a b) c\<^sub>1 c\<^sub>2 =
          Some (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<and>
          (ba \<approx> c) \<in> Congruence_Closure
           ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
             aa < length (ufa_union l a b) \<and>
             ufa_union l a b ! aa \<noteq> aa} \<union>
            pending_set pe)
            \<or>
          ((F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set urest' \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 =
           rep_of (ufa_union l a b) c\<^sub>2) \<and>
          (ba \<approx> c) \<in> Congruence_Closure
           ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
             aa < length (ufa_union l a b) \<and>
             ufa_union l a b ! aa \<noteq> aa} \<union>
            pending_set pe))"
  proof(cases "u1' = F c\<^sub>1 c\<^sub>2 \<approx> c")
    case True
      \<comment> \<open>u1' is now in the lookup table, after the update.\<close>
    with assms have "lookup_entry (update_lookup t (ufa_union l a b) u1')
        (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some u1'" unfolding True update_lookup.simps
      by (metis True congruence_closure.select_convs(3) equation.inject(2) length_list_update lookup_invar_def nth_list_update_eq rep_of_less_length_l ufa_invar_mini_step)
    then show ?thesis 
      using Congruence_Closure.reflexive True by blast
  next
    case False
      \<comment> \<open>u1' was already in the lookup table before the update.\<close>
    then have  "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u ! a')"
      by (metis assms(14) nth_list_update_eq nth_list_update_neq prems(3) set_ConsD)
    with assms obtain b\<^sub>1 b\<^sub>2 ba where 
      "lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2 =
           Some (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
              aa < length (ufa_union l a b) \<and>
              ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set pe)
             \<or>
           ((F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u1' # urest') \<and>
            rep_of (ufa_union l a b) b\<^sub>1 =
            rep_of (ufa_union l a b) c\<^sub>1 \<and>
            rep_of (ufa_union l a b) b\<^sub>2 =
            rep_of (ufa_union l a b) c\<^sub>2) \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
              aa < length (ufa_union l a b) \<and>
              ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set pe)" 
      unfolding use_list_invar2'_def congruence_closure.select_convs
      using prems by blast
    then show ?thesis 
    proof
      assume prems2: "lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<and>
    (ba \<approx> c) \<in> Congruence_Closure
     ({aa \<approx> rep_of (ufa_union l a b) aa | aa.
       aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
      pending_set pe)"
      then have "lookup_entry (update_lookup t (ufa_union l a b) u1') 
          (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba)" 
        using assms(8) assms(9) update_lookup_unchanged' by auto
      then show ?thesis 
        using prems2 by blast
    next
      assume prems2: "((F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u1' # urest') \<and>
     rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
     rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2) \<and>
    (ba \<approx> c) \<in> Congruence_Closure
     ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
       aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
      pending_set pe)"    
      then show ?thesis proof(cases "u1' = (F b\<^sub>1 b\<^sub>2 \<approx> ba)")
        case True
        have "rep_of (ufa_union l a b) b\<^sub>1 < length t" 
          "rep_of (ufa_union l a b) b\<^sub>2 < length (t ! rep_of (ufa_union l a b) b\<^sub>1)"
          "rep_of (ufa_union l a b) b\<^sub>1 < length l" 
          "rep_of (ufa_union l a b) b\<^sub>2 < length l"
          using assms unfolding lookup_invar_def congruence_closure.select_convs
          by (metis True equation.inject(2) length_list_update rep_of_bound ufa_invar_mini_step)+
        then have "lookup_entry (update_lookup t (ufa_union l a b) u1')
        (ufa_union l a b) b\<^sub>1 b\<^sub>2 = Some u1'" 
          unfolding True update_lookup.simps by simp
        then show ?thesis 
          using prems2 by auto
      next
        case False
        with prems2 have "(F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set urest'"
          by simp
        then show ?thesis 
          using prems2 by blast
      qed
    qed
  qed
qed

paragraph \<open>Invariants after the entire loop\<close>

lemma lookup_invar_loop: 
  assumes "ufa_invar l"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar ?base") 
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "length t = length l" "length u = length l" 
    "(\<forall> j < length u_a . use_list_valid_element (u_a ! j) l rep_b)"
    "rep_b < length l"
  shows "lookup_invar (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
)" 
  using assms proof(induction rep_b u_a 
    "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
  case (1 rep_b' u1' urest' l' u' t' pe' pf' pfl' ip')
  from "1.prems" have *: "\<forall>j<length urest'. use_list_valid_element (urest' ! j) l rep_b'" 
    by auto
  then show ?case proof(cases "lookup_Some t' l' u1'")
    case True
    with 1 have lookup_invar: "lookup_invar \<lparr>cc_list = l', use_list = u', lookup = t', 
pending = link_to_lookup t' l' u1' # pe', proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      unfolding lookup_invar_def by auto
    from 1 have use_list_invar: "use_list_invar \<lparr>cc_list = l', use_list = u', lookup = t', 
pending = link_to_lookup t' l' u1' # pe', proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      unfolding use_list_invar_def by auto
    with 1 show ?thesis 
      using True * lookup_invar use_list_invar by auto
  next
    case False
    with "1.prems" obtain a\<^sub>1 a\<^sub>2 aa where u1': "u1' = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
      "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l" "rep_of l a\<^sub>1 = rep_b' \<or> rep_of l a\<^sub>2 = rep_b'"
      by (metis in_set_conv_nth list.set_intros(1))
    from 1 have lookup_invar: "lookup_invar \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'], lookup = update_lookup t' l' u1',
             pending = pe', proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      using lookup_invar_loop2 by auto
    from 1 use_list_invar_loop2 u1' have use_list_invar: "use_list_invar \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'], lookup = update_lookup t' l' u1',
             pending = pe', proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      using congruence_closure.ext_inject by auto
    with 1 show ?thesis 
      using False * lookup_invar use_list_invar
      by (simp add: u1'(1))
  qed
qed simp

lemma pending_invar_loop:
  assumes "ufa_invar l"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "length t = length l" "length u = length l"
    "(\<forall> j < length u_a . use_list_valid_element (u_a ! j) l rep_b)"
    "rep_b < length l"
  shows "pending_invar (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)" 
  using assms proof(induction rep_b u_a 
    "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    arbitrary: l u t pe pf pfl ip  rule: propagate_loop.induct)
  case (1 rep_b' u1' urest' l' u' t' pe' pf' pfl' ip')
  from "1.prems" obtain a\<^sub>1 a\<^sub>2 aa where u1': "u1' = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l" "rep_of l a\<^sub>1 = rep_b' \<or> rep_of l a\<^sub>2 = rep_b'"
    by (metis in_set_conv_nth list.set_intros(1))
  from 1 have *: "\<forall>j<length urest'. use_list_valid_element (urest' ! j) l' rep_b'" 
    by auto
  show ?case proof(cases "lookup_Some t' l' u1'")
    case True
    with 1 u1' pending_invar_loop1 have pending_invar: "pending_invar \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>" 
      by (metis congruence_closure.ext_inject)
    from 1 have lookup_invar: "lookup_invar \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>" unfolding lookup_invar_def 
      by auto
    from 1 have use_list_invar: "use_list_invar \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>" unfolding use_list_invar_def 
      by auto
    with True pending_invar lookup_invar use_list_invar * show ?thesis using 1 
      by simp
  next
    case False
    from 1 have pending_invar: "pending_invar \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'], lookup = update_lookup t' l' u1', pending = pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      unfolding pending_invar_def by fastforce
    from 1 lookup_invar_loop2 u1' have lookup_invar: "lookup_invar \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'], lookup = update_lookup t' l' u1', pending = pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      by (metis congruence_closure.ext_inject)
    from 1 use_list_invar_loop2 u1' have use_list_invar: "use_list_invar \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'], lookup = update_lookup t' l' u1', pending = pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      by (metis congruence_closure.ext_inject)
    with False pending_invar * show ?thesis using 1 
      using congruence_closure.ext_inject length_list_update lookup_invar propagate_loop.simps(1) u1'(1) update_lookup.simps(1) use_list_invar 
      by auto
  qed
qed simp


lemma use_list_invar_loop:
  assumes "ufa_invar l" 
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar ?base") 
    "length u = length l"
    "(\<forall> j < length u_a . use_list_valid_element (u_a ! j) l rep_b)"
    "rep_b < length l"
  shows "use_list_invar (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
)" 
  using assms proof(induction rep_b u_a 
    "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    arbitrary: l u t pe pf pfl ip  rule: propagate_loop.induct)
  case (1 rep_b' u1' urest' l' u' t' pe' pf' pfl' ip')
  from "1.prems" obtain a\<^sub>1 a\<^sub>2 aa where u1': "u1' = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l" "rep_of l a\<^sub>1 = rep_b' \<or> rep_of l a\<^sub>2 = rep_b'"
    by (metis in_set_conv_nth list.set_intros(1))
  from 1 have *: "\<forall>j<length urest'. use_list_valid_element (urest' ! j) l' rep_b'" 
    by auto
  show ?case proof(cases "lookup_Some t' l' u1'")
    case True
    from 1 have "use_list_invar \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>" unfolding use_list_invar_def 
      by simp
    with 1 show ?thesis 
      using "*" True by auto
  next
    case False
    from 1 u1' use_list_invar_loop2 have "use_list_invar \<lparr>cc_list = l', 
use_list = u'[rep_b' := u1' # u' ! rep_b'], lookup = update_lookup t' l' u1', pending = pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" 
      by (metis congruence_closure.ext_inject)
    with 1 show ?thesis 
      using "*" False by force
  qed
qed simp

lemma lookup_invar2_loop:
  assumes 
    "ufa_invar l" "a < length l" "b < length l"
    "rep_of l a \<noteq> rep_of l b"
    "lookup_invar2 \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr>"

"\<forall> eq' \<in> set u_a . 
(\<exists> c\<^sub>1 c\<^sub>2 c . eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and> c\<^sub>1 < length l \<and> c\<^sub>2 < length l \<and> c < length l
\<and> (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c)

\<and> 
(rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)
)"
"(\<forall> j < length u_a . use_list_valid_element (u_a ! j) (ufa_union l a b) rep_b)"

"rep_b < length l"
"use_list_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr>"
"lookup_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr>"
"length u = length l"
"length l = length t"
"rep_b = rep_of l b"
"(\<forall> j < length u_a . use_list_valid_element (u_a ! j) l (rep_of l a))"
shows "lookup_invar2 (propagate_loop rep_b u_a 
\<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr>)"
  using assms proof(induction rep_b u_a 
    "\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    arbitrary: u t pe rule: propagate_loop.induct)
  case (1 rep_b' u1' urest' l' u' t' pe' pf' pfl' ip')
  from 1(9) obtain c\<^sub>1 c\<^sub>2 c where u1': "u1' = (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>2 < length (ufa_union l a b)" "c < length (ufa_union l a b)" 
    "rep_of (ufa_union l a b) c\<^sub>1 = rep_b' \<or> rep_of (ufa_union l a b) c\<^sub>2 = rep_b'"
    by auto
  then have c_length: "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l" 
    using length_list_update 1(2) by simp_all
  from 1(2) have eq: "l' = ufa_union l a b" "t = t'" "pe = pe'" by simp_all
  show ?case proof(cases "lookup_entry t' l' c\<^sub>1 c\<^sub>2")
    case None
    let ?loop2 = "\<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t l' u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>"

    from None u1' eq have lookup_None: "\<not> lookup_Some t (ufa_union l a b) u1'" 
      by fastforce
    from 1(8) u1' have *: "(rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
     contains_similar_equation
      \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
         pf_labels = pfl, input = ip\<rparr>
      (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
    (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
     contains_similar_equation
      \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
         pf_labels = pfl, input = ip\<rparr>
      (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)" 
      by simp
    from 1(16) obtain k\<^sub>1 k\<^sub>2 k where u1'': "u1' = (F k\<^sub>1 k\<^sub>2 \<approx> k)"
      "k\<^sub>1 < length l" "k\<^sub>2 < length l" "k < length l" 
      "rep_of l k\<^sub>1 = rep_of l a \<or> rep_of l k\<^sub>2 = rep_of l a"
      by auto
    have "rep_b' < length u" " rep_b' = rep_of l b"
      "rep_of l a = rep_of l c\<^sub>1 \<or> rep_of l a = rep_of l c\<^sub>2"
        apply (simp add: "1.prems"(11) "1.prems"(8))
       apply (simp add: "1.prems"(13))
      using u1'' 
      using u1'(1) by force
    with lookup_invar2_loop2 assms(1-4) 1(10-14,7) lookup_None u1'(1) c_length * eq have 
      2: "lookup_invar2 ?loop2" by blast
    have *: "ufa_invar (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)"
      by (simp_all add: c_length assms(1) assms(2) assms(3) ufa_union_invar)
    from lookup_invar2_prems_loop2[OF 1(8)] eq have 6: "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop2
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop2
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)"
      using 1(14,10) "1.prems"(11) by simp
    from 1(9) have 3:"\<forall>j<length urest'. use_list_valid_element (urest' ! j) (ufa_union l a b) rep_b'"
      by auto
    have "rep_b' < length u" 
      by (simp add: "1.prems"(11) "1.prems"(8))
    then have 4: "use_list_invar ?loop2" "lookup_invar ?loop2" 
      using 1(11) use_list_invar_loop2 u1' 
      using \<open>l' = ufa_union l a b\<close> apply blast
      using 1(12) lookup_invar_loop2 u1' 
      using \<open>l' = ufa_union l a b\<close> by blast
    from lookup_None 1(2) have 5: "(if lookup_Some t' l' u1'
     then \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>
     else \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'],
             lookup = update_lookup t' l' u1', pending = pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>) =
    ?loop2" 
      by auto
    have " \<forall>j<length urest'. use_list_valid_element (urest' ! j) l (rep_of l a) " using 1(16) 
      by auto
    with 1(1)[OF 5(1) assms(1,2,3,4) 2 6 3 1(10) 4] "1.prems"(11,12) eq(1) lookup_None u1'(1) length_list_update
    show ?thesis 
      by (simp add: "1.prems"(13))
  next
    case (Some k)
    let ?loop1 = "\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, 
pending = link_to_lookup t' l' u1' # pe', proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>"
    from Some u1' eq have lookup_Some: "lookup_Some t (ufa_union l a b) u1'" 
      by fastforce
    thm lookup_invar2_loop1
    with lookup_invar2_loop1 assms(1,2,3) 1(11,12,7) 1 u1' have 
      2: "lookup_invar2 ?loop1" using c_length eq  
      by (metis (no_types, lifting))
    have *: "ufa_invar (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>2 < length (ufa_union l a b)"
      by (simp_all add: c_length assms(1) assms(2) assms(3) ufa_union_invar)
    with lookup_invar2_prems_loop1 1(8)   have 6: "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop1
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop1
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)"
      using eq by fast
    from 1(9) have 3:"\<forall>j<length urest'. use_list_valid_element (urest' ! j) (ufa_union l a b) rep_b'"
      by auto
    have 4: "use_list_invar ?loop1" "lookup_invar ?loop1" 
      using 1(11) unfolding use_list_invar_def apply simp
      using 1(12) unfolding lookup_invar_def by simp
    from lookup_Some 1(2) have 5: "(if lookup_Some t' l' u1'
     then \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>
     else \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'],
             lookup = update_lookup t' l' u1', pending = pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>) =
    ?loop1" 
      by auto
    have "\<forall>j<length urest'. use_list_valid_element (urest' ! j) l (rep_of l a) " using 1(16) 
      by auto
    with 1(1)[OF 5(1) assms(1,2,3,4) 2 6 3] 1(2-) 2 3 4 lookup_Some show ?thesis 
      by auto
  qed
qed simp

lemma use_list_invar2_loop:
  assumes 
    "ufa_invar l" "a < length l" "b < length l"
    "rep_of l a \<noteq> rep_of l b"
    "use_list_invar2' \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> u_a"

"(\<forall> j < length u_a . use_list_valid_element (u_a ! j) (ufa_union l a b) rep_b)"

"rep_b < length l"
"use_list_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr>"
"lookup_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr>"
"length u = length l"
"length l = length t"
"rep_b = rep_of l b"
"(\<forall> j < length u_a . use_list_valid_element (u_a ! j) l (rep_of l a))"

shows "use_list_invar2 (propagate_loop rep_b u_a 
\<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr>)"
  using assms proof(induction rep_b u_a 
    "\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    arbitrary: u t pe rule: propagate_loop.induct)
  case (1 rep_b' u1' urest' l' u' t' pe' pf' pfl' ip')
  from 1(8) obtain c\<^sub>1 c\<^sub>2 c where u1': "u1' = (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>2 < length (ufa_union l a b)" "c < length (ufa_union l a b)" 
    "rep_of (ufa_union l a b) c\<^sub>1 = rep_b' \<or> rep_of (ufa_union l a b) c\<^sub>2 = rep_b'"
    by auto
  then have c_length: "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l" 
    using length_list_update 1(2) by simp_all
  from 1(2) have eq: "l' = ufa_union l a b" "t = t'" "pe = pe'" by simp_all
  show ?case proof(cases "lookup_entry t' l' c\<^sub>1 c\<^sub>2")
    case None
    let ?loop2 = "\<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t l' u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>"
    from None u1' eq have lookup_None: "\<not> lookup_Some t (ufa_union l a b) u1'" 
      by fastforce
    from 1(15) obtain k\<^sub>1 k\<^sub>2 k where u1'': "u1' = (F k\<^sub>1 k\<^sub>2 \<approx> k)"
      "k\<^sub>1 < length l" "k\<^sub>2 < length l" "k < length l" 
      "rep_of l k\<^sub>1 = rep_of l a \<or> rep_of l k\<^sub>2 = rep_of l a"
      by auto
    have "rep_b' < length u" "rep_b' = rep_of l b"
      "rep_of l a = rep_of l c\<^sub>1 \<or> rep_of l a = rep_of l c\<^sub>2"
        apply (auto simp add: "1.prems"(10,11,12,7) u1'' u1')
      using "1.prems"(11) "1.prems"(12) "1.prems"(7) apply auto[1]
      using "1.prems"(11) "1.prems"(12) "1.prems"(7) apply auto[1]
      apply (simp add: "1.prems"(12))
      using u1'' u1'(1) by force
    with use_list_invar2_loop2[OF "1.prems"(1,2,3,8,9,5,4) lookup_None u1'(1) c_length
        "1.prems"(11) _ "1.prems"(12,6)] 1(10,13) eq have 
      2: "use_list_invar2' ?loop2 urest'"  
      by blast
    have *: "ufa_invar (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)"
      by (simp_all add: c_length assms(1) assms(2) assms(3) ufa_union_invar)
    from 1(8) have 3:"\<forall>j<length urest'. use_list_valid_element (urest' ! j) (ufa_union l a b) rep_b'"
      by auto
    have "rep_b' < length u" 
      by (simp add: "1.prems"(10) "1.prems"(7))
    then have 4: "use_list_invar ?loop2" "lookup_invar ?loop2" 
      using 1(10) use_list_invar_loop2 u1' 
      using \<open>l' = ufa_union l a b\<close> apply blast
      using 1(11) lookup_invar_loop2 u1' 
      using \<open>l' = ufa_union l a b\<close> by blast
    from lookup_None 1(2) have 5: "(if lookup_Some t' l' u1'
     then \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>
     else \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'],
             lookup = update_lookup t' l' u1', pending = pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>) =
    ?loop2" 
      by auto
    have " \<forall>j<length urest'. use_list_valid_element (urest' ! j) l (rep_of l a) " using 1(15) 
      by auto
    with 1(1)[OF 5(1) assms(1,2,3,4) 2 3 1(9) 4] "1.prems"(11,12) eq(1) lookup_None u1'(1) 
      length_list_update 
    show ?thesis 
      by (simp add: "1.prems"(10))
  next
    case (Some k)
    let ?loop1 = "\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, 
pending = link_to_lookup t' l' u1' # pe', proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>"

    from Some u1' eq have lookup_Some: "lookup_Some t (ufa_union l a b) u1'" 
      by fastforce
    with use_list_invar2_loop1[OF "1.prems"(1,2,3,8,9,5) ] 1 u1' have 
      2: "use_list_invar2' ?loop1 urest'" using c_length 
      by blast
    have *: "ufa_invar (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>2 < length (ufa_union l a b)"
      by (simp_all add: c_length assms(1) assms(2) assms(3) ufa_union_invar)
    from 1(8) have 3: "\<forall>j<length urest'. use_list_valid_element (urest' ! j) (ufa_union l a b) rep_b'"
      by auto
    have 4: "use_list_invar ?loop1" "lookup_invar ?loop1" 
      using 1(10) unfolding use_list_invar_def apply simp
      using 1(11) unfolding lookup_invar_def by simp
    from lookup_Some 1(2) have 5: "(if lookup_Some t' l' u1'
     then \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe',
             proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>
     else \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'],
             lookup = update_lookup t' l' u1', pending = pe', proof_forest = pf',
             pf_labels = pfl', input = ip'\<rparr>) =
    ?loop1" 
      by auto
    have "\<forall>j<length urest'. use_list_valid_element (urest' ! j) l (rep_of l a) " 
      using 1(15) by auto
    with 1(1)[OF 5(1) assms(1,2,3,4) 2 3] 1(2-) 2 3 4 assms(4) lookup_Some 
    show ?thesis 
      by auto
  qed
qed simp

lemma correctness_invar_loop:
  assumes "a < length (cc_list cc)" "b < length (cc_list cc)" 
    "lookup_invar cc"
    "use_list_invar cc"
    "cc_list_invar cc"
    "length (use_list cc) = length (cc_list cc)"
    "length (lookup cc) = length (cc_list cc)"
    "(\<forall> j < length u_a . use_list_valid_element (u_a ! j) (cc_list cc) rep_b)"
    "rep_b < length (cc_list cc)"
    "rep_b = rep_of l b"
  shows 
    "Congruence_Closure (representativeE cc \<union> pending_set (pending cc) \<union> set u_a) 
= Congruence_Closure (representativeE ((propagate_loop rep_b u_a cc)) 
\<union> pending_set (pending (propagate_loop rep_b u_a cc)))" 
  using assms proof(induction rep_b u_a cc rule: propagate_loop.induct)
  case (1 rep_b' u1' urest' l' u' t' pe' pf' pfl' ip')
  from "1.prems" obtain a\<^sub>1 a\<^sub>2 aa where u1': "u1' = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l'" "a\<^sub>2 < length l'" "aa < length l'" "rep_of l' a\<^sub>1 = rep_b' \<or> rep_of l' a\<^sub>2 = rep_b'"
    unfolding congruence_closure.select_convs
    by (metis in_set_conv_nth list.set_intros(1))
  from 1 have *: "\<forall>j<length urest'. use_list_valid_element (urest' ! j) l' rep_b'" 
    by auto
  let ?loop1 = "\<lparr>cc_list = l', use_list = u', lookup = t',
                 pending = link_to_lookup t' l' u1' # pe', proof_forest = pf',
                 pf_labels = pfl', input = ip'\<rparr>"
  let ?loop2 = "\<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'],
                lookup = update_lookup t' l' u1', pending = pe',
                proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>"
  let ?step = "if lookup_Some t' l' u1'
        then ?loop1
        else ?loop2"
  show ?case proof(cases "lookup_Some t' l' u1'")
    case True
    then have invars: "use_list_invar ?loop1" "lookup_invar ?loop1" 
      using "1.prems"(3,4) use_list_invar_def lookup_invar_def by auto
    then have **: "Congruence_Closure (representativeE ?step \<union>
      pending_set (pending ?step) \<union> set urest') =
    Congruence_Closure (representativeE (propagate_loop rep_b' urest'
         ?step) \<union> pending_set (pending (propagate_loop rep_b' urest'
           ?step)))" using True 1 *  
      unfolding congruence_closure.select_convs cc_list_invar_def by simp
    from invars u1' "1.prems" correctness_invar_loop1 True 
    have "Congruence_Closure (representativeE ?step \<union>
      pending_set (pending ?step) \<union> set urest')
= Congruence_Closure
     (representativeE
       \<lparr>cc_list = l', use_list = u', lookup = t', pending = pe', proof_forest = pf',
          pf_labels = pfl', input = ip'\<rparr> \<union>
      pending_set
       (pending
         \<lparr>cc_list = l', use_list = u', lookup = t', pending = pe', proof_forest = pf',
            pf_labels = pfl', input = ip'\<rparr>) \<union>
      set (u1' # urest'))" 
      unfolding cc_list_invar_def by simp
    then show ?thesis using ** unfolding propagate_loop.simps 
      by argo
  next
    case False
    have invars: "lookup_invar ?loop2" "use_list_invar ?loop2" 
      using "1.prems"(3,4) lookup_invar_loop2 u1' 
       apply blast using "1.prems" use_list_invar_loop2 u1' by force
    with 1 have **: "Congruence_Closure
     (representativeE ?loop2 \<union> pending_set (pending ?loop2) \<union>
      set urest') = Congruence_Closure (representativeE
       (propagate_loop rep_b' urest' ?loop2) \<union> pending_set
       (pending (propagate_loop rep_b' urest' ?loop2)))" 
      using * False unfolding cc_list_invar_def by force
    from "1.prems" correctness_invar_loop2 u1' False have "Congruence_Closure
     (representativeE ?loop2 \<union> pending_set (pending ?loop2) \<union>
      set urest') = Congruence_Closure
     (representativeE
       \<lparr>cc_list = l', use_list = u', lookup = t', pending = pe', proof_forest = pf', pf_labels = pfl',
          input = ip'\<rparr> \<union>
      pending_set
       (pending
         \<lparr>cc_list = l', use_list = u', lookup = t', pending = pe', proof_forest = pf',
            pf_labels = pfl', input = ip'\<rparr>) \<union>
      set (u1' # urest'))" unfolding congruence_closure.select_convs cc_list_invar_def 
      by presburger
    then show ?thesis using ** 
      using False propagate_loop.simps(1) by presburger
  qed
qed simp

lemma same_length_invar_loop: 
  assumes 
    "same_length_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr> (length l)"
    (is "same_length_invar ?base (length l)") 
  shows "same_length_invar (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
) (nr_vars ((propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)))" 
  using assms proof(induction rep_b u_a 
    "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
  case (1 rep_b' u1' urest' l' u' t' pe' pf' pfl' ip')
  then show ?case proof(cases "lookup_Some t' l' u1'")
    case True
    have "same_length_invar \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe',
                 proof_forest = pf', pf_labels = pfl', input = ip'\<rparr> (length l')"
      using "1.hyps"(2) "1.prems" unfolding same_length_invar_def by auto
    then show ?thesis 
      using "1.hyps"(1,2) "1.prems"(1) True by auto
  next
    case False
    have "same_length_invar \<lparr>cc_list = l', use_list = u'[rep_b' := u1' # u' ! rep_b'], 
lookup = update_lookup t' l' u1',
             pending = pe', proof_forest = pf', pf_labels = pfl', input = ip'\<rparr> (length l')"
      using 1(2) "1.prems" update_lookup_preserves_length unfolding same_length_invar_def by auto
    then show ?thesis 
      using "1.hyps"(1,2) "1.prems"(1) False by auto
  qed
qed simp

lemma cc_list_invar_loop: 
  assumes 
    "cc_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_list_invar ?base") 
  shows "cc_list_invar (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)" 
  using assms apply(induction rep_b u_a 
      "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
  unfolding cc_list_invar_def by auto

lemma pf_labels_invar_loop: 
  "pf_labels (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)
= pfl" 
  apply(induction rep_b u_a 
      "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
  by auto

lemma proof_forest_loop: 
  "proof_forest (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)
= pf" 
  apply(induction rep_b u_a 
      "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
  by auto

lemma cc_list_loop: 
  "cc_list (propagate_loop rep_b u_a 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)
= l"
  apply(induction rep_b u_a 
      "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
  by auto

subsection \<open>The invariants remain invariant after propagate\<close>

paragraph \<open>Invariants before entering the \<open>propagate_loop\<close>\<close>

lemma lookup_invar_mini_step:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar ?base") "ufa_invar l" "a < length l" "b < length l"
  shows "lookup_invar \<lparr>cc_list = ufa_union l a b,
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>" (is "lookup_invar ?step")  
  unfolding lookup_invar_def
proof(standard, standard, standard, standard, standard, standard)
  fix i j
  assume i_j: "i < nr_vars ?step" "j < nr_vars ?step"
    "cc_list ?step ! i = i \<and> cc_list ?step ! j = j"
  then have "cc_list ?base ! i = i \<and> cc_list ?base ! j = j" "i < nr_vars ?base" "j < nr_vars ?base"
      apply (metis assms(2) assms(3) assms(4) congruence_closure.select_convs(1) ufa_union_root)
    using i_j by auto
  with assms(1) have "lookup_valid_element (lookup ?base) (cc_list ?base) i j"
    unfolding lookup_invar_def congruence_closure.select_convs by blast
  with assms i_j show "lookup_valid_element (lookup ?step) (cc_list ?step) i j"
    unfolding lookup_invar_def congruence_closure.select_convs
    by (metis length_list_update list_update_same_conv nth_list_update rep_of_fun_upd' rep_of_refl rep_of_root)
next
  show "quadratic_table (lookup ?step)"
    using assms lookup_invar_def by auto
qed


lemma use_list_invar_mini_step:
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar ?base") "ufa_invar l" "a < length l" "b < length l" "length l = length u"
  shows "use_list_invar \<lparr>cc_list = ufa_union l a b,
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>" (is "use_list_invar ?step")  
  unfolding use_list_invar_def
proof(standard, standard, standard, standard, standard)
  fix i j
  assume i_j: "i < nr_vars ?step" "j < length (use_list ?step ! i)" "cc_list ?step ! i = i"
  then have "cc_list ?base ! i = i" 
    by (metis assms(2) assms(3) assms(4) congruence_closure.select_convs(1) ufa_union_root)
  have "rep_of l a < length u" 
    by (metis assms(2) assms(3) assms(5) rep_of_bound)
  then show "use_list_valid_element (use_list ?step ! i ! j) (cc_list ?step) i"
  proof(cases "i = rep_of l a")
    case True
    then have "length (use_list ?step ! i) = 0" 
      by (simp add: \<open>rep_of l a < length u\<close>)
    then show ?thesis 
      using i_j(2) by presburger
  next
    case False
    then have "(use_list ?step ! i) = (use_list ?base ! i)" 
      by fastforce
    with assms show ?thesis unfolding use_list_invar_def 
      by (metis \<open>cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr> ! i = i\<close> congruence_closure.select_convs(1) i_j(1) i_j(2) i_j(3) length_list_update rep_of_iff rep_of_ufa_union_invar ufa_union_invar)
  qed
qed

lemma pending_invar_mini_step:
  assumes "ufa_invar l" "a < length l" "b < length l"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "pending_invar ?base")
  shows"pending_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>" (is "pending_invar ?step") unfolding pending_invar_def
proof(standard, standard)
  fix i
  assume i: "i < length (pending ?step)"
  then have "pending ?base ! (i + 1) = pending ?step ! i"
    unfolding congruence_closure.select_convs by auto
  then have *: "valid_vars_pending (pending ?step ! i) (cc_list ?base)"
    using assms i unfolding pending_invar_def congruence_closure.select_convs by force
  then show "valid_vars_pending (pending ?step ! i) (cc_list ?step)"
  proof(induction rule: valid_vars_pending_cases)
    case (One a b)
    with * show ?case 
      unfolding pending_invar_def congruence_closure.select_convs
      by simp
  next
    case (Two a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b')
    with * have "rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) b\<^sub>1"
      "rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) b\<^sub>2"
      unfolding congruence_closure.select_convs
      by (metis assms(1) assms(2) assms(3) rep_of_ufa_union_invar)+
    with * Two show ?case 
      unfolding pending_invar_def congruence_closure.select_convs
      by simp
  qed
qed

lemma correctness_invar_mini_step1:
  assumes "ufa_invar l" "a < length l" "b < length l"
    "a = left eq2" "b = right eq2"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar2 ?base")
    "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "eq \<in> representativeE
         \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
            proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq2, input = ip\<rparr> \<union>
        pending_set pe \<union>
        set (u ! rep_of l a)"
    (is "eq \<in> (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a)) ")
  shows "eq \<in> Congruence_Closure 
(representativeE 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
\<union> pending_set (eq2 # pe))"
proof-
  from assms(11) consider
    (rep) c where "eq = (c \<approx> rep_of (ufa_union l a b) c)"
    "c < length (ufa_union l a b)" "(ufa_union l a b) ! c \<noteq> c"
    "rep_of l a \<noteq> rep_of l c"
  | (new_rep) c where "eq = (c \<approx> rep_of (ufa_union l a b) c)"
    "c < length (ufa_union l a b)" "(ufa_union l a b) ! c \<noteq> c"
    "rep_of l a = rep_of l c"
  | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of (ufa_union l a b) c" 
    "a' < length (ufa_union l a b)" "b' < length (ufa_union l a b)"
    "c < length (ufa_union l a b)" "(ufa_union l a b) ! a' = a'" 
    "(ufa_union l a b) ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "rep_of l c \<noteq> rep_of l a"
  | (new_lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of (ufa_union l a b) c" 
    "a' < length (ufa_union l a b)" "b' < length (ufa_union l a b)"
    "c < length (ufa_union l a b)" "(ufa_union l a b) ! a' = a'" 
    "(ufa_union l a b) ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "rep_of l c = rep_of l a"
  | (pending) "eq \<in> pending_set pe"
  | (urest) "eq \<in> set (u ! rep_of l a)" 
    unfolding representativeE_def congruence_closure.select_convs 
    by blast
  then show "eq \<in> Congruence_Closure
           (representativeE
             \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq2 # pe, proof_forest = pf,
                pf_labels = pfl, input = ip\<rparr> \<union>
            pending_set (eq2 # pe))" proof(cases)
    case pending
    then show ?thesis 
      by (metis Congruence_Closure_split_rule UnCI pending_set_Cons)
  next
    case rep
    then have "rep_of (ufa_union l a b) c = rep_of l c" "l ! c \<noteq> c"  
      using assms ufa_union_aux rep rep_of_refl by auto
    then show ?thesis 
      using assms base representativeE_def rep by force
  next
    case new_rep
    then have rep_union: "rep_of (ufa_union l a b) c = rep_of l b"
      by (simp add: assms(1) assms(3) ufa_union_aux)
    have "length l = length (ufa_union l a b)" using assms(1) 
      by simp
    then have *: "(c \<approx> (rep_of l c)) \<in> Congruence_Closure (representativeE ?base)"
      "((rep_of l a) \<approx> a) \<in> Congruence_Closure (representativeE ?base)"
      "(b \<approx> (rep_of l b)) \<in> Congruence_Closure (representativeE ?base)" using a_eq_rep_of_a_in_CC new_rep congruence_closure.select_convs(1) assms(2,3)
      by metis+
    from assms have "valid_vars_pending eq2 (cc_list ?base)"
      unfolding pending_invar_def by (metis assms(8) congruence_closure.select_convs(1) pending_invar_Cons)
    with pending_a_b_in_Congruence_Closure' 
    have **: "(a \<approx> b) \<in> Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe))"
      by (simp add: assms(4) assms(5))
    with * Congruence_Closure_split_rule have "(c \<approx> a) \<in>
Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe))" 
      by (metis new_rep(4) transitive1)
    with * ** Congruence_Closure_union have "(c \<approx> b) \<in> 
Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe))" 
      by (metis transitive1)
    with * Congruence_Closure_split_rule rep_union new_rep show ?thesis 
      by (metis transitive1)
  next
    case lookup
    then have *: "l ! a' = a'" "l ! b' = b'" 
      using assms(1) assms(2) assms(3) ufa_union_root by blast+
    have "rep_of (ufa_union l a b) c = rep_of l c" 
      by (metis assms(1,2) length_list_update lookup(4,8) rep_of_fun_upd' rep_of_refl rep_of_root)
    with lookup * have "eq \<in> representativeE ?base" unfolding representativeE_def by force
    then show ?thesis using base by simp
  next
    case new_lookup
    then have *: "l ! a' = a'" "l ! b' = b'" 
      using assms(1) assms(2) assms(3) ufa_union_root by blast+
    have **: "rep_of (ufa_union l a b) c = rep_of l b" 
      by (metis assms(1) assms(3) length_list_update new_lookup(4) new_lookup(8) ufa_union_aux)
    have "rep_of (ufa_union l a b) (rep_of l b) = rep_of (ufa_union l a b) (rep_of l a)"
      by (simp add: assms(1) assms(2) assms(3) rep_of_idem rep_of_less_length_l ufa_union_aux)
    with pending_a_b_in_Congruence_Closure'
    have ***: "(a \<approx> b) \<in> Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe))" 
      using assms(4,5,8) pending_invar_Cons by force
    from assms * new_lookup have F_in_rep: "(F a' b' \<approx> rep_of l c) \<in> (representativeE ?base)" 
      unfolding representativeE_def congruence_closure.select_convs by simp
    have "rep_of l (rep_of l c) = rep_of l a" 
      by (simp add: assms(1) assms(2) new_lookup(8) rep_of_idem)
    then have cc1: "(rep_of l c \<approx> a) \<in> Congruence_Closure (representativeE ?base)" 
      "(b \<approx> rep_of l b) \<in> Congruence_Closure (representativeE ?base)" 
      using CC_same_rep 
       apply (simp add: assms(1) assms(2) new_lookup(8) rep_of_less_length_l)
      by (simp add: CC_same_rep assms(1) assms(3) rep_of_idem rep_of_less_length_l)
    with new_lookup ** CC_rep_of_a_imp_a have "(rep_of l c \<approx> b) \<in> Congruence_Closure
     (representativeE ?base \<union> pending_set (eq2 # pe))" 
      by (meson "***" Congruence_Closure_split_rule transitive1)
    then have "(rep_of l c \<approx> rep_of (ufa_union l a b) c) \<in> Congruence_Closure
     (representativeE ?base \<union> pending_set (eq2 # pe))" 
      by (metis "**" transitive1 Congruence_Closure_split_rule cc1(2))
    then show ?thesis 
      by (metis Congruence_Closure_split_rule F_in_rep base new_lookup(1) transitive2)
  next
    case urest
    have rep_a_valid: "rep_of l a < length l" "l ! (rep_of l a) = rep_of l a"
       apply (simp add: assms(1) assms(2) rep_of_less_length_l)
      by (simp add: assms(1) assms(2) rep_of_min)
    with urest assms(10) obtain c\<^sub>1 c\<^sub>2 c where c: "eq = (F c\<^sub>1 c\<^sub>2 \<approx> c)"
      "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l"
      by (meson assms(1,2) use_list_invar_less_n_in_set')
    with urest assms(6) obtain b\<^sub>1 b\<^sub>2 b where b: "
           lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
           (b \<approx> c) \<in> Congruence_Closure
            (cc_list_set (cc_list ?base) \<union> pending_set (eq2 # pe))" unfolding congruence_closure.select_convs use_list_invar2_def
      using rep_a_valid by blast
    then have b2: "(b \<approx> c) \<in> Congruence_Closure
            (representativeE ?base \<union> pending_set (eq2 # pe))"
      unfolding representativeE_def congruence_closure.select_convs
      using Congruence_Closure_imp 
      by (metis (no_types, lifting) Congruence_Closure_split_rule Un_iff sup_commute)
    have *: "l ! rep_of l c\<^sub>1 = rep_of l c\<^sub>1" "l ! rep_of l c\<^sub>2 = rep_of l c\<^sub>2"
      "rep_of l c\<^sub>1 < length l" "rep_of l c\<^sub>2 < length l"
      using assms(1) c rep_of_min rep_of_bound rep_of_less_length_l by auto
    with assms(9) b have c_b: "rep_of l c\<^sub>1 = rep_of l b\<^sub>1" "rep_of l c\<^sub>2 = rep_of l b\<^sub>2"
      "b\<^sub>1 < length l" "b\<^sub>2 < length l" "b < length l"
      using lookup_invar_valid lookup_invar_less_n by fast+
    then have CC_b: "(F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> Congruence_Closure (representativeE ?base)"
      using CC_lookup_entry_in_CC b  "*" assms(9) by force
    then have "(b\<^sub>1 \<approx> c\<^sub>1) \<in> Congruence_Closure (representativeE ?base)"
      "(b\<^sub>2 \<approx> c\<^sub>2) \<in> Congruence_Closure (representativeE ?base)"
      using c_b c CC_same_rep 
      by auto
    then have "(F c\<^sub>1 c\<^sub>2 \<approx> b) \<in> Congruence_Closure (representativeE ?base)"
      using c_b b * assms(9) transitive3 CC_b by blast
    with assms urest show ?thesis
      using Congruence_Closure_union b2 c(1) transitive2 by blast
  qed 
qed

lemma correctness_invar_mini_step2:
  assumes "ufa_invar l" "a < length l" "b < length l"
    "a = left eq2" "b = right eq2"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar2 ?base")
    "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "(k \<approx> j) \<in> (representativeE
         \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq2 # pe, proof_forest = pf, pf_labels = pfl,
            input = ip\<rparr> \<union>
        pending_set (eq2 # pe))"
  shows "(k \<approx> j) \<in> Congruence_Closure 
(representativeE 
\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq2, 
    input = ip\<rparr>
\<union> pending_set pe
\<union> set (u ! rep_of l a))"
    (is "(k \<approx> j) \<in> Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))")
proof-
  from assms(11) consider
    (rep) c where "(k \<approx> j) = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
  | (new_eq) "(k \<approx> j) \<in> pending_set [eq2]"
  | (pending) "(k \<approx> j) \<in> pending_set pe"
    unfolding representativeE_def congruence_closure.select_convs 
    using pending_set_Cons
    by blast
  then show ?thesis proof(cases)
    case rep
    have "rep_of (ufa_union l a b) c = rep_of (ufa_union l a b) (rep_of l c)" 
      by (simp add: assms(1) assms(2) assms(3) rep(2) rep_of_idem rep_of_less_length_l ufa_union_aux)
    then have "(c \<approx> rep_of l c) \<in> Congruence_Closure (representativeE ?step)"
      using CC_same_rep using assms(1) rep(2) rep_of_less_length_l by auto
    then show ?thesis 
      using Congruence_Closure_split_rule rep(1) by auto
  next
    case new_eq
    with assms have "valid_vars_pending eq2 l" unfolding pending_invar_def 
      by fastforce
    with new_eq have eq: "(k \<approx> j) = (a \<approx> b)"
      by (simp add: assms(4) assms(5))
    have "rep_of (ufa_union l a b) a = rep_of (ufa_union l a b) b" 
      by (simp add: assms(1) assms(2) assms(3) ufa_union_aux)
    then have "(a \<approx> b) \<in> Congruence_Closure (representativeE ?step)"
      using CC_same_rep assms by auto
    then show ?thesis 
      using Congruence_Closure_split_rule eq by auto
  qed (simp add: base)
qed

lemma correctness_invar_mini_step:
  assumes "ufa_invar l" "a < length l" "b < length l"
    "a = left eq2" "b = right eq2"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar2 ?base")
    "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "Congruence_Closure 
(representativeE 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
\<union> pending_set (eq2 # pe))
= Congruence_Closure (representativeE 
\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq2, 
    input = ip\<rparr>
\<union> pending_set pe
\<union> set (u ! rep_of l a))"
    (is "?left = Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))")
proof(induction rule: Congruence_Closure_eq)
  case (right eq)
  then show ?case using correctness_invar_mini_step1 assms 
    by blast
next
  case (left eq)
  then consider
    (rep) c where "eq = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
  | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
    "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  | (new_eq) "eq \<in> pending_set [eq2]"
  | (pending) "eq \<in> pending_set pe"
    unfolding representativeE_def congruence_closure.select_convs 
    using pending_set_Cons
    by blast
  then show ?case proof(cases)
    case rep
    then show ?thesis using correctness_invar_mini_step2 assms left by blast 
  next
    case lookup
    then show ?thesis proof(cases "a' = rep_of l a \<or> b' = rep_of l a")
      case True
      with assms lookup obtain b\<^sub>1 b\<^sub>2 bb where b: "
           ((F b\<^sub>1 b\<^sub>2 \<approx> bb) \<in> set (u ! rep_of l a) \<and>
           rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
           rep_of l b\<^sub>2 = rep_of l c\<^sub>2 \<and>
           (bb \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (eq2 # pe)))"  
        unfolding lookup_invar2_def congruence_closure.select_convs 
        by blast
      from b have cc1: "(F b\<^sub>1 b\<^sub>2 \<approx> bb) \<in> 
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))"
        using Congruence_Closure_split_rule by blast
      from assms lookup rep_of_iff ufa_union_aux
      have c_length: "rep_of (ufa_union l a b) c\<^sub>1 = rep_of (ufa_union l a b) a'"
        "c\<^sub>1 < length l" "rep_of (ufa_union l a b) c\<^sub>2 = rep_of (ufa_union l a b) b'"
        "c\<^sub>2 < length l"
        unfolding lookup_invar_def congruence_closure.select_convs 
        by (metis equation.inject(2) option.discI option.inject)+
      from b have
        b_length: "b\<^sub>1 < length l" "b\<^sub>2 < length l" "bb < length l"
        using b True assms(10) lookup use_list_invar_less_n_in_set(1) apply blast        
        using b True assms(10) lookup use_list_invar_less_n_in_set(2) apply blast
        using b True assms(10) lookup use_list_invar_less_n_in_set(3) by blast
      then have reps_union: "rep_of (ufa_union l a b) c\<^sub>1 = rep_of (ufa_union l a b) b\<^sub>1" 
        "rep_of (ufa_union l a b) c\<^sub>2 = rep_of (ufa_union l a b) b\<^sub>2"
        using b 
         apply (metis (no_types, lifting) assms(1) assms(2) assms(3) c_length(2) rep_of_ufa_union_invar)
        using b b_length
        by (metis (no_types, lifting) \<open>c\<^sub>2 < length l\<close> assms(1) assms(2) assms(3) rep_of_ufa_union_invar)
      with CC_same_rep lookup have cc2: "(b\<^sub>1 \<approx> c\<^sub>1) \<in> Congruence_Closure (representativeE ?step)"
        "(b\<^sub>2 \<approx> c\<^sub>2) \<in> Congruence_Closure (representativeE ?step)" 
        by (simp_all add: \<open>c\<^sub>1 < length l\<close> \<open>c\<^sub>2 < length l\<close> b_length)
      from cc1 cc2 have *: "(F c\<^sub>1 c\<^sub>2 \<approx> bb) \<in>
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))"
        using Congruence_Closure_split_rule by auto
      from b have "(bb \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (eq2 # pe))"
        by auto
      then have "(bb \<approx> c) \<in>
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))" 
      proof(rule Congruence_Closure_imp)
        fix eqa
        assume eqa: "eqa \<in> cc_list_set
                (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq2 # pe,
                   proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) \<union>
               pending_set (eq2 # pe)"
        then have representativeE: "eqa \<in> representativeE
                \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq2 # pe,
                   proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
               pending_set (eq2 # pe)"
          unfolding representativeE_def 
          by blast
        from eqa consider
          (rep) c where "eqa = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
        | (new_eq) "eqa \<in> pending_set (eq2 # pe)"
          unfolding congruence_closure.select_convs 
          by blast
        then show "eqa \<in> Congruence_Closure
           (representativeE
             \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t,
                pending = pe, proof_forest = add_edge pf a b,
                pf_labels = add_label pfl pf a eq2, input = ip\<rparr> \<union>
            pending_set pe \<union>
            set (u ! rep_of l a))"
        proof(cases)
          case rep
          then show ?thesis 
            using correctness_invar_mini_step2 assms representativeE by blast
        next
          case new_eq
          then obtain hh hhh where "eqa = (hh \<approx> hhh)" 
            using pending_set_Constant by blast 
          then show ?thesis  
            using assms(1) assms(10) assms correctness_invar_mini_step2 representativeE by blast
        qed
      qed
      with * have *: "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> 
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))" using transitive2 
        by blast 
      have "rep_of (ufa_union l a b) (rep_of l c) = rep_of (ufa_union l a b) c"
        by (simp add: assms(1) assms(2) assms(3) lookup(4) rep_of_idem rep_of_less_length_l ufa_union_aux)
      with CC_same_rep
      have cc2: "(c \<approx> rep_of l c) \<in>
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))"
        using assms(1) lookup(4) rep_of_less_length_l Congruence_Closure_split_rule 
        by simp
      then have "(c\<^sub>1 \<approx> a') \<in> 
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))"
        "(c\<^sub>2 \<approx> b') \<in> Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))"
        using reps_union Congruence_Closure_split_rule CC_same_rep c_length lookup 
        by fastforce+
      with * have "(F a' b' \<approx> c) \<in> 
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))" 
        by blast 
      with lookup transitive2 cc2 show ?thesis  
        by blast
    next
      case False
      with lookup have *: "(ufa_union l a b) ! a' = a'" "(ufa_union l a b) ! b' = b'" 
        by auto
      have "rep_of (ufa_union l a b) (rep_of l c) = rep_of (ufa_union l a b) c"
        by (simp add: assms(1) assms(2) assms(3) lookup(4) rep_of_idem rep_of_less_length_l ufa_union_aux)
      with a_eq_rep_of_a_in_CC have **: "(rep_of (ufa_union l a b) c \<approx> rep_of l c) \<in>
Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))" 
        by (metis Congruence_Closure_split_rule assms(1) congruence_closure.select_convs(1) length_list_update lookup(4) rep_of_less_length_l)
      from lookup * base Congruence_Closure_union
      have "(F a' b' \<approx> rep_of (ufa_union l a b) c) \<in>
Congruence_Closure (representativeE ?step)"
        unfolding representativeE_def congruence_closure.select_convs by force
      with ** Congruence_Closure_union show ?thesis 
        using lookup(1) by blast
    qed
  next
    case new_eq
    then obtain hh hhh where "eq = (hh \<approx> hhh)" 
      by simp
    then show ?thesis using correctness_invar_mini_step2 assms left by blast 
  qed (simp add: base)
qed

lemma CC_cc_list_set_pending_mini_step:
  assumes "eq2 \<in> Congruence_Closure
          (cc_list_set
            (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>) \<union>
             pending_set (eq # pe))"
    "ufa_invar l" "a < length l" "b < length l"
    "a = left eq" "b = right eq"
  shows "eq2 \<in> Congruence_Closure
            (cc_list_set
              (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                 proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>) \<union>
             pending_set pe)"
  using assms(1) proof(rule Congruence_Closure_imp)
  fix eq'
  assume "eq' \<in> cc_list_set
                (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe,
                   proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) \<union>
               pending_set (eq # pe)"
  then consider k where "eq' = (k \<approx> rep_of l k)" "k < length l"  "l ! k \<noteq> k"
    | "eq' \<in> pending_set [eq]" | "eq' \<in> pending_set pe" 
    using pending_set_Cons unfolding congruence_closure.select_convs
    by blast
  then show "eq' \<in> Congruence_Closure
           (cc_list_set
             (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []],
                lookup = t, pending = pe, proof_forest = add_edge pf a b,
                pf_labels = add_label pfl pf a eq, input = ip\<rparr>) \<union>
            pending_set pe)"
  proof(cases)
    case 1
    then have same_rep: "rep_of (ufa_union l a b) k = rep_of (ufa_union l a b) (rep_of l k)"
      using assms(2) assms(3) assms(4) rep_of_bound rep_of_idem ufa_union_aux by presburger
    have "k < length (ufa_union l a b)""rep_of l k < length (ufa_union l a b)"
      by (simp_all add: "1"(2) assms(2) rep_of_bound)
    with 1 CC_same_rep_cc_list_set[of "ufa_union l a b"] same_rep
    have "eq' \<in> Congruence_Closure
     (cc_list_set
       (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []],
          lookup = t, pending = pe, proof_forest = add_edge pf a b,
          pf_labels = add_label pfl pf a eq, input = ip\<rparr>))"
      unfolding congruence_closure.select_convs by blast
    then show ?thesis 
      using Congruence_Closure_split_rule by blast
  next
    case 2
    then have "eq' = (a \<approx> b)" 
      using assms by auto
    then have same_rep: "rep_of (ufa_union l a b) a = rep_of (ufa_union l a b) b"
      using assms(2) assms(3) assms(4) rep_of_bound rep_of_idem ufa_union_aux by presburger
    have "a < length (ufa_union l a b)" "b < length (ufa_union l a b)"
      by (simp_all add: assms(3,4))
    with CC_same_rep_cc_list_set[of "ufa_union l a b"] same_rep
    have "eq' \<in> Congruence_Closure
     (cc_list_set
       (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []],
          lookup = t, pending = pe, proof_forest = add_edge pf a b,
          pf_labels = add_label pfl pf a eq, input = ip\<rparr>))" 
      unfolding congruence_closure.select_convs 
      using \<open>eq' = a \<approx> b\<close> by presburger
    then show ?thesis 
      using Congruence_Closure_split_rule by blast
  next
    case 3
    then show ?thesis 
      using Congruence_Closure_split_rule by blast
  qed
qed

lemma lookup_invar2_mini_step:
  assumes "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar2 ?base")
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l" "a < length l" "b < length l"
    "a = left eq" "b = right eq"
    "rep_of l a \<noteq> rep_of l b"
  shows "lookup_invar2 \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
    (is "lookup_invar2 ?mini_step")
  unfolding lookup_invar2_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix a' b' c c\<^sub>1 c\<^sub>2
  assume prems: "a' < length (ufa_union l a b)"
    "b' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "ufa_union l a b ! b' = b'"
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  with assms have *: "l ! a' = a'" "l ! b' = b'" 
    "a' < length l" "b' < length l"
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    using ufa_union_root apply blast+ 
    using prems by auto
  with assms obtain b\<^sub>1 b\<^sub>2 bc a\<^sub>1 a\<^sub>2 ac where 1: "
         (F b\<^sub>1 b\<^sub>2 \<approx> bc) \<in> set (u ! b') \<and>
         rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
         rep_of l b\<^sub>2 = rep_of l c\<^sub>2 \<and>
         (bc \<approx> c) \<in> Congruence_Closure
          (cc_list_set
            (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>) \<union>
             pending_set (eq # pe))"
    "(F a\<^sub>1 a\<^sub>2 \<approx> ac) \<in> set (u ! a') \<and>
         rep_of l a\<^sub>1 = rep_of l c\<^sub>1 \<and>
         rep_of l a\<^sub>2 = rep_of l c\<^sub>2 \<and>
         (ac \<approx> c) \<in> Congruence_Closure
          (cc_list_set
            (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>) \<union>
             pending_set (eq # pe))" 
    unfolding lookup_invar2_def congruence_closure.select_convs
    by presburger
  have 4: "aa < length l \<Longrightarrow> bb < length l \<Longrightarrow> 
rep_of l aa = rep_of l bb \<Longrightarrow> rep_of (ufa_union l a b) aa = rep_of (ufa_union l a b) bb" 
    for aa bb using assms rep_of_ufa_union_invar by blast
  from assms use_list_invar_less_n_in_set * 1
  have 5: "b\<^sub>1 < length l" "b\<^sub>2 < length l" "bc < length l"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "ac < length l"
    by meson+
  from correctness_invar_mini_step 
    assms have 6: "Congruence_Closure
          (representativeE
            \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr> \<union>
           pending_set (eq # pe)) 
= Congruence_Closure
         (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                 proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr> \<union>
             pending_set pe \<union> set (u ! rep_of l a))" 
    by force
  from assms prems * have "a' \<noteq> rep_of l a" "b' \<noteq> rep_of l a"
    by (metis nth_list_update_eq)+
  then have 3: "u[rep_of l a := []] ! a' = u ! a'"
    "u[rep_of l a := []] ! b' = u ! b'"
    by fastforce+
  from assms * lookup_invar_less_n
  have "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l"
    by simp_all
  with 1 4 5 6 * have "
           ((F b\<^sub>1 b\<^sub>2 \<approx> bc) \<in> set (u[rep_of l a := []] ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (bc \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                 proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>) \<union>
             pending_set pe)
            )"
    "(F a\<^sub>1 a\<^sub>2 \<approx> ac) \<in> set (u[rep_of l a := []] ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ac \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                 proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>) \<union>
             pending_set pe)
            " unfolding 6 3 using 
    CC_cc_list_set_pending_mini_step[OF _ assms(6,7,8,9,10)] 
    by blast+
  then show "(\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_of l a := []] ! a') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set pe)
            ) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_of l a := []] ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           (ba \<approx> c) \<in> Congruence_Closure
            ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
              aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
             pending_set pe)
            )"
    by auto
qed

lemma use_list_invar2_mini_step:
  assumes "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar2 ?base")
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"

"lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"

"pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"

"lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
"ufa_invar l" "a < length l" "b < length l"
"a = left eq" "b = right eq"
"rep_of l a \<noteq> rep_of l b"
shows "use_list_invar2' \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (u ! rep_of l a)"
  (is "use_list_invar2' ?mini_step (u ! rep_of l a)")
  unfolding use_list_invar2'_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard)
  fix a' c\<^sub>1 c\<^sub>2 c
  assume prems: "a' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u[rep_of l a := []] ! a')"
  then have "a' \<noteq> rep_of l a" 
    using assms by force
  with prems have *: "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u ! a')" "l ! a' = a'" "a' < length l"
    by auto
  with assms(2) have c_length: "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l"
    using use_list_invar_less_n_in_set by metis+
  show "\<exists>b\<^sub>1 b\<^sub>2 ba.
          lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<and>
          (ba \<approx> c) \<in> Congruence_Closure
           ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
             aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
            pending_set pe)
            \<or>
          ((F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l a) \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2) \<and>
          (ba \<approx> c) \<in> Congruence_Closure
           ({aa \<approx> rep_of (ufa_union l a b) aa |aa.
             aa < length (ufa_union l a b) \<and> ufa_union l a b ! aa \<noteq> aa} \<union>
            pending_set pe)
           "
  proof(cases "rep_of l c\<^sub>1 = rep_of l a \<or> rep_of l c\<^sub>2 = rep_of l a")
    case False
    with assms(5,6,7) c_length have same_rep: "rep_of l c\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
      "rep_of l c\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2" 
      by (auto simp add: rep_of_fun_upd' rep_of_idem)
    with assms(1) * obtain b\<^sub>1 b\<^sub>2 b where b: "
           lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
           (b \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr>) \<union>
             pending_set (eq # pe))
            " 
      unfolding use_list_invar2_def congruence_closure.select_convs
      by blast
    then have "lookup_entry t l c\<^sub>1 c\<^sub>2 = lookup_entry t (ufa_union l a b) c\<^sub>1 c\<^sub>2"
      using False assms(5,6,7) c_length rep_of_fun_upd' rep_of_min rep_of_refl by presburger
    with CC_cc_list_set_pending_mini_step[OF _ assms(6,7,8,9,10)] show ?thesis 
      using b same_rep by fastforce
  next
    case True
    with assms * obtain d\<^sub>1 d\<^sub>2 d where 
      d: "lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F d\<^sub>1 d\<^sub>2 \<approx> d)"
      "(d \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr>) \<union>
             pending_set (eq # pe))
            "
      unfolding use_list_invar2_def congruence_closure.select_convs
      by blast
    have **: "rep_of l c\<^sub>1 < length l" "rep_of l c\<^sub>2 < length l"
      "l ! rep_of l c\<^sub>1 = rep_of l c\<^sub>1" "l ! rep_of l c\<^sub>2 = rep_of l c\<^sub>2" 
      by (auto simp add: assms(6,7) c_length rep_of_less_length_l rep_of_min)
    with d have "rep_of l c\<^sub>1 = rep_of l d\<^sub>1" "rep_of l c\<^sub>2 = rep_of l d\<^sub>2"
      "d\<^sub>1 < length l" "d\<^sub>2 < length l"
      using assms(3,5) lookup_invar_valid lookup_invar_less_n c_length by auto
    with assms *  ** d obtain e\<^sub>1 e\<^sub>2 e where e:
      "(F e\<^sub>1 e\<^sub>2 \<approx> e) \<in> set (u ! rep_of l a)" 
      "rep_of l e\<^sub>1 = rep_of l d\<^sub>1 \<and>
           rep_of l e\<^sub>2 = rep_of l d\<^sub>2 \<and>
           (e \<approx> d) \<in> Congruence_Closure
            (cc_list_set
              (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr>) \<union>
             pending_set (eq # pe))
            "
      unfolding lookup_invar2_def congruence_closure.select_convs 
      apply(cases "rep_of l c\<^sub>1 = rep_of l a")
      using assms * d ** True by (metis (no_types, lifting))+
    then have "rep_of (ufa_union l a b) e\<^sub>1 = rep_of (ufa_union l a b) d\<^sub>1"
      "rep_of (ufa_union l a b) e\<^sub>2 = rep_of (ufa_union l a b) d\<^sub>2"
      using ufa_union_aux lookup_invar_less_n use_list_invar_less_n_in_set
      by (metis (no_types, lifting) "**" True assms(2,3,6-8) d(1))+
    then have reps: "rep_of (ufa_union l a b) e\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
      "rep_of (ufa_union l a b) e\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
      using ufa_union_aux \<open>d\<^sub>1 < length l\<close> \<open>rep_of l c\<^sub>1 = rep_of l d\<^sub>1\<close> 
        \<open>d\<^sub>2 < length l\<close> \<open>rep_of l c\<^sub>2 = rep_of l d\<^sub>2\<close> assms(6-8) c_length by presburger+
    from d e transitive1 have "(e \<approx> c) \<in> Congruence_Closure
            (cc_list_set
              (cc_list \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr>) \<union>
             pending_set (eq # pe))
            " 
      by blast
    with assms CC_cc_list_set_pending_mini_step have "(e \<approx> c) \<in> Congruence_Closure
            (cc_list_set
          (cc_list \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t,
             pending = pe, proof_forest = add_edge pf a b,
             pf_labels = add_label pfl pf a eq, input = ip\<rparr>) \<union>
         pending_set pe)" 
      by auto
    with reps e show ?thesis 
      unfolding congruence_closure.select_convs by blast
  qed
qed

lemma same_length_invar_mini_step:
  assumes 
    "same_length_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr> (length l)"
    "rep_of l a \<noteq> rep_of l b" "a = left eq" "b = right eq"
    "ufa_invar pf" "a < length l" "b < length l"
    "same_eq_classes_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
  shows "same_length_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (length (ufa_union l a b))"
  unfolding same_length_invar_def congruence_closure.select_convs
proof(standard,standard,standard,standard)
  show "length (u[rep_of l a := []]) = length (ufa_union l a b)" 
    using assms unfolding same_length_invar_def congruence_closure.select_convs by simp
  show "length t = length (ufa_union l a b)"
    using assms unfolding same_length_invar_def congruence_closure.select_convs by simp
  show "length (add_edge pf a b) = length (ufa_union l a b)"
    using assms unfolding same_length_invar_def congruence_closure.select_convs 
    using add_edge_preserves_length' unfolding same_eq_classes_invar_def by auto
  show "length (add_label pfl pf a eq) = length (ufa_union l a b)"
    using assms unfolding same_length_invar_def congruence_closure.select_convs 
    using add_label_preserves_length' by auto
qed simp

lemma valid_labels_invar_fun_upd: 
  assumes "valid_labels_invar pfl pf l"
    "(\<exists> c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d . (eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)))
\<and> ((b = c \<and> a = d) \<or> (a = c \<and> b = d))
\<and> c < length l \<and> d < length l
\<and> valid_vars_pending eq l
)"
    "ufa_invar pf"
    "length l = length pf"
    "length l = length pfl"
    "rep_of pf a \<noteq> rep_of pf b"
  shows "valid_labels_invar (CONST list_update pfl a (Some eq)) (pf[a := b]) l"
proof(standard, standard, standard, standard)
  fix n
  assume prems: "n < length (pf[a := b])" "pf[a := b] ! n \<noteq> n"
  obtain a\<^sub>1 a\<^sub>2 b\<^sub>1 b\<^sub>2 aa bb where valid_eq: "(eq = (One (aa \<approx> bb)) \<or> 
          eq = (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))
          \<and> (aa = a \<and> bb = b \<or> bb = a \<and> aa = b))
\<and> aa < length l \<and> bb < length l"
    using assms by auto
  have "the (pfl[a := Some eq] ! a) = eq" 
    using assms(2) assms(5) by force
  with assms(2,4,5) valid_eq have "(pfl[a := Some eq] ! a = Some (One (aa \<approx> bb)) \<or>
        pfl[a := Some eq] ! a = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))) \<and>
(aa = a \<and> bb = pf[a := b] ! a \<or> bb = a \<and> aa = pf[a := b] ! a)
\<and> (valid_vars_pending (the (pfl[a := Some eq] ! a)) l)"
    by auto
  with assms prems show "\<exists>aa a\<^sub>1 a\<^sub>2 ba b\<^sub>1 b\<^sub>2.
            (pfl[a := Some eq] ! n = Some (One (aa \<approx> ba)) \<or>
             pfl[a := Some eq] ! n = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> ba))) \<and>
            (aa = pf[a := b] ! n \<and> ba = n \<or> aa = n \<and> ba = pf[a := b] ! n) \<and>
            valid_vars_pending (the (pfl[a := Some eq] ! n)) l" 
    apply(cases "n = a")
     apply blast
    by force
next
  fix n
  assume "n < length (pf[a := b])" 
  then show "pf[a := b] ! n = n \<longrightarrow> pfl[a := Some eq] ! n = None"
    by (metis (mono_tags, lifting) assms(1) assms(6) length_list_update nth_list_update_eq nth_list_update_neq)
qed  

lemma valid_labels_invar_ufa_union: 
  assumes "valid_labels_invar pfl pf l"
    "ufa_invar l" "a < length l" "b < length l"
  shows "valid_labels_invar pfl pf (ufa_union l a b)"
proof(standard, standard, standard, standard)
  fix n
  assume prems: "n < length pf" "pf ! n \<noteq> n"
  then obtain a\<^sub>1 a\<^sub>2 b\<^sub>1 b\<^sub>2 aa bb where valid_eq: "((pfl ! n) = Some (One (aa \<approx> bb)) \<or> 
          (pfl ! n) = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> bb))
          \<and> (aa = pf ! n \<and> bb = n \<or> aa = n \<and> bb = pf ! n))
\<and> valid_vars_pending (the (pfl ! n)) l"
    using assms by blast
  then show "\<exists>aa a\<^sub>1 a\<^sub>2 ba b\<^sub>1 b\<^sub>2.
            (pfl ! n = Some (One (aa \<approx> ba)) \<or> pfl ! n = Some (Two (F a\<^sub>1 a\<^sub>2 \<approx> aa) (F b\<^sub>1 b\<^sub>2 \<approx> ba))) \<and>
            (aa = pf ! n \<and> ba = n \<or> aa = n \<and> ba = pf ! n) \<and>
            valid_vars_pending (the (pfl ! n)) (ufa_union l a b)" 
  proof(cases "(pfl ! n) = Some (One (aa \<approx> bb))")
    case True
    then show ?thesis using valid_eq prems 
      using assms(1) by force
  next
    case False
    then show ?thesis using valid_eq prems 
      using assms valid_vars_pending_cases length_list_update rep_of_ufa_union_invar 
      by force
  qed
next
  fix n
  assume "n < length pf"
  with assms show "pf ! n = n \<longrightarrow> pfl ! n = None" 
    by presburger
qed

lemma add_label_fun_upd:
  assumes "ufa_invar pf"
    "path pf (rep_of pf e) p e"
    "e < length pf" "k < length pf"
    "x \<notin> set p" "rep_of pf x \<noteq> rep_of pf k"
  shows "add_label pfl pf e eq = add_label pfl (pf[x := k]) e eq"
proof-
  have dom: "add_label_dom (pfl, pf, e, eq)"
    by (simp add: add_label_domain assms(1) assms(3))
  from dom assms show ?thesis 
  proof(induction pfl pf e eq arbitrary: p rule: add_label.pinduct)
    case (1 pfl pf e lbl)
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      with "1.prems" show ?thesis 
        by (metis add_label.domintros add_label.psimps list.set_intros(1) nth_list_update_neq path_no_cycle path_root)
    next
      case False
      then have "path pf (rep_of pf (pf ! e)) (butlast p) (pf ! e)" 
        by (metis "1.prems"(1-3) path_butlast rep_of_min rep_of_step)
      then have "x \<notin> set (butlast p)" 
        by (metis "1.prems"(5) in_set_butlastD)
      with 1 have IH: "add_label (pfl[e := Some lbl]) pf (pf ! e) (the (pfl ! e)) =
    add_label (pfl[e := Some lbl]) (pf[x := k]) (pf ! e) (the (pfl ! e))" 
        by (meson False \<open>path pf (rep_of pf (pf ! e)) (butlast p) (pf ! e)\<close> path_nodes_lt_length_l)
      from "1.prems" have pf_e: "pf ! e = pf[x := k] ! e" 
        by (metis False nth_list_update_eq nth_list_update_neq rep_of_fun_upd rep_of_refl rep_of_root)
      have "ufa_invar (pf[x := k])" 
        using ufa_invar_fun_upd' "1.prems" by blast
      then have "add_label_dom (pfl, (pf[x := k]), e, lbl)"
        by (simp add: "1.prems"(3) add_label_domain)
      with pf_e IH add_label.psimps 1(1) False show ?thesis 
        by metis
    qed
  qed
qed

lemma valid_labels_invar_mini_step:
  assumes "valid_labels_invar pfl pf l"
    "(\<exists> c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d . (eq = (One (c \<approx> d)) \<or>
eq = (Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)))
\<and> ((b = c \<and> a = d) \<or> (a = c \<and> b = d))
\<and> c < length l \<and> d < length l
\<and> valid_vars_pending eq l)"
    "ufa_invar pf"
    "length l = length pf"
    "length l = length pfl"
    "rep_of pf a \<noteq> rep_of pf b"
  shows "valid_labels_invar (add_label pfl pf a eq) (add_edge pf a b) l"
proof-
  have "a < length pf" "b < length pf" 
    using assms(2,4) by auto 
  then have domains: "add_edge_dom (pf, a, b)" "add_label_dom (pfl, pf, a, eq)" 
    using add_edge_domain add_label_domain assms by blast+
  show ?thesis
    using domains assms 
  proof(induction arbitrary: pfl eq l rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case proof(cases "pf ! e = e")
      case True
      with 1(1) "1.prems" have "add_label pfl pf e eq = pfl[e := Some eq]" 
        "add_edge pf e e' = pf[e := e']" 
        using add_label.psimps add_edge.psimps by metis+ 
      then show ?thesis 
        using valid_labels_invar_fun_upd[OF "1.prems"(2-7)] 
        by simp
    next
      case False
      then have "add_label pfl pf e eq = 
add_label (pfl[e := Some eq]) pf (pf ! e) (the (pfl ! e))"
        using "1.prems" add_label.psimps add_edge.psimps by presburger
      obtain pER where "path pf (rep_of pf e) pER e" 
        using "1.prems" path_to_root_correct by metis
      then have pER:  "path pf (rep_of pf e) (butlast pER) (pf ! e)" 
        by (metis "1.prems"(4) False path_butlast path_nodes_lt_length_l rep_of_min)
      have e_e': "e < length pf" "e' < length pf" using "1.prems"
        by metis+
      have "e \<notin> set (butlast pER)" 
        using "1.prems"(4) \<open>path pf (rep_of pf e) pER e\<close> path_remove_right by auto
      with pER have "add_label (pfl[e := Some eq]) pf (pf ! e) (the (pfl ! e)) = 
add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e))"
        using "1.prems" \<open>path pf (rep_of pf e) pER e\<close> add_label_fun_upd e_e'
        by (simp add: rep_of_idx ufa_invarD(2))
      have 2: "valid_labels_invar (pfl[e := Some eq]) (pf[e := e']) l"
        using valid_labels_invar_fun_upd[OF "1.prems"(2-7)] by simp
      have 3: "add_label_dom (pfl[e := Some eq], pf[e := e'], pf ! e, (the (pfl ! e)))"
        using "1.prems" add_label_domain ufa_invarD(2) ufa_invar_fun_upd' by auto
      let ?eq = "the (pfl ! e)"
      have 4: "\<exists>c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d.
       (?eq = One (c \<approx> d) \<or> ?eq = Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)) \<and>
       (e = c \<and> pf ! e = d \<or> pf ! e = c \<and> e = d) \<and> c < length l \<and> d < length l 
\<and> valid_vars_pending ?eq l" 
        using "1.prems" False ufa_invarD(2) by auto
      then have "path pf (pf ! e) [pf ! e, e] e" 
        by (simp add: "1.prems"(4) False path.step single ufa_invarD(2) e_e')
      have "rep_of (pf[e := e']) (pf ! e) = rep_of (pf) (pf ! e)" 
        using rep_of_fun_upd_aux1 
        using "1.prems"(4) False \<open>path pf (pf ! e) [pf ! e, e] e\<close> by auto
      have 5: "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        by (metis "1.prems"(4) "1.prems"(7) \<open>e < length pf\<close> \<open>e' < length pf\<close> \<open>rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)\<close> length_list_update nth_list_update_eq rep_of_fun_upd' rep_of_idx ufa_invar_fun_upd')
      have 6: "ufa_invar (pf[e := e'])" 
        by (simp add: "1.prems"(4) "1.prems"(7) \<open>e' < length pf\<close> ufa_invar_fun_upd')
      have "valid_labels_invar (add_label (pfl[e := Some eq])
(pf[e := e']) (pf ! e) (the (pfl ! e)))
     (add_edge (pf[e := e']) (pf ! e) e) l"
        using 1(2)[OF False 3 2 4 6 _ _ 5] "1.prems"(5,6)
        by auto
      then show ?thesis 
        using "1.hyps" "5" \<open>add_label (pfl[e := (Some eq)]) pf (pf ! e) (the (pfl ! e)) = add_label (pfl[e := Some eq]) (pf[e := e']) (pf ! e) (the (pfl ! e))\<close> \<open>add_label pfl pf e eq = add_label (pfl[e := Some eq]) pf (pf ! e) (the (pfl ! e))\<close> add_edge.psimps
        by presburger
    qed
  qed
qed

paragraph \<open>Invariants after one step of propagate\<close>

lemma proof_forest_invar_step: 
  assumes "ufa_invar l" "a < length l" "b < length l" "length l = length pf"
    "proof_forest_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "rep_of pf a \<noteq> rep_of pf b"
  shows "proof_forest_invar (propagate_step l u t pe pf pfl ip a b eq)"
  using assms proof(induction rule: propagate_step_induct)
  case base
  then show ?case 
    using add_edge_ufa_invar_invar assms(2) assms(3) proof_forest_invar_def by force
qed (simp_all add: proof_forest_invar_def)

lemma same_eq_classes_invar_step:
  assumes  "ufa_invar l" "a < length l" "b < length l"
    "same_eq_classes_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "same_eq_classes_invar ?base")
    "rep_of pf a \<noteq> rep_of pf b" "ufa_invar pf" "length pf = length l"
  shows "same_eq_classes_invar (propagate_step l u t pe pf pfl ip a b eq)"
  unfolding same_eq_classes_invar_def
  using assms proof(induction rule: propagate_step_induct)
  case base
  show ?case proof(standard, standard, standard, standard)
    fix i j
    let ?step = "\<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                     proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>"
    assume i_j: "i < length (proof_forest ?step)" "j < length (proof_forest ?step)"
    with add_edge_preserves_length' assms have 
      "length (proof_forest ?step) = length (proof_forest ?base)" 
      by simp
        \<comment>\<open>The representative classes of \<open>add_edge\<close> and \<open>ufa_invar\<close> have the same behaviour\<close>
    with rep_of_add_edge_aux ufa_union_aux 
    show "(rep_of (cc_list ?step) i = rep_of (cc_list ?step) j) =
           (rep_of (proof_forest ?step) i = rep_of (proof_forest ?step) j) " 
      using assms i_j unfolding same_eq_classes_invar_def congruence_closure.select_convs 
      by presburger
  qed
qed auto

lemma use_list_invar_impl_valid_input_propagate_loop:
  assumes "ufa_invar l" "a < length l" "b < length l" 
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "(\<forall> j < length (u ! rep_of l a) . use_list_valid_element ((u ! rep_of l a) ! j) (ufa_union l a b) (rep_of l b))"
    "(rep_of l b) < length l"
proof-
  have "rep_of l a < length l" "l ! rep_of l a = rep_of l a"
    by (simp_all add: assms(1) assms(2) rep_of_less_length_l rep_of_root)
  with assms have"(\<forall> j < length (u ! rep_of l a) . use_list_valid_element ((u ! rep_of l a) ! j) l (rep_of l a))"
    unfolding use_list_invar_def
    by fastforce
  moreover have "rep_of (ufa_union l a b) a = rep_of l b"
    by (simp add: assms(1) assms(2) assms(3) ufa_union_aux)
  ultimately show "(\<forall> j < length (u ! rep_of l a) . use_list_valid_element ((u ! rep_of l a) ! j) (ufa_union l a b) (rep_of l b))"
    "(rep_of l b) < length l" unfolding use_list_invar_def
    using assms(1) assms(3) ufa_union_aux rep_of_less_length_l by auto
qed

lemma lookup2_invar_impl_valid_input_propagate_loop:
  assumes "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar2 ?base")
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l" "a < length l" "b < length l"
    "a = left eq" "b = right eq"
    "rep_of l a \<noteq> rep_of l b"
  shows "\<forall> eq' \<in> set (u ! rep_of l a) . 
(\<exists> c\<^sub>1 c\<^sub>2 c . eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and> c\<^sub>1 < length l \<and> c\<^sub>2 < length l \<and> c < length l
\<and> (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c)

\<and> 
(rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)
)"
proof(standard)
  let ?step = "\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
  fix eq'
  assume eq': "eq' \<in> set (u ! rep_of l a)"
  with assms use_list_invar_less_n_in_set' rep_of_bound rep_of_root use_list_invar_less_n_in_set(1)
  obtain c\<^sub>1 c\<^sub>2 c where c: "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l" 
    by metis
  with assms obtain b\<^sub>1 b\<^sub>2 bb where 
    b: "lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> bb)" 
    "(bb \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (pending ?base))"
    unfolding use_list_invar2_def congruence_closure.select_convs
    by (metis (no_types, lifting) eq' rep_of_less_length_l rep_of_min)
  with assms c rep_of_bound rep_of_min b
  have *: "rep_of l c\<^sub>1 < length l" "l ! rep_of l c\<^sub>1 = rep_of l c\<^sub>1" 
    "rep_of l c\<^sub>2 < length l" "l ! rep_of l c\<^sub>2 = rep_of l c\<^sub>2" 
    "lookup_entry t l c\<^sub>1 c\<^sub>2 \<noteq> None"
    by auto
  with assms have c_eq_b: "rep_of l c\<^sub>1 = rep_of l b\<^sub>1" "rep_of l c\<^sub>2 = rep_of l b\<^sub>2"
    unfolding lookup_invar_def congruence_closure.select_convs 
    by (metis b(1) equation.inject(2) option.inject)+
  with assms *  b obtain d\<^sub>1 d\<^sub>2 d where d: 
    "(F d\<^sub>1 d\<^sub>2 \<approx> d) \<in> set (u ! rep_of l b\<^sub>2)"
    "rep_of l d\<^sub>1 = rep_of l b\<^sub>1" 
    "rep_of l d\<^sub>2 = rep_of l b\<^sub>2"
    "(d \<approx> bb) \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (eq # pe))"
    unfolding lookup_invar2_def congruence_closure.select_convs 
    by (metis (no_types, lifting))
  with transitive1 b(2) have CC_d_c: 
    "(d \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (eq # pe))" 
    unfolding congruence_closure.select_convs by blast
  from c_eq_b * assms c d have c2_step: "rep_of l a \<noteq> rep_of l c\<^sub>2 \<Longrightarrow> 
(F d\<^sub>1 d\<^sub>2 \<approx> d) \<in> set ((u[rep_of l a := []]) ! rep_of (ufa_union l a b) c\<^sub>2) \<and> 
rep_of (ufa_union l a b) d\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and> 
rep_of (ufa_union l a b) d\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    by (metis (no_types, lifting) ufa_union_aux nth_list_update_neq rep_of_ufa_union_invar use_list_invar_less_n_in_set(1,2))
  have CC_step: "eq2 \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (eq # pe)) 
\<Longrightarrow> eq2 \<in> Congruence_Closure (cc_list_set (cc_list ?step) \<union> pending_set pe)"  for eq2
    using assms CC_cc_list_set_pending_mini_step[OF _ assms(6,7,8,9,10)] assms by auto
  with assms * c b c_eq_b obtain e\<^sub>1 e\<^sub>2 e where e: "(F e\<^sub>1 e\<^sub>2 \<approx> e) \<in> set (u ! rep_of l b\<^sub>1)"
    "rep_of l e\<^sub>1 = rep_of l b\<^sub>1" "rep_of l e\<^sub>2 = rep_of l b\<^sub>2"
    "(e \<approx> bb) \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (eq # pe))"
    unfolding lookup_invar2_def congruence_closure.select_convs by (metis (no_types, lifting))
  with b(2) transitive1 have CC_e_c: 
    "(e \<approx> c) \<in> Congruence_Closure (cc_list_set (cc_list ?base) \<union> pending_set (eq # pe)) " 
    unfolding congruence_closure.select_convs by blast
  from e c_eq_b * assms c have c1_step: "rep_of l a \<noteq> rep_of l c\<^sub>1 \<Longrightarrow> 
(F e\<^sub>1 e\<^sub>2 \<approx> e) \<in> set ((u[rep_of l a := []]) ! rep_of (ufa_union l a b) c\<^sub>1) \<and> 
rep_of (ufa_union l a b) e\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and> 
rep_of (ufa_union l a b) e\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    by (metis (no_types, lifting) ufa_union_aux nth_list_update_neq rep_of_ufa_union_invar use_list_invar_less_n_in_set(1,2))
  have 1: "(rep_of l c\<^sub>1 \<noteq> rep_of l a \<Longrightarrow>
            contains_similar_equation ?step (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c)"
    using CC_e_c CC_step assms(6,7) c(2) c1_step rep_of_fun_upd' rep_of_idem by fastforce
  have "rep_of l c\<^sub>2 \<noteq> rep_of l a \<Longrightarrow>
            contains_similar_equation ?step (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c"
    using CC_d_c CC_step assms(6,7) c(3) c2_step rep_of_fun_upd' rep_of_idem by fastforce
  with c c1_step c2_step CC_step 1 have "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
           c\<^sub>1 < length l \<and> c\<^sub>2 < length l \<and> c < length l \<and>
           (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
            contains_similar_equation ?step (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
           (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
            contains_similar_equation ?step (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)"
    unfolding congruence_closure.select_convs by blast
  then show "\<exists>c\<^sub>1 c\<^sub>2 c.
              eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
              c\<^sub>1 < length l \<and> c\<^sub>2 < length l \<and> c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation ?step (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation ?step (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)" 
    by blast
qed

lemma lookup_invar_step: 
  assumes "ufa_invar l" "a < length l" "b < length l" 
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar ?base") 
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "length t = length l" "length u = length l"
  shows "lookup_invar (propagate_step l u t pe pf pfl ip a b eq)" 
proof-
  let ?mini_step = "\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
  have ufa_invar: "ufa_invar (ufa_union l a b)" 
    using assms(1) assms(2) assms(3) ufa_union_invar by auto
  with assms have lookup_invar: "lookup_invar ?mini_step" 
    by (simp add: lookup_invar_mini_step)
  with assms have use_list_invar: "use_list_invar ?mini_step" unfolding lookup_invar_def congruence_closure.select_convs 
    using use_list_invar_mini_step by presburger
  with lookup_invar_loop use_list_invar_impl_valid_input_propagate_loop assms show ?thesis
    by (simp add: lookup_invar ufa_invar use_list_invar)
qed

text \<open>All the equations in the pending list have valid variables, after a step in propagate.\<close>

lemma pending_invar_step:
  assumes "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    (is "pending_invar ?base")    
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l" "a < length l" "b < length l" "length t = length l" "length u = length l"
  shows "pending_invar (propagate_step l u t pe pf pfl ip a b eq)"
    (is "pending_invar ?step") 
  unfolding pending_invar_def
proof(standard)+
  let ?mini_step = "\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
  fix i
  assume i_valid: "i < length (pending ?step)"
  from assms have 1: "pending_invar ?mini_step" 
    by (simp add: pending_invar_mini_step)
  from assms have 2: "lookup_invar ?mini_step" 
    using lookup_invar_mini_step by blast
  from assms have 3: "use_list_invar ?mini_step" 
    using use_list_invar_mini_step by presburger
  from assms have 4: "ufa_invar (ufa_union l a b)" 
    "length t = length (ufa_union l a b)"
    "length (u[rep_of l a := []]) = length (ufa_union l a b)"
    "a < length (ufa_union l a b)" "b < length (ufa_union l a b)"
    using ufa_union_invar apply blast 
    by (simp_all add: assms)
  from assms use_list_invar_impl_valid_input_propagate_loop have "\<forall>j<length (u ! rep_of l a). use_list_valid_element ((u ! rep_of l a) ! j) (ufa_union l a b) 
(rep_of l b)" "rep_of l b < length l"
     apply blast
    using assms(4) assms(6) rep_of_less_length_l by auto
  with  pending_invar_loop 1 2 3 4 assms  
  show "valid_vars_pending ((pending ?step) ! i) (cc_list ?step)"
    using i_valid pending_invar_def by force
qed

lemma input_unchanged_loop:
  "input (propagate_loop a b cc) = 
input cc"
  apply(induction a b cc rule: propagate_loop.induct)
  by auto

lemma input_unchanged_step:
  "input (propagate_step l u t pe pf pfl ip a b eq) = ip"
  by (simp add: input_unchanged_loop)

lemma use_list_invar_step: 
  assumes "ufa_invar l" "a < length l" "b < length l" 
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar ?base") 
    "length u = length l"
  shows "use_list_invar (propagate_step l u t pe pf pfl ip a b eq)" (is "use_list_invar ?step")
  unfolding use_list_invar_def 
proof(standard, standard,standard, standard, standard)
  fix i j 
  assume i_j: "i < nr_vars ?step" 
    "cc_list ?step ! i = i"
    "j < length (use_list ?step ! i)"
  with use_list_invar_mini_step 
  have base: "use_list_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5))
  from assms use_list_invar_impl_valid_input_propagate_loop 
  have "\<forall>j<length (u ! rep_of l a). use_list_valid_element 
((u ! rep_of l a) ! j) (ufa_union l a b) (rep_of l b)" 
    by blast
  with base use_list_invar_loop show "use_list_valid_element (use_list ?step ! i ! j) (cc_list ?step) i"
    using assms i_j rep_of_bound ufa_union_invar use_list_invar_def by auto
qed

lemma lookup_invar2_step:
  assumes 
    "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l"  "length u = length l" "length t = length l"
    "a < length l" "b < length l" "rep_of l a \<noteq> rep_of l b"
    "a = left eq" "b = right eq"
  shows "lookup_invar2 (propagate_step l u t pe pf pfl ip a b eq)"
proof-
  let ?base = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf, pf_labels = pfl,
               input = ip\<rparr>"
  let ?mini_step = "
     \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
        proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>"
  have 1: "lookup_invar2 ?mini_step" 
    using assms lookup_invar2_mini_step by blast 
  have 2: "\<forall> eq' \<in> set (u ! rep_of l a) . 
(\<exists> c\<^sub>1 c\<^sub>2 c . eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and> c\<^sub>1 < length l \<and> c\<^sub>2 < length l \<and> c < length l
\<and> (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c)

\<and> 
(rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c)
)" using assms lookup2_invar_impl_valid_input_propagate_loop by blast
  then have 
    3: "\<forall>j<length (u ! rep_of l a). use_list_valid_element (u ! rep_of l a ! j) (ufa_union l a b) (rep_of l b)"
    "rep_of l b < length l"  using assms use_list_invar_impl_valid_input_propagate_loop 
    by simp_all
  have 4: "use_list_invar ?mini_step" "lookup_invar ?mini_step" 
    using assms use_list_invar_mini_step lookup_invar_mini_step by auto
  have 5: "\<forall>j<length (u ! rep_of l a). use_list_valid_element (u ! rep_of l a ! j) l (rep_of l a)"
    using assms unfolding use_list_invar_def congruence_closure.select_convs
    using rep_of_less_length_l rep_of_root by auto
  from lookup_invar2_loop[OF assms(6,9,10,11) 1 2 3 4 _ _ _ 5] show ?thesis 
    by (metis assms(7) assms(8) length_list_update)
qed

lemma use_list_invar2_step:
  assumes 
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l"  "length u = length l" "length t = length l"
    "a < length l" "b < length l" "rep_of l a \<noteq> rep_of l b"
    "a = left eq" "b = right eq"
  shows "use_list_invar2 (propagate_step l u t pe pf pfl ip a b eq)"
proof-
  let ?base = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf, pf_labels = pfl,
               input = ip\<rparr>"
  let ?mini_step = "
     \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
        proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>"
  have 1: "use_list_invar2' ?mini_step (u ! rep_of l a)" 
    using assms use_list_invar2_mini_step by blast 
  then have 
    3: "\<forall>j<length (u ! rep_of l a). use_list_valid_element (u ! rep_of l a ! j) (ufa_union l a b) (rep_of l b)"
    "rep_of l b < length l"  using assms use_list_invar_impl_valid_input_propagate_loop 
    by simp_all
  have 4: "use_list_invar ?mini_step" "lookup_invar ?mini_step" 
    using assms use_list_invar_mini_step lookup_invar_mini_step by auto
  have 5: "\<forall>j<length (u ! rep_of l a). use_list_valid_element (u ! rep_of l a ! j) l (rep_of l a)"
    using assms unfolding use_list_invar_def congruence_closure.select_convs
    using rep_of_less_length_l rep_of_root by auto
  from use_list_invar2_loop[OF assms(6,9,10,11) 1 3 4 _ _ _ 5 ]  show ?thesis 
    by (metis assms(7) assms(8) length_list_update)
qed

lemma correctness_invar_invar_step:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "a < length l" "b < length l" "rep_of l a \<noteq> rep_of l b"
    "a = left eq" "b = right eq"
  shows "correctness_invar (propagate_step l u t pe pf pfl ip a b eq)" 
proof-
  let ?mini_step = "\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"
  from assms pending_left_right_valid have length_union:  "length l = length (ufa_union l a b)"
    by auto
  from assms have invar: "ufa_invar l" unfolding cc_list_invar_def 
    by simp
  from assms have lengths: "length u = length l" "length t = length l" 
    unfolding same_length_invar_def by auto
  with invar have invars: "lookup_invar ?mini_step" "use_list_invar ?mini_step"
    "cc_list_invar ?mini_step"
    using assms(1,4,5) lookup_invar_mini_step apply blast
    using assms(1,4,5) use_list_invar_mini_step lengths invar apply presburger
    using assms unfolding cc_list_invar_def by (simp add: ufa_union_invar)
  from correctness_invar_mini_step assms invar have base: "Congruence_Closure (representativeE ?mini_step
\<union> pending_set pe
\<union> set (u ! rep_of l a)) = 
Congruence_Closure 
(representativeE 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
\<union> pending_set (eq # pe))" 
    by blast
  have 
    "\<forall>j<length (u ! rep_of l a). use_list_valid_element (u ! rep_of l a ! j) (ufa_union l a b) (rep_of l b)"
    "rep_of l b < length l" 
    using invar use_list_invar_impl_valid_input_propagate_loop[OF invar assms(4,5)] assms(1)
     apply blast
    by (simp add: assms(4,5) invar rep_of_less_length_l)
  with correctness_invar_loop[of "a"
      "?mini_step"
      b "u ! rep_of l a" "rep_of l b"] assms use_list_invar_impl_valid_input_propagate_loop 
  have *: "Congruence_Closure (representativeE \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>
\<union> pending_set pe
\<union> set (u ! rep_of l a)) = 
Congruence_Closure (representativeE (propagate_step l u t pe pf pfl ip a b eq)
\<union> pending_set (pending (propagate_step l u t pe pf pfl ip a b eq)))" 
    using assms assms(2,3) length_union invars
    unfolding congruence_closure.select_convs 
    by (metis length_list_update lengths(1) lengths(2))
  have "Congruence_Closure (input (propagate_step l u t pe pf pfl ip a b eq)) = 
Congruence_Closure ip" 
    by (simp add: input_unchanged_loop)
  with assms * base show ?thesis unfolding correctness_invar_def congruence_closure.select_convs 
    by argo
qed

lemma same_length_invar_step:
  assumes 
    "same_length_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr> (length l)"
    "rep_of l a \<noteq> rep_of l b" "a = left eq" "b = right eq"
    "a < length l" "b < length l"
    "proof_forest_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "same_eq_classes_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
  shows "same_length_invar (propagate_step l u t pe pf pfl ip a b eq)
(nr_vars (propagate_step l u t pe pf pfl ip a b eq))" 
proof-
  have "same_length_invar \<lparr>cc_list = (ufa_union l a b), 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (length (ufa_union l a b))"
    using same_length_invar_mini_step assms unfolding proof_forest_invar_def by force
  then show ?thesis using same_length_invar_loop assms by simp
qed 

lemma cc_list_invar_step: 
  assumes "a < length l" "b < length l" 
    "cc_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "cc_list_invar (propagate_step l u t pe pf pfl ip a b eq)"
proof-
  have "cc_list_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>" using assms ufa_union_invar unfolding cc_list_invar_def 
    by simp
  then show ?thesis using cc_list_invar_loop
    by blast
qed

lemma pf_labels_invar_step:
  assumes "ufa_invar pf" "a < length l" "b < length l" 
    "a = left eq" "b = right eq"
    "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "pf_labels_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "length l = length pf" "length l = length pfl"  
    "rep_of pf a \<noteq> rep_of pf b"
    "ufa_invar l" 
  shows "pf_labels_invar (propagate_step l u t pe pf pfl ip a b eq)"
proof-
  have *: "\<exists>c\<^sub>1 c\<^sub>2 c d\<^sub>1 d\<^sub>2 d.
       (eq = One (c \<approx> d) \<or> eq = Two (F c\<^sub>1 c\<^sub>2 \<approx> c) (F d\<^sub>1 d\<^sub>2 \<approx> d)) \<and>
       (b = c \<and> a = d \<or> a = c \<and> b = d) \<and> c < length l \<and> d < length l
\<and> valid_vars_pending eq l"
    using assms pending_invar_Cons valid_vars_pending_cases by fastforce
  have "valid_labels_invar (add_label pfl pf a eq) (add_edge pf a b) l"
    using valid_labels_invar_mini_step[OF assms(7)[unfolded pf_labels_invar_def congruence_closure.select_convs] * assms(1,8,9,10)] 
    by blast
  then have "pf_labels_invar \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>" using  assms(2,3,11) valid_labels_invar_ufa_union
    unfolding pf_labels_invar_def congruence_closure.select_convs 
    by presburger
  then show ?thesis using pf_labels_invar_loop proof_forest_loop cc_list_loop
    unfolding pf_labels_invar_def congruence_closure.select_convs
    by simp
qed

lemma cc_invar_step:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>" "a = left eq" "b = right eq" "rep_of l a \<noteq> rep_of l b"
  shows "cc_invar (propagate_step l u t pe pf pfl ip a b eq)"
proof (rule conjI)+
  show "cc_list_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms cc_list_invar_def ufa_union_invar cc_list_invar_loop
    by (metis congruence_closure.select_convs(1) pending_left_right_valid)
  have invar: "ufa_invar l" "ufa_invar pf" 
    using assms unfolding cc_list_invar_def proof_forest_invar_def by auto
  have a_b: "a < length l" "b < length l" 
    using assms pending_left_right_valid by blast+
  have same_length: "length u = length l" "length t = length l" 
    "length pf = length l" "length pfl = length l"  
    using assms unfolding same_length_invar_def congruence_closure.select_convs by blast+
  have rep_pf: "rep_of pf a \<noteq> rep_of pf b"
    using assms(1,4) a_b same_length(3) unfolding same_eq_classes_invar_def by auto
  show "use_list_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms invar same_length a_b use_list_invar_step by blast
  show "lookup_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms lookup_invar_step same_length a_b invar by blast
  show "proof_forest_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms proof_forest_invar_step same_length invar a_b rep_pf by presburger
  show "correctness_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms correctness_invar_invar_step a_b by presburger
  show "same_eq_classes_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms same_eq_classes_invar_step a_b invar rep_pf same_length(3) by blast
  show "same_length_invar (propagate_step l u t pe pf pfl ip a b eq)
     (nr_vars (propagate_step l u t pe pf pfl ip a b eq))"
    using assms same_length_invar_step a_b by simp
  show "pending_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms pending_invar_step a_b invar(1) same_length by blast
  show "lookup_invar2 (propagate_step l u t pe pf pfl ip a b eq)"
    using assms lookup_invar2_step a_b invar(1) same_length by presburger
  show "use_list_invar2 (propagate_step l u t pe pf pfl ip a b eq)"
    using assms use_list_invar2_step a_b invar(1) same_length by blast
  show "pf_labels_invar (propagate_step l u t pe pf pfl ip a b eq)"
    using assms pf_labels_invar_step a_b invar same_length rep_pf by auto
qed

subsection \<open>Invariants after propagate\<close>

lemma correctness_invar_step2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "rep_of l (left eq) = rep_of l (right eq)"
  shows "Congruence_Closure
     (representativeE
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
      pending_set
       (pending
         \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)) 
= Congruence_Closure
     (representativeE
      \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr> \<union>
      pending_set
       (pending
         \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>))" (is "Congruence_Closure ?left = Congruence_Closure ?right")
proof(induction rule: Congruence_Closure_eq)
  case (left a)
  then have "a \<in> ?right" unfolding representativeE_def congruence_closure.select_convs pending_set_Cons[of eq pe]
    by fast
  then show ?case 
    by auto
next
  case (right b)
  then show ?case proof(cases "b \<in> pending_set [eq]")
    case True
    then have b: "b = (left eq \<approx> right eq)"
      by auto
    have "left eq < length l" "right eq < length l" 
      using assms pending_left_right_valid by blast+
    with assms b have "b \<in> Congruence_Closure
     (representativeE
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)"
      using CC_same_rep by auto
    then show ?thesis 
      by (simp add: Congruence_Closure_split_rule)
  next
    case False
    with right have "b \<in> ?left" unfolding representativeE_def congruence_closure.select_convs pending_set_Cons[of eq pe]
      by fast
    then show ?thesis 
      by (simp add: base)
  qed
qed

lemma Congruence_Closure_step2:
  assumes "(left eq \<approx> right eq) \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a})"
    "k \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set (eq # pe))"
  shows "k \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)"
  using assms(2) proof(rule Congruence_Closure_imp)
  fix a
  assume prems: "a \<in> {a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set (eq # pe)"
  then show "a \<in>
Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)" 
  proof(cases "a \<in> pending_set [eq]")
    case True
    then have "a = (left eq \<approx> right eq)" 
      by simp
    then show ?thesis using assms Congruence_Closure_union by auto
  next
    case False
    then have "a \<in> ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)" 
      using prems unfolding pending_set_Cons[of eq pe] by blast 
    then show ?thesis by (simp add: base)
  qed
qed

lemma lookup_invar2_step2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "rep_of l (left eq) = rep_of l (right eq)"
  shows "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar2 ?step")
  unfolding lookup_invar2_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix a' b' c c\<^sub>1 c\<^sub>2
  assume "a' < length l" "b' < length l"
    "l ! a' = a'" "l ! b' = b'"
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  with assms obtain  b\<^sub>1 b\<^sub>2 b a\<^sub>1 a\<^sub>2 a where b: 
    "(F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> set (u ! a') \<and>
           rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
           rep_of l b\<^sub>2 = rep_of l c\<^sub>2 "
    "(b \<approx> c) \<in>
Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set (eq # pe))"

"(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> set (u ! b') \<and>
           rep_of l a\<^sub>1 = rep_of l c\<^sub>1 \<and>
           rep_of l a\<^sub>2 = rep_of l c\<^sub>2 "
"(a \<approx> c) \<in>
Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set (eq # pe))" 
    unfolding lookup_invar2_def congruence_closure.select_convs by blast
  have "left eq < length l" "right eq < length l" 
    "rep_of (cc_list ?step) (left eq) = rep_of (cc_list ?step) (right eq)"
    using assms pending_left_right_valid apply blast+
    by (simp add: assms(2))
  then have CC_eq: "(left eq \<approx> right eq) \<in> Congruence_Closure (cc_list_set (cc_list ?step))"
    using assms CC_same_rep_cc_list_set[of l] by simp
  then show "(\<exists>b\<^sub>1 b\<^sub>2 b.
           (F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> set (u ! a') \<and>
           rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
           rep_of l b\<^sub>2 = rep_of l c\<^sub>2 \<and>
           (b \<approx> c) \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 b.
           (F b\<^sub>1 b\<^sub>2 \<approx> b) \<in> set (u ! b') \<and>
           rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
           rep_of l b\<^sub>2 = rep_of l c\<^sub>2 \<and>
           (b \<approx> c) \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe))"
    using CC_eq Congruence_Closure_step2 b unfolding congruence_closure.select_convs by blast
qed

lemma use_list_invar2_step2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "rep_of l (left eq) = rep_of l (right eq)"
  shows "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "use_list_invar2 ?step")
  unfolding use_list_invar2_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard)
  fix a' c c\<^sub>1 c\<^sub>2
  assume "a' < length l" "l ! a' = a'"
    "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u ! a')"
  with assms obtain b\<^sub>1 b\<^sub>2 b where b: 
    "lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
          (b \<approx> c) \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} 
          \<union> pending_set (eq # pe)) " 
    unfolding use_list_invar2_def congruence_closure.select_convs by blast
  have "left eq < length l" "right eq < length l" 
    "rep_of (cc_list ?step) (left eq) = rep_of (cc_list ?step) (right eq)"
    using assms pending_left_right_valid apply blast+
    by (simp add: assms(2))
  then have CC_eq: "(left eq \<approx> right eq) \<in> Congruence_Closure (cc_list_set (cc_list ?step))"
    using assms CC_same_rep_cc_list_set[of l]
    by fastforce
  then show "(\<exists>b\<^sub>1 b\<^sub>2 b.
          lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
          (b \<approx> c) \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe))"
    using CC_eq Congruence_Closure_step2 b unfolding congruence_closure.select_convs by blast
qed

lemma cc_invar_step2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "rep_of l (left eq) = rep_of l (right eq)"
  shows "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?step")
proof (rule conjI)+
  show "cc_list_invar ?step"
    using assms unfolding cc_list_invar_def by simp
  show "use_list_invar ?step"
    using assms unfolding use_list_invar_def by simp
  show "lookup_invar ?step"
    using assms unfolding lookup_invar_def by simp
  show "proof_forest_invar ?step"
    using assms unfolding proof_forest_invar_def by simp
  show "correctness_invar ?step"
    using assms correctness_invar_def correctness_invar_step2 by auto
  show "same_eq_classes_invar ?step"
    using assms unfolding same_eq_classes_invar_def by simp
  show "same_length_invar ?step (nr_vars ?step)"
    using assms unfolding same_length_invar_def by simp
  show "pending_invar ?step"
    using assms pending_invar_Cons pending_invar_def unfolding pending_invar_def by blast
  show "lookup_invar2 ?step"
    using assms lookup_invar2_step2 by blast
  show "use_list_invar2 ?step"
    using assms use_list_invar2_step2 by blast
  show "pf_labels_invar ?step"
    using assms unfolding pf_labels_invar_def congruence_closure.select_convs by argo
qed

lemma cc_invar_propagate: 
  assumes "propagate_dom cc" "cc_invar cc"
  shows "cc_invar (propagate cc)"
  using assms proof(induction cc rule: propagate.pinduct)
  case (2 l u t eq pe pf pfl ip)
  then show ?case 
  proof(cases "rep_of l (left eq) = rep_of l (right eq)")
    case True
    let ?step = "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    have "cc_invar ?step"
      using "2.prems" cc_invar_step2 True by blast 
    then show ?thesis using 2(2) 
      by (simp add: "2.hyps" True)
  next
    case False
    let ?step = "(propagate_step l u t pe pf pfl ip (left eq) (right eq) eq)"
    have invar: "ufa_invar l" using "2.prems" unfolding cc_list_invar_def by simp
    have left_right: "left eq < length l" "right eq < length l" 
      using "2.prems" pending_left_right_valid by auto
    have "cc_invar ?step"
      using "2.prems" cc_invar_step invar left_right False by blast
    then show ?thesis using 2(3)
      by (simp add: "2.hyps" False)
  qed            
qed simp

subsection \<open>Invariants after merge\<close>

lemma representativeE_unchanged:
  "representativeE
        \<lparr>cc_list = l, use_list = u, lookup = t, pending = k # pe, proof_forest = pf, pf_labels = pfl,
           input = insert q ip\<rparr> 
= representativeE
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  unfolding representativeE_def 
  by auto

lemma correctness_invar_merge1:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (a \<approx> b)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
  shows "correctness_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b) # pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"
    (is "correctness_invar ?step")
proof-
  have *: "Congruence_Closure (representativeE ?step \<union> pending_set (pending ?step))
= Congruence_Closure (representativeE ?base \<union> pending_set (pending ?base) \<union> {(a \<approx> b)})"
    apply(induction rule: Congruence_Closure_eq)
    by (simp_all add: base representativeE_unchanged)
  then have "input ?step = input ?base \<union> {(a \<approx> b)}"
    by auto
  with * assms show ?thesis unfolding correctness_invar_def 
    by (metis CC_union_correct)
qed

lemma Congruence_Closure_pending_Cons:
  "Congruence_Closure
            ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe) 
\<subseteq>
Congruence_Closure
            ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set (k # pe))"
  unfolding pending_set_Cons[of k pe] using Congruence_Closure_union 
  by (metis (no_types, lifting) Congruence_Closure_union' boolean_algebra_cancel.sup2)

lemma lookup_invar2_merge1:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (a \<approx> b)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
  shows "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b) # pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"
    (is "lookup_invar2 ?step") 
  using assms Congruence_Closure_pending_Cons 
  unfolding lookup_invar2_def congruence_closure.select_convs 
  by blast

lemma use_list_invar2_merge1:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (a \<approx> b)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
  shows "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b) # pe, proof_forest = pf, pf_labels = pfl,
            input = insert (a \<approx> b) ip\<rparr>"
    (is "use_list_invar2 ?step")
proof-
  have "(k\<^sub>1 \<approx> k\<^sub>2) \<in> Congruence_Closure
            ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)
\<Longrightarrow>
(k\<^sub>1 \<approx> k\<^sub>2) \<in> Congruence_Closure
            ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set (One (a \<approx> b) # pe))"
    for k\<^sub>1 k\<^sub>2 unfolding pending_set_Cons[of "One (a \<approx> b)" pe] using Congruence_Closure_split_rule 
    by (metis (no_types, lifting) Un_assoc Un_commute)
  with assms show ?thesis
    unfolding use_list_invar2_def congruence_closure.select_convs 
    by blast
qed

lemma cc_invar_merge1:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (a \<approx> b)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
  shows "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
      proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"
    (is "cc_invar ?step")
proof(rule conjI)+
  show "cc_list_invar ?step"
    using assms unfolding cc_list_invar_def by simp
  show "use_list_invar ?step"
    using assms unfolding use_list_invar_def by simp
  show "lookup_invar ?step"
    using assms unfolding lookup_invar_def by simp
  show "proof_forest_invar ?step"
    using assms unfolding proof_forest_invar_def by simp
  show "correctness_invar ?step"
    using assms correctness_invar_merge1 by blast
  show "same_eq_classes_invar ?step"
    using assms unfolding same_eq_classes_invar_def by simp
  show "same_length_invar ?step (nr_vars ?step)"
    using assms unfolding same_length_invar_def by simp
  show "pending_invar ?step"
    using assms pending_invar_Cons pending_invar_def unfolding pending_invar_def by simp
  show "lookup_invar2 ?step"
    using assms lookup_invar2_merge1 by blast
  show "use_list_invar2 ?step"
    using assms use_list_invar2_merge1 by blast
  show "pf_labels_invar ?step"
    using assms unfolding pf_labels_invar_def congruence_closure.select_convs by argo
qed

lemma correctness_invar_merge2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "correctness_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, 
            pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "correctness_invar ?step")
proof-
  let ?new_pending = "left (Two (F a\<^sub>1 a\<^sub>2 \<approx> a)
        (the (lookup_entry t l a\<^sub>1 a\<^sub>2))) \<approx> right (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (the (lookup_entry t l a\<^sub>1 a\<^sub>2)))"
  have valid: "a\<^sub>1 < length l" "a\<^sub>2 < length l" "ufa_invar l" "length t = length l"
    using assms unfolding cc_list_invar_def same_length_invar_def by auto
  from assms(3)have "lookup_entry t l a\<^sub>1 a\<^sub>2 \<noteq> None" 
    unfolding lookup_Some.simps Option.is_none_def .
  with assms obtain d\<^sub>1 d\<^sub>2 d where d: "lookup_entry t l a\<^sub>1 a\<^sub>2 = Some (F d\<^sub>1 d\<^sub>2 \<approx> d)"
    "rep_of l a\<^sub>1 = rep_of l d\<^sub>1" "rep_of l a\<^sub>2 = rep_of l d\<^sub>2"
    "d\<^sub>1 < length l" "d\<^sub>2 < length l" "d < length l"
    unfolding lookup_invar_def congruence_closure.select_convs 
    using valid rep_of_min rep_of_less_length_l
    by metis 
  then have new_pending: "?new_pending = (a \<approx> d)" 
    by simp
  have new_input: "(input ?step) = (input ?base \<union> {F a\<^sub>1 a\<^sub>2 \<approx> a})"
    unfolding congruence_closure.select_convs by fast
  have new_pending_list: "pending_set (link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe) = 
pending_set pe \<union> {?new_pending}"
    using pending_set_Cons by auto
  from representativeE_unchanged 
  have cc1: "(F d\<^sub>1 d\<^sub>2 \<approx> d) \<in> Congruence_Closure (representativeE ?base)"
    by (metis CC_lookup_entry_in_CC d assms(1) congruence_closure.select_convs(1,3) rep_of_bound rep_of_root valid(3))+
  then have cc2: "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> Congruence_Closure (representativeE ?base \<union> pending_set pe \<union>
      {F a\<^sub>1 a\<^sub>2 \<approx> a})"
    "(a \<approx> d) \<in> Congruence_Closure (representativeE ?base \<union> pending_set pe \<union>
      {a \<approx> d})" using base by auto
  have cc3: "(a\<^sub>1 \<approx> d\<^sub>1) \<in> Congruence_Closure (representativeE ?base)"
    "(a\<^sub>2 \<approx> d\<^sub>2) \<in> Congruence_Closure (representativeE ?base)" 
    using d CC_same_rep assms(2) by auto
  have *: "Congruence_Closure (representativeE ?step \<union> pending_set (pending ?step))
= Congruence_Closure (representativeE ?base \<union> pending_set (pending ?base) \<union> 
{?new_pending})"
    using base representativeE_unchanged by auto
  also have "... = Congruence_Closure (representativeE ?base \<union> pending_set (pending ?base) \<union> 
{F a\<^sub>1 a\<^sub>2 \<approx> a})" proof(induction rule: Congruence_Closure_eq)
    case (left eq)
    then consider a where "eq = (a \<approx> rep_of l a)" "a < length l" "l ! a \<noteq> a"
      |  a' b' c c\<^sub>1 c\<^sub>2 where
        "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
        "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
      | "eq \<in> pending_set pe"
      | "eq = (a \<approx> d)"
      unfolding representativeE_def congruence_closure.select_convs 
      using new_pending by blast
    then show ?case proof(cases)
      case 4
      then show ?thesis
        using Congruence_Closure_split_rule cc1 cc2 cc3 monotonic transitive3
        unfolding congruence_closure.select_convs 4 by meson
    qed (simp_all add: base representativeE_def)
  next
    case (right eq)
    then consider a where "eq = (a \<approx> rep_of l a)" "a < length l" "l ! a \<noteq> a"
      |  a' b' c c\<^sub>1 c\<^sub>2 where
        "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
        "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
      | "eq \<in> pending_set pe"
      | "eq = (F a\<^sub>1 a\<^sub>2 \<approx> a)"
      unfolding representativeE_def congruence_closure.select_convs 
      using new_pending by blast
    then show ?case proof(cases)
      case 4
      then have 
        "(F a\<^sub>1 a\<^sub>2 \<approx> d) \<in> Congruence_Closure (representativeE ?base \<union> pending_set pe \<union>
      {a \<approx> d}) " using Congruence_Closure_split_rule cc1 cc3(1) cc3(2) 
        by (meson symmetric transitive3)
      then show ?thesis 
        using "4" cc2(2) new_pending transitive2 by auto
    qed (auto simp add: representativeE_def)
  qed
  with * assms new_input show ?thesis unfolding correctness_invar_def 
    by (metis CC_union_correct)
qed

lemma pending_invar_merge2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, 
            pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "pending_invar ?step") unfolding pending_invar_def congruence_closure.select_convs 
proof(standard, standard)
  fix i 
  assume prems: "i < length (link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) # pe)"
  have valid: "a\<^sub>1 < length l" "a\<^sub>2 < length l" "ufa_invar l" "length t = length l"
    using assms unfolding cc_list_invar_def same_length_invar_def by auto
  from assms(3) have "lookup_entry t l a\<^sub>1 a\<^sub>2 \<noteq> None" 
    unfolding lookup_Some.simps Option.is_none_def .
  with assms obtain d\<^sub>1 d\<^sub>2 d where d: "lookup_entry t l a\<^sub>1 a\<^sub>2 = Some (F d\<^sub>1 d\<^sub>2 \<approx> d)"
    "rep_of l a\<^sub>1 = rep_of l d\<^sub>1" "rep_of l a\<^sub>2 = rep_of l d\<^sub>2"
    "d\<^sub>1 < length l" "d\<^sub>2 < length l" "d < length l"
    unfolding lookup_invar_def congruence_closure.select_convs 
    using valid rep_of_min rep_of_less_length_l
    by metis 
  then have lookup: "the (lookup_entry t l a\<^sub>1 a\<^sub>2) = (F d\<^sub>1 d\<^sub>2 \<approx> d)"
    by simp
  then have *: "valid_vars_pending (link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)) l" 
    unfolding link_to_lookup.simps lookup valid_vars_pending.simps valid_vars.simps
    using assms d unfolding congruence_closure.select_convs by auto
  show "valid_vars_pending ((link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) # pe) ! i) l"
  proof(cases "i = 0")
    case True
    then show ?thesis using * by simp
  next
    case False
    then show ?thesis 
      using assms unfolding pending_invar_def congruence_closure.select_convs using prems by auto
  qed
qed

lemma cc_invar_merge2:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, 
            pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "cc_invar ?step")
proof(rule conjI)+
  show "cc_list_invar ?step"
    using assms unfolding cc_list_invar_def by simp
  show "use_list_invar ?step"
    using assms unfolding use_list_invar_def by simp
  show "lookup_invar ?step"
    using assms unfolding lookup_invar_def by simp
  show "proof_forest_invar ?step"
    using assms unfolding proof_forest_invar_def by simp
  show "correctness_invar ?step"
    using assms correctness_invar_merge2 by blast
  show "same_eq_classes_invar ?step"
    using assms unfolding same_eq_classes_invar_def by simp
  show "same_length_invar ?step (nr_vars ?step)"
    using assms unfolding same_length_invar_def by simp
  show "pending_invar ?step"
    using assms pending_invar_merge2 by simp
  show "lookup_invar2 ?step"
    using assms Congruence_Closure_pending_Cons 
    unfolding lookup_invar2_def congruence_closure.select_convs
    by blast
  show "use_list_invar2 ?step"
    using assms Congruence_Closure_pending_Cons 
    unfolding use_list_invar2_def congruence_closure.select_convs
    by blast
  show "pf_labels_invar ?step"
    using assms unfolding pf_labels_invar_def congruence_closure.select_convs by argo
qed

lemma use_list_invar_merge3:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "\<not> lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "use_list_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "use_list_invar ?step") unfolding use_list_invar_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard)
  fix i j
  let ?new_u = "u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>1,
                   rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>2]"
  assume prems: "i < length l"
    "l ! i = i"
    "j < length (?new_u ! i)"
  have "length l = length u" "ufa_invar l" "a\<^sub>1 < length l" "a\<^sub>2 < length l"
    using assms unfolding cc_list_invar_def same_length_invar_def by auto
  then have "rep_of l a\<^sub>1 < length u" "rep_of l a\<^sub>2 < length u" 
    using rep_of_bound by force+
  have valid1: "use_list_valid_element (F a\<^sub>1 a\<^sub>2 \<approx> a) l (rep_of l a\<^sub>1)"
    using assms(2) by fastforce
  have valid2: "use_list_valid_element (F a\<^sub>1 a\<^sub>2 \<approx> a) l (rep_of l a\<^sub>2)"
    using assms(2) by fastforce
  consider "i \<noteq> rep_of l a\<^sub>1 \<and> i \<noteq> rep_of l a\<^sub>2"
    | "i = rep_of l a\<^sub>2 \<and> j = 0"
    | "i = rep_of l a\<^sub>2 \<and> j > 0"
    | "i = rep_of l a\<^sub>1 \<and> i \<noteq> rep_of l a\<^sub>2 \<and> j = 0"
    | "i = rep_of l a\<^sub>1 \<and> i \<noteq> rep_of l a\<^sub>2 \<and> j > 0"
    by fast
  then show "use_list_valid_element (?new_u ! i ! j) l i"
  proof(cases)
    case 1
    then show ?thesis using valid1 valid2 assms prems
      unfolding use_list_invar_def congruence_closure.select_convs
      by simp
  next
    case 2
    then have "?new_u ! i ! j = (F a\<^sub>1 a\<^sub>2 \<approx> a)"
      by (simp add: \<open>rep_of l a\<^sub>2 < length u\<close>)
    then show ?thesis using valid1 valid2 assms prems 2 \<open>rep_of l a\<^sub>2 < length u\<close>
      unfolding use_list_invar_def congruence_closure.select_convs
      by blast
  next
    case 3
    then have new_u: "?new_u ! i = (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>2"
      using \<open>length l = length u\<close> prems(1) by auto
    then have *: "j - 1 < length (u ! rep_of l a\<^sub>2)" using prems 
      by (metis "3" Suc_diff_1 length_Cons not_less_eq)
    have "?new_u ! i ! j = u ! i ! (j - 1)"
      by (metis "3" new_u nth_Cons_pos)
    then show ?thesis using valid1 valid2 assms prems 3
      unfolding use_list_invar_def congruence_closure.select_convs
      by (metis *)
  next
    case 4
    then have "?new_u ! i ! j = (F a\<^sub>1 a\<^sub>2 \<approx> a)"
      by (simp add: \<open>rep_of l a\<^sub>1 < length u\<close>)
    then show ?thesis using valid1 valid2 assms prems 4 \<open>rep_of l a\<^sub>2 < length u\<close>
      unfolding use_list_invar_def congruence_closure.select_convs
      by blast
  next
    case 5
    then have new_u: "?new_u ! i = (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>1"
      using \<open>length l = length u\<close> prems(1) by auto
    then have *: "j - 1 < length (u ! i)" using prems 
      by (metis "5" Suc_diff_1 Suc_less_eq length_Cons)
    then have "?new_u ! i ! j = u ! i ! (j - 1)"
      by (metis "5" new_u nth_Cons_pos)
    then show ?thesis using valid1 valid2 assms prems 5
      unfolding use_list_invar_def congruence_closure.select_convs
      by (metis *)
  qed
qed

lemma lookup_invar_merge3:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "\<not> lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "lookup_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "lookup_invar ?step") unfolding lookup_invar_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard)
  fix i j
  let ?new_t = "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  assume prems:"i < length l"
    "j < length l"
    "l ! i = i \<and> l ! j = j"
  show "lookup_valid_element ?new_t l i j"
  proof(cases "i = rep_of l a\<^sub>1 \<and> j = rep_of l a\<^sub>2")
    case True
    then have "?new_t ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)" 
      using assms(1) same_length_invar_def lookup_invar_def prems(1) prems(2) by fastforce
    then show ?thesis using assms 
      by (metis True congruence_closure.select_convs(1) valid_vars.simps(2))
  next
    case False
    then show ?thesis 
      using assms prems unfolding lookup_invar_def congruence_closure.select_convs
      by (metis update_lookup_unchanged)
  qed
next
  show "quadratic_table (update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a))"
    using assms unfolding lookup_invar_def 
    by (metis (no_types, lifting) congruence_closure.select_convs(3) length_list_update nth_list_update_eq nth_list_update_neq update_lookup.simps(1))
qed

lemma Congruence_Closure_fun_upd:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "\<not> lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "Congruence_Closure (representativeE \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])
          [rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>
 \<union> pending_set pe)
= Congruence_Closure (representativeE \<lparr>cc_list = l, use_list = u, lookup = t,
    pending = pe, proof_forest = pf, 
    pf_labels = pfl, input = ip\<rparr> \<union> pending_set pe \<union> {(F a\<^sub>1 a\<^sub>2 \<approx> a)})"
    (is "Congruence_Closure ?step
= Congruence_Closure ?base")
proof(induction rule: Congruence_Closure_eq)
  case (left eq)
  then consider a where 
    "eq = (a \<approx> rep_of l a)" "a < length l" "l ! a \<noteq> a" 
  | a' b' c c\<^sub>1 c\<^sub>2 where
    "eq = F a' b' \<approx> rep_of l c"
    "a' < length l"
    "b' < length l"
    "c < length l"
    "l ! a' = a'" "l ! b' = b'" 
    "a' \<noteq> rep_of l a\<^sub>1 \<or> b' \<noteq> rep_of l a\<^sub>2"
    "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  | c c\<^sub>1 c\<^sub>2 where
    "eq = F (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) \<approx> rep_of l c"
    "c < length l"
    "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) ! (rep_of l a\<^sub>1) ! (rep_of l a\<^sub>2) = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  | "eq \<in> pending_set pe"
    unfolding representativeE_def congruence_closure.select_convs by blast
  then show ?case 
  proof(cases)
    case 2
    then have "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) ! a' ! b' = t ! a' ! b'"
      using update_lookup_unchanged by metis
    then show ?thesis unfolding representativeE_def congruence_closure.select_convs 
      using base "2"(1-8) by auto
  next
    case 3
    have "length l = length t" "ufa_invar l" "a\<^sub>1 < length l" "a\<^sub>2 < length l"
      using assms unfolding cc_list_invar_def same_length_invar_def by auto
    then have "rep_of l a\<^sub>1 < length t" "rep_of l a\<^sub>2 < length (t ! rep_of l a\<^sub>1)" 
      using rep_of_bound assms unfolding lookup_invar_def by fastforce+
    then have entry: "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) ! rep_of l a\<^sub>1 ! rep_of l a\<^sub>2 = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)"
      by fastforce
    then have cc1: "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> Congruence_Closure ?base" using base by simp
    then have cc2: "(a\<^sub>1 \<approx> rep_of l a\<^sub>1) \<in> Congruence_Closure ?base" 
      "(a\<^sub>2 \<approx> rep_of l a\<^sub>2) \<in> Congruence_Closure ?base" 
      "(c \<approx> rep_of l c) \<in> Congruence_Closure ?base" 
      using \<open>a\<^sub>1 < length l\<close> \<open>a\<^sub>2 < length l\<close> 3(2)
      by (metis Congruence_Closure_split_rule a_eq_rep_of_a_in_CC(1) congruence_closure.select_convs(1))+
    from 3 entry have "a = c" by auto
    then show ?thesis using cc2 cc1 transitive2 transitive3 using "3"(1) by blast
  qed (simp_all add: representativeE_def base)
next
  case (right eq)
  then consider a where 
    "eq = (a \<approx> rep_of l a)" "a < length l" "l ! a \<noteq> a" 
  | a' b' c c\<^sub>1 c\<^sub>2 where
    "eq = F a' b' \<approx> rep_of l c"
    "a' < length l"
    "b' < length l"
    "c < length l"
    "l ! a' = a'" "l ! b' = b'" 
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  | "eq = (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  | "eq \<in> pending_set pe"
    unfolding representativeE_def congruence_closure.select_convs by blast
  then show ?case 
  proof(cases)
    case 2
    then have "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) ! a' ! b' = t ! a' ! b'"
      using assms(3) update_lookup_unchanged by (metis is_none_code(2) lookup_Some.simps(1))
    with 2 show ?thesis unfolding representativeE_def congruence_closure.select_convs 
      using base by simp
  next
    case 3
    have "length l = length t" "ufa_invar l" "a\<^sub>1 < length l" "a\<^sub>2 < length l"
      using assms unfolding cc_list_invar_def same_length_invar_def by auto
    then have "rep_of l a\<^sub>1 < length t" "rep_of l a\<^sub>2 < length (t ! rep_of l a\<^sub>1)" 
      using rep_of_bound assms unfolding lookup_invar_def by fastforce+
    then have entry: "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) ! rep_of l a\<^sub>1 ! rep_of l a\<^sub>2 = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)"
      by fastforce
    then show ?thesis using "3"(1) CC_lookup_entry_in_CC[of "\<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])
          [rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"] 
      unfolding  congruence_closure.select_convs 
      using assms lookup_invar_merge3 
      by (metis Congruence_Closure_split_rule \<open>ufa_invar l\<close> congruence_closure.select_convs(1) rep_of_bound rep_of_min valid_vars.simps(2))
  qed (simp_all add: representativeE_def base)
qed

lemma lookup_invar2_merge3:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "\<not> lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "lookup_invar2 \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "lookup_invar2 ?step") 
  unfolding lookup_invar2_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix a' b' c c\<^sub>1 c\<^sub>2
  let ?new_u = "u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a) # (u ! rep_of l a\<^sub>1),
                     rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a) # (u ! rep_of l a\<^sub>2)]"
  let ?new_t = "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  assume prems: "a' < length l" "b' < length l "
    "l ! a' = a'" "l ! b' = b'"
    "?new_t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  show "(\<exists>b\<^sub>1 b\<^sub>2 b.
           (F b\<^sub>1 b\<^sub>2 \<approx> b)
           \<in> set (?new_u ! a') \<and>
           rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
           rep_of l b\<^sub>2 = rep_of l c\<^sub>2 \<and>
   (b \<approx> c) \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 b.
           (F b\<^sub>1 b\<^sub>2 \<approx> b)
           \<in> set (?new_u ! b') \<and>
           rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
           rep_of l b\<^sub>2 = rep_of l c\<^sub>2 \<and>
   (b \<approx> c) \<in> Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe))"
  proof(cases "a' = rep_of l a\<^sub>1 \<and> b' = rep_of l a\<^sub>2")
    case True
    have valid: "rep_of l a\<^sub>1 < length t" "rep_of l a\<^sub>2 < length (t ! rep_of l a\<^sub>1)"
      "rep_of l a\<^sub>1 < length u" "rep_of l a\<^sub>2 < length u"
      using assms unfolding cc_list_invar_def same_length_invar_def lookup_invar_def
      by (simp add: rep_of_less_length_l)+
    with True have entry: "?new_t ! a' ! b' = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)" 
      unfolding update_lookup.simps by auto
    have "?new_u ! rep_of l a\<^sub>1 = (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>1" 
      "?new_u ! rep_of l a\<^sub>2 = (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>2" 
      using valid by (simp_all add: nth_list_update')
    then have "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> set (?new_u ! rep_of l a\<^sub>1)" 
      "(F a\<^sub>1 a\<^sub>2 \<approx> a) \<in> set (?new_u ! rep_of l a\<^sub>2)" 
      by auto
    then show ?thesis using reflexive 
      using True entry prems(5) by fastforce
  next
    case False
    then have *: "?new_t ! a' ! b' = t ! a' ! b'"
      using update_lookup_unchanged by metis
    have "k \<in> set (u ! j) \<Longrightarrow> k \<in> set (?new_u ! j)" for k j 
      apply(cases "j = rep_of l a\<^sub>1 \<or> j = rep_of l a\<^sub>2")
       apply (metis list.set_intros(2) nth_list_update_eq nth_list_update_neq nth_update_invalid)
      by (metis nth_list_update')
    then show ?thesis using assms unfolding lookup_invar2_def congruence_closure.select_convs
      by (metis (no_types, lifting) * prems)
  qed
qed

lemma use_list_invar2_merge3:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "\<not> lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "use_list_invar2 \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "use_list_invar2 ?step") 
  unfolding use_list_invar2_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard)
  fix a' c\<^sub>1 c\<^sub>2 c
  let ?new_u = "u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>1,
                 rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a) # u ! rep_of l a\<^sub>2]"
  let ?new_t = "update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  assume prems: "a' < length l" "l ! a' = a'"
    "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (?new_u ! a')"
  show "\<exists>b\<^sub>1 b\<^sub>2 b.
          lookup_entry ?new_t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
          (b \<approx> c) \<in>
Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)"
  proof(cases "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u ! a')")
    case True
    then obtain b\<^sub>1 b\<^sub>2 b where
      b: "lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and>
          (b \<approx> c) \<in>
Congruence_Closure ({a \<approx> rep_of l a |a. a < length l \<and> l ! a \<noteq> a} \<union> pending_set pe)" 
      using assms prems unfolding use_list_invar2_def by fastforce
    then have "lookup_entry t l c\<^sub>1 c\<^sub>2 = lookup_entry ?new_t l c\<^sub>1 c\<^sub>2"
      using assms(3) update_lookup_unchanged' by auto
    with b show ?thesis 
      by simp
  next
    case False
    then have c_a: "(F c\<^sub>1 c\<^sub>2 \<approx> c) = (F a\<^sub>1 a\<^sub>2 \<approx> a)" 
      by (metis nth_list_update' prems(3) set_ConsD)
    have valid: "rep_of l a\<^sub>1 < length t" "rep_of l a\<^sub>2 < length (t ! rep_of l a\<^sub>1)"
      "rep_of l a\<^sub>1 < length u" "rep_of l a\<^sub>2 < length u"
      using assms unfolding cc_list_invar_def same_length_invar_def lookup_invar_def
      by (simp add: rep_of_less_length_l)+
    then have "lookup_entry ?new_t l a\<^sub>1 a\<^sub>2 = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)" 
      by simp
    then show ?thesis 
      using c_a False reflexive by blast
  qed
qed

lemma cc_invar_merge3:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    (is "cc_invar ?base")
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a)
     (nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>)"
    "\<not> lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  shows "cc_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    (is "cc_invar ?step")
proof(rule conjI)+
  show "cc_list_invar ?step"
    using assms unfolding cc_list_invar_def by simp
  show "use_list_invar ?step"
    using assms use_list_invar_merge3 by blast
  show "lookup_invar ?step"
    using assms lookup_invar_merge3 by blast
  show "proof_forest_invar ?step"
    using assms unfolding proof_forest_invar_def by simp
  show "correctness_invar ?step"
    using assms Congruence_Closure_fun_upd 
    unfolding correctness_invar_def congruence_closure.select_convs
    by (smt (verit, del_insts) CC_union_correct Congruence_Closure_eq base insert_is_Un sup_commute)
  show "same_eq_classes_invar ?step"
    using assms unfolding same_eq_classes_invar_def by simp
  show "same_length_invar ?step (nr_vars ?step)"
    using assms unfolding same_length_invar_def by simp
  show "pending_invar ?step"
    using assms unfolding pending_invar_def by simp
  show "lookup_invar2 ?step"
    using assms lookup_invar2_merge3 by blast
  show "use_list_invar2 ?step"
    using assms use_list_invar2_merge3 by blast
  show "pf_labels_invar ?step"
    using assms unfolding pf_labels_invar_def congruence_closure.select_convs by argo
qed

end