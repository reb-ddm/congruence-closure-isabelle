theory CC_Invars
  imports CC_Abstraction
begin


subsection \<open>The invariants remain invariant after the loop of propagate\<close>

paragraph \<open>Invariants after a step in the loop\<close>

lemma lookup_invar_loop2:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
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
    with assms i_j nth_list_update_eq nth_update_invalid show ?thesis 
      unfolding congruence_closure.select_convs lookup_invar_def assms(2) update_lookup.simps
      by (smt (verit, best))
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
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
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
  assumes "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "pending_invar ?base")  
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "u1 = (F a\<^sub>1 a\<^sub>2 \<approx> aa)"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "aa < length l"
    "lookup_Some t l u1" "ufa_invar l"
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
      unfolding congruence_closure.select_convs * assms(3,4,5,6) link_to_lookup.simps  
      by simp
  next
    case (Suc nat)
    then have "pending ?step ! i = pending ?base ! (i - 1)"
      by simp
    then show ?thesis using assms unfolding pending_invar_def 
      using Suc i_j by force
  qed
qed


lemma inv2_loop1:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>"
    "ufa_invar l" "lookup_Some t l u1"
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
  have "l ! rep_of l a\<^sub>1 = rep_of l a\<^sub>1 \<and> l ! rep_of l a\<^sub>2 = rep_of l a\<^sub>2"
    "rep_of l a\<^sub>1 < length l \<and> rep_of l a\<^sub>2 < length l"
     apply (simp add: assms(2) assms(5) assms(6) rep_of_min)
    by (simp add: assms(2) assms(5) assms(6) rep_of_less_length_l)
  with assms entry_not_none 
  obtain c\<^sub>1 c\<^sub>2 c where entry: "lookup_entry t l a\<^sub>1 a\<^sub>2 = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)" 
    "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l" "rep_of l a\<^sub>1 = rep_of l c\<^sub>1 \<and> rep_of l a\<^sub>2 = rep_of l c\<^sub>2"
    unfolding lookup_invar_def congruence_closure.select_convs 
    by metis
  from entry CC_lookup_entry_in_CC 
  have f2: "Congruence_Closure ?base (F c\<^sub>1 c\<^sub>2 \<approx> c)" using base assms(4)
    by (metis Congruence_Closure_union \<open>l ! rep_of l a\<^sub>1 = rep_of l a\<^sub>1 \<and> l ! rep_of l a\<^sub>2 = rep_of l a\<^sub>2\<close> \<open>rep_of l a\<^sub>1 < length l \<and> rep_of l a\<^sub>2 < length l\<close> assms(1) congruence_closure.select_convs(1) congruence_closure.select_convs(3))
  from assms(1) have "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = link_to_lookup t l u1 # pe,
                 proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
    unfolding lookup_invar_def by simp
  with entry CC_lookup_entry_in_CC 
  have f2': "Congruence_Closure ?step (F c\<^sub>1 c\<^sub>2 \<approx> c)" using base assms(4) 
    by (metis Congruence_Closure_union \<open>l ! rep_of l a\<^sub>1 = rep_of l a\<^sub>1 \<and> l ! rep_of l a\<^sub>2 = rep_of l a\<^sub>2\<close> \<open>rep_of l a\<^sub>1 < length l \<and> rep_of l a\<^sub>2 < length l\<close> congruence_closure.select_convs(1) congruence_closure.select_convs(3))
  from entry CC_same_rep have a_c: "Congruence_Closure ?base (a\<^sub>1 \<approx> c\<^sub>1)"
    "Congruence_Closure ?base (a\<^sub>2 \<approx> c\<^sub>2)" 
    by (metis Congruence_Closure_union assms(5,6) congruence_closure.select_convs(1))+
  from entry CC_same_rep have c_a: "Congruence_Closure ?step (c\<^sub>1 \<approx> a\<^sub>1)" 
    "Congruence_Closure ?step (c\<^sub>2 \<approx> a\<^sub>2)" 
    by (metis Congruence_Closure_union assms(5,6) congruence_closure.select_convs(1))+
  have "u1 \<in> ?base"
    by simp
  have *: "u1 \<in> ?base"
    by simp
  then have f1: "Congruence_Closure ?base (F a\<^sub>1 a\<^sub>2 \<approx> a)" using * base assms(4)
    by simp
  show ?thesis 
  proof(rule Congruence_Closure_eq)
    fix eq


    assume "eq \<in> ?step"
    then consider
      (rep) c where "eq = c \<approx> rep_of l c" "c < length l" "l ! c \<noteq> c"
    | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
      "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    | (pending) "eq \<in> pending_set pe"
    | (new_pending) "eq \<in> pending_set [link_to_lookup t l u1]"
    | (urest) "eq \<in> set urest"
      unfolding representativeE_def using pending_set_union
      by fastforce
    then show "Congruence_Closure ?base eq"
    proof(cases)
      case new_pending

      with new_pending assms(4) entry have eq: "eq = a \<approx> c" 
        by auto
      with eq f1 f2 a_c monotonic show ?thesis 
        by simp
    qed (simp_all add: base representativeE_def)
  next
    fix eq' 
    assume  "eq' \<in> ?base"
    then consider
      (rep) c where "eq' = c \<approx> rep_of l c" "c < length l" "l ! c \<noteq> c"
    | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq' = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
      "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    | (pending) "eq' \<in> pending_set pe"
    | (new_pending) "eq' = u1"
    | (urest) "eq' \<in> set urest" 
      unfolding representativeE_def congruence_closure.select_convs
      by fastforce
    then show "Congruence_Closure ?step eq'"
    proof(cases)
      case pending
      with pending_set_union' have "eq' \<in> pending_set (link_to_lookup t l u1 # pe)"
        by (metis append_Cons append_eq_append_conv2 )
      with base show ?thesis 
        using Congruence_Closure_union by blast
    next
      case new_pending
      with base show ?thesis 
        using f1 f2 c_a assms(4) sorry
    qed (simp_all add: base representativeE_def)
  qed
qed

lemma inv2_loop2:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip\<rparr>" "length l = length t"
    "ufa_invar l" "\<not> lookup_Some t l u1"
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
    (rep) c where "eq = c \<approx> rep_of l c" "c < length l" "l ! c \<noteq> c"
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
  then show "Congruence_Closure ?base eq"
  proof(cases)
    case lookup
    then have "update_lookup t l u1 ! a' ! b' = t ! a' ! b'"
      by (metis assms(5) lookup(8) update_lookup_unchanged)
    with lookup have "eq \<in> (representativeE
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
          input = ip\<rparr>)" unfolding representativeE_def congruence_closure.select_convs 
      by auto
    with assms lookup show ?thesis unfolding representativeE_def congruence_closure.select_convs
      using Congruence_Closure_union base by presburger
  next
    case new_lookup
    from assms have "length t = length l " "length (t ! a') = length l" 
       apply simp using assms new_lookup(2) unfolding lookup_invar_def by auto
    with new_lookup have lookup_entry: "update_lookup t l u1 ! a' ! b' = Some (F a\<^sub>1 a\<^sub>2 \<approx> a)"
      unfolding assms(5) update_lookup.simps  
      by fastforce
    then have cc1: "Congruence_Closure ?base (F a\<^sub>1 a\<^sub>2 \<approx> a)" using base assms(5)
      by simp
    have "c = a" 
      using lookup_entry new_lookup(7) by simp
    with new_lookup(8,4) a_eq_rep_of_a_in_CC assms(6,7)
    have cc2: "Congruence_Closure ?base (a\<^sub>1 \<approx> a')" "Congruence_Closure ?base (a\<^sub>2 \<approx> b')" 
      "Congruence_Closure ?base (c \<approx> rep_of l c)" 
      by (metis Congruence_Closure_union congruence_closure.select_convs(1))+
    then have "Congruence_Closure ?base (F a' b' \<approx> c)" using assms(5)
      by (metis \<open>c = a\<close> cc1 transitive3)
    then show ?thesis 
      using cc2(3) new_lookup(1) transitive2 by blast
  qed (simp_all add: base representativeE_def)
next
  fix eq' 
  assume  "eq' \<in> ?base"
  then consider
    (rep) c where "eq' = c \<approx> rep_of l c" "c < length l" "l ! c \<noteq> c"
  | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq' = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
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
  then show "Congruence_Closure ?step eq'"
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
    with assms have "length t = length l " "length (t ! rep_of l a\<^sub>1) = length l" 
       apply simp using assms rep_of_less_length_l unfolding lookup_invar_def 
      by fastforce
    with assms(5) have "lookup_entry (update_lookup t l u1) l a\<^sub>1 a\<^sub>2 = Some u1" 
      by (simp add: assms(3) assms(6) assms(7) rep_of_less_length_l)
    with assms have "(F (rep_of l a\<^sub>1) (rep_of l a\<^sub>2) \<approx> rep_of l a) \<in> representativeE
       \<lparr>cc_list = l, use_list = u[rep_b := u1 # u ! rep_b], lookup = update_lookup t l u1,
          pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      unfolding representativeE_def congruence_closure.select_convs 
      using rep_of_less_length_l rep_of_min by fastforce
    then show ?thesis using CC_F_rep_of_a_imp_F_a base 
      by (simp add: Congruence_Closure_union assms(5) assms(6) assms(7) assms(8) new_pending)      
  qed (simp_all add: base representativeE_def)
qed


lemma in_set_Cons_use_list:
  assumes "rep_b' < length u" 
"i \<noteq> rep_of l a " "eq \<in> set (u ! i) "
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
  assumes "ufa_invar l" 
    "a < length l" "b < length l" 
    "use_list_invar
\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
"
    "lookup_invar
\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"

"lookup_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
     (u1' # urest')"
(is "lookup_invar2' ?base (u1' # urest')")
"rep_of l a \<noteq> rep_of l b"
"lookup_Some t (ufa_union l a b) u1'"
"u1' = (F d\<^sub>1 d\<^sub>2 \<approx> d)" "d\<^sub>1 < length l" "d\<^sub>2 < length l" 
shows "lookup_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
        pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr> urest'"
  (is "lookup_invar2' ?loop1 urest'")
  unfolding lookup_invar2'_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  have ufa_invar_mini_step: "ufa_invar (ufa_union l a b)" 
    by (simp add: assms(1,2,3) ufa_union_invar)
  have CC_loop1: "Congruence_Closure
   (representativeE ?base \<union> pending_set pe \<union> set (u1' # urest'))
= Congruence_Closure
            (representativeE ?loop1 \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe)
\<union> set urest')" 
    using inv2_loop1 assms 
    by (metis length_list_update ufa_invar_mini_step)
  fix a' b' c c\<^sub>1 c\<^sub>2
  assume prems: "a' < length (ufa_union l a b)"
    "b' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "ufa_union l a b ! b' = b'"
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)" 
  from prems have *: "l ! a' = a'" "l ! b' = b'" "a' < length l" "b' < length l" 
    using assms(1-3) ufa_union_root apply blast+
    using prems by auto
  with prems assms have "a' \<noteq> rep_of l a" "b' \<noteq> rep_of l a" 
    by (metis nth_list_update_eq)+
  with assms * prems obtain b\<^sub>1 b\<^sub>2 cb a\<^sub>1 a\<^sub>2 ca where use_list: "F a\<^sub>1 a\<^sub>2 \<approx> ca \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?base \<union>
             pending_set (pe) \<union>
             set (u1' # urest'))
            (ca \<approx> c) 
       ""
           F b\<^sub>1 b\<^sub>2 \<approx> cb \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?base \<union>
             pending_set (pe) \<union>
             set (u1' # urest'))
            (cb \<approx> c)" unfolding lookup_invar2'_def congruence_closure.select_convs
    by blast
  with assms * use_list_invar_less_n_in_set use_list
    prems * lookup_invar_less_n length_list_update
  have length_b: "b\<^sub>1 < length l" "b\<^sub>2 < length l" "cb < length l" "a\<^sub>1 < length l" "a\<^sub>2 < length l" 
    "ca < length l" "c\<^sub>1 < length l" "c\<^sub>2 < length l"
    by metis+
  with rep_of_ufa_union_invar assms(1,2,3) use_list
  have "rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
    "rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    " rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
    "rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    by metis+
  with use_list length_b have "(F a\<^sub>1 a\<^sub>2 \<approx> ca) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?loop1 \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe) \<union>
      set urest')
            (ca \<approx> c) 
       ""
           (F b\<^sub>1 b\<^sub>2 \<approx> cb) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?loop1 \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe) \<union>
      set urest')
            (cb \<approx> c)"
    unfolding CC_loop1 
    by blast+
  then show "(\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                 pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr> \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe) \<union>
             set urest')
            (ba \<approx> c)) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                 pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr> \<union>
             pending_set (link_to_lookup t (ufa_union l a b) u1' # pe) \<union>
             set urest')
            (ba \<approx> c))"
    using assms by auto
qed

lemma lookup_invar2_loop2:
  assumes "ufa_invar l" 
    "a < length l" "b < length l" 
    "use_list_invar
\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
"
    "lookup_invar
\<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"

"lookup_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
        pf_labels = pfl, input = ip\<rparr>
     (u1' # urest')"
(is "lookup_invar2' ?base (u1' # urest')")
"rep_of l a \<noteq> rep_of l b"
"\<not> lookup_Some t (ufa_union l a b) u1'"
"u1' = (F d\<^sub>1 d\<^sub>2 \<approx> d)" "d\<^sub>1 < length l" "d\<^sub>2 < length l"  "d < length l"

"length l = length t"
"rep_b' < length u"
 "(rep_of l d\<^sub>1 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l d\<^sub>1) d\<^sub>1 d\<^sub>2 d (u1' # urest'))

\<and> 
(rep_of l d\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l d\<^sub>2) d\<^sub>1 d\<^sub>2 d (u1' # urest'))
"
"rep_of l a = rep_of l d\<^sub>1 \<or> rep_of l a = rep_of l d\<^sub>2"
"rep_b' = rep_of l b"
shows "lookup_invar2'
     \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr> urest'"
(is "lookup_invar2' ?loop2 urest'")
  unfolding lookup_invar2'_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  have ufa_invar_mini_step: "ufa_invar (ufa_union l a b)" 
    by (simp add: assms(1,2,3) ufa_union_invar)
  have CC_loop2: "Congruence_Closure
   (representativeE ?base \<union> pending_set pe \<union> set (u1' # urest'))
= Congruence_Closure
            (representativeE ?loop2 \<union>
             pending_set pe
\<union> set urest')" 
    using inv2_loop2 assms 
    by (metis length_list_update ufa_invar_mini_step)
  fix a' b' c c\<^sub>1 c\<^sub>2
  assume prems: "a' < length (ufa_union l a b)"
    "b' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "ufa_union l a b ! b' = b'"
    "update_lookup t (ufa_union l a b) u1' ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)" 
  from prems have *: "l ! a' = a'" "l ! b' = b'" "a' < length l" "b' < length l" 
    using assms(1-3) ufa_union_root apply blast+
    using prems by auto
  with prems assms have "a' \<noteq> rep_of l a" "b' \<noteq> rep_of l a" 
    by (metis nth_list_update_eq)+
  have "update_lookup t (ufa_union l a b) u1' ! a' ! b' \<noteq> None" 
    using prems by fast
  with assms(5) prems obtain k\<^sub>1 k\<^sub>2 k where 
"update_lookup t (ufa_union l a b) u1' ! a' ! b' = Some (F k\<^sub>1 k\<^sub>2 \<approx> k)" 
     "rep_of (ufa_union l a b) k\<^sub>1 = a'" "rep_of (ufa_union l a b) k\<^sub>2 = b'"
    unfolding lookup_invar_def congruence_closure.select_convs     
    by (smt (verit, ccfv_threshold) "*"(3,4) assms(13,9) nth_list_update_eq update_lookup.simps(1) update_lookup_unchanged)
  then have a_b: "rep_of (ufa_union l a b) c\<^sub>1 = a'" "rep_of (ufa_union l a b) c\<^sub>2 = b'"
    using prems(5) by auto
  show "(\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! a') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'],
                 lookup = update_lookup t (ufa_union l a b) u1', pending = pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr> \<union>
             pending_set pe \<union>
             set urest')
            (ba \<approx> c)) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'],
                 lookup = update_lookup t (ufa_union l a b) u1', pending = pe, proof_forest = pf,
                 pf_labels = pfl, input = ip\<rparr> \<union>
             pending_set pe \<union>
             set urest')
            (ba \<approx> c))"
proof(cases "update_lookup t (ufa_union l a b) u1' ! a' ! b' = t ! a' ! b'")
  case True
  with assms * prems obtain b\<^sub>1 b\<^sub>2 cb a\<^sub>1 a\<^sub>2 ca where use_list: "F a\<^sub>1 a\<^sub>2 \<approx> ca \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?base \<union>
             pending_set (pe) \<union>
             set (u1' # urest'))
            (ca \<approx> c) 
       ""
           F b\<^sub>1 b\<^sub>2 \<approx> cb \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?base \<union>
             pending_set pe \<union>
             set (u1' # urest'))
            (cb \<approx> c)" unfolding lookup_invar2'_def congruence_closure.select_convs True
    by blast
  with assms * use_list_invar_less_n_in_set use_list
    prems True * lookup_invar_less_n length_list_update
  have length_b: "b\<^sub>1 < length l" "b\<^sub>2 < length l" "cb < length l" "a\<^sub>1 < length l" "a\<^sub>2 < length l" 
    "ca < length l" "c\<^sub>1 < length l" "c\<^sub>2 < length l"
    by metis+
  with rep_of_ufa_union_invar assms(1,2,3) use_list
  have "rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
    "rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    " rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1"
    "rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    by metis+
  with use_list length_b have *: "(F a\<^sub>1 a\<^sub>2 \<approx> ca) \<in> set (u ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?loop2 \<union>
             pending_set pe \<union>
      set urest')
            (ca \<approx> c) 
       ""
           (F b\<^sub>1 b\<^sub>2 \<approx> cb) \<in> set (u ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              ?loop2 \<union>
             pending_set pe \<union>
      set urest')
            (cb \<approx> c)"
    unfolding CC_loop2
    by blast+
  have "i \<noteq> rep_of l a 
\<Longrightarrow> eq \<in> set (u ! i) \<Longrightarrow> eq \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! i)"
    for eq i using assms(14) in_set_Cons_use_list 
    by fast 
  with * show ?thesis
    using \<open>a' \<noteq> rep_of l a\<close> \<open>b' \<noteq> rep_of l a\<close> by blast
next
  case False
  with prems(5) have u1': "u1' = (F c\<^sub>1 c\<^sub>2 \<approx> c)" 
    unfolding assms(9) update_lookup.simps by (metis nth_list_update' option.inject)
  have u1_in_set: "F c\<^sub>1 c\<^sub>2 \<approx> c \<in> set (u[rep_b' := u1' # u ! rep_b'] ! rep_of l b)" 
    using assms(14) u1' assms(17) assms(9) assms(17) by auto
  have eq_rep_l_b: "eq \<in> set (u ! rep_of l b)
\<Longrightarrow> eq \<in> set (u[rep_b' := u1' # u ! rep_b'] ! rep_of l b)" for eq 
    by (metis assms(14) assms(7) in_set_Cons_use_list)
have eq_not_rep_l_b: "rep_of l b \<noteq> kk \<Longrightarrow> eq \<in> set (u ! kk)
\<Longrightarrow> eq \<in> set (u[rep_b' := u1' # u ! rep_b'] ! kk)" for eq kk
    by (metis assms(14) assms(7) in_set_Cons_use_list)
  consider "rep_of l a = rep_of l c\<^sub>1" "rep_of l a \<noteq> rep_of l c\<^sub>2"
    | "rep_of l a = rep_of l c\<^sub>1" "rep_of l a = rep_of l c\<^sub>2"
    | "rep_of l a \<noteq> rep_of l c\<^sub>1" "rep_of l a = rep_of l c\<^sub>2"
    using \<open>u1' = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> assms(16) assms(9) by fastforce
  then show ?thesis proof(cases)
    case 1
    with a_b have "a' = rep_of l b"
      using \<open>u1' = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> assms ufa_union_aux by simp
    have "(\<exists>b\<^sub>1 b\<^sub>2 ba.
        (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_b' := u1' # u ! rep_b'] ! a') \<and>
        rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
        rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
        Congruence_Closure
         (representativeE
           \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'],
              lookup = update_lookup t (ufa_union l a b) u1', pending = pe, proof_forest = pf,
              pf_labels = pfl, input = ip\<rparr> \<union>
          pending_set pe \<union>
          set urest')
         (ba \<approx> c))" 
      by (smt (verit) "1"(2) CC_loop2 Congruence_Closure.symmetric \<open>a' = rep_of l b\<close> assms(15) assms(9) congruence_closure.select_convs(4) equation.inject(2) transitive1 u1' u1_in_set)
    then show ?thesis 
      by (smt (z3) CC_loop2 \<open>a' = rep_of l b\<close> a_b assms(1) assms(11) assms(15) assms(2) assms(3) assms(9) congruence_closure.select_convs(1) congruence_closure.select_convs(2) congruence_closure.select_convs(4) eq_not_rep_l_b equation.inject(2) option.inject prems(5) u1' ufa_union_aux)
  next
    case 2
    then show ?thesis 
      by (metis Congruence_Closure.reflexive a_b(1) a_b(2) assms(1) assms(10) assms(11) assms(3) assms(9) equation.inject(2) u1' u1_in_set ufa_union_aux)
  next
    case 3
    then show ?thesis 
      by (smt (verit, best) CC_loop2 Congruence_Closure.reflexive \<open>rep_of (ufa_union l a b) k\<^sub>1 = a'\<close> \<open>rep_of (ufa_union l a b) k\<^sub>2 = b'\<close> \<open>update_lookup t (ufa_union l a b) u1' ! a' ! b' = Some (F k\<^sub>1 k\<^sub>2 \<approx> k)\<close> assms(1) assms(10) assms(11) assms(15) assms(3) assms(9) congruence_closure.select_convs(1) congruence_closure.select_convs(2) congruence_closure.select_convs(4) eq_not_rep_l_b equation.inject(2) option.inject prems(5) u1' u1_in_set ufa_union_aux)
  qed
qed
qed

lemma lookup_invar2_prems_loop1:
  assumes "\<forall>eq'\<in>set (u1' # urest').
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c (u1' # urest')) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c (u1' # urest'))"
"lookup_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>"
"ufa_invar (ufa_union l a b)" "lookup_Some t (ufa_union l a b) u1'"
"u1' = (F a\<^sub>1 a\<^sub>2 \<approx> aa)" "a\<^sub>1 < length (ufa_union l a b)" "a\<^sub>2 < length (ufa_union l a b)"
  shows "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
               pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
               input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c urest') \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
               pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
               input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c urest')"
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
               Congruence_Closure
                (representativeE
                  \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
                 pending_set pe \<union>
                 set (u1' # urest'))
                (ba \<approx> c))) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           (\<exists>b\<^sub>1 b\<^sub>2 ba.
               (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>2) \<and>
               rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
               rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
               Congruence_Closure
                (representativeE
                  \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
                 pending_set pe \<union>
                 set (u1' # urest'))
                (ba \<approx> c)))" unfolding congruence_closure.select_convs
    by fast
  from inv2_loop1[OF assms(2,3,4,5,6,7)] have "Congruence_Closure
                (representativeE
                  \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
                 pending_set pe \<union>
                 set (u1' # urest')) = Congruence_Closure
                    (representativeE
                      \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                         pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
                         pf_labels = pfl, input = ip\<rparr> \<union>
                     pending_set (link_to_lookup t (ufa_union l a b) u1' # pe) \<union>
                     set urest')"
    by simp
  then have "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>1) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                   Congruence_Closure
                    (representativeE
                      \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                         pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
                         pf_labels = pfl, input = ip\<rparr> \<union>
                     pending_set (link_to_lookup t (ufa_union l a b) u1' # pe) \<union>
                     set urest')
                    (ba \<approx> c))) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>2) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                   Congruence_Closure
                    (representativeE
                      \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                         pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf,
                         pf_labels = pfl, input = ip\<rparr> \<union>
                     pending_set (link_to_lookup t (ufa_union l a b) u1' # pe) \<union>
                     set urest')
                    (ba \<approx> c)))"
    using "*" by presburger
  then show "\<exists>c\<^sub>1 c\<^sub>2 c.
              eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                   pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
                   input = ip\<rparr>
                (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c urest') \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t,
                   pending = link_to_lookup t (ufa_union l a b) u1' # pe, proof_forest = pf, pf_labels = pfl,
                   input = ip\<rparr>
                (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c urest')" 
    unfolding congruence_closure.select_convs by blast
qed


lemma lookup_invar2_prems_loop2:
  assumes "\<forall>eq'\<in>set (u1' # urest').
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c (u1' # urest')) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c (u1' # urest'))"

"lookup_invar \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>"
"length (ufa_union l a b) = length t"
"ufa_invar (ufa_union l a b)" 
 "\<not> lookup_Some t (ufa_union l a b) u1'"
"u1' = (F a\<^sub>1 a\<^sub>2 \<approx> aa)" "a\<^sub>1 < length (ufa_union l a b)" "a\<^sub>2 < length (ufa_union l a b)"
"aa < length (ufa_union l a b)"
"rep_b' < length u"
  shows "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c urest') \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c urest')"
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
               Congruence_Closure
                (representativeE
                  \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
                 pending_set pe \<union>
                 set (u1' # urest'))
                (ba \<approx> c))) \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           (\<exists>b\<^sub>1 b\<^sub>2 ba.
               (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u ! rep_of l c\<^sub>2) \<and>
               rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
               rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
               Congruence_Closure
                (representativeE
                  \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
                 pending_set pe \<union>
                 set (u1' # urest'))
                (ba \<approx> c)))" unfolding congruence_closure.select_convs
    by fast
  from inv2_loop2[OF assms(2,3,4,5,6,7,8,9)] have CC_step: "Congruence_Closure
                (representativeE
                  \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe,
                     proof_forest = pf, pf_labels = pfl, input = ip\<rparr> \<union>
                 pending_set pe \<union>
                 set (u1' # urest')) = Congruence_Closure
                    (representativeE
                      \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr> \<union>
                     pending_set pe \<union>
                     set urest')"
    by simp
  have "i \<noteq> rep_of l a 
\<Longrightarrow> eq \<in> set (u ! i) \<Longrightarrow> eq \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! i)"
    for eq i 
    using assms(10) in_set_Cons_use_list by fast
  then have "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! rep_of l c\<^sub>1) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                   Congruence_Closure
                    (representativeE
                      \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr> \<union>
                     pending_set pe \<union>
                     set urest')
                    (ba \<approx> c))) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               (\<exists>b\<^sub>1 b\<^sub>2 ba.
                   (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set ((u[rep_b' := u1' # u ! rep_b']) ! rep_of l c\<^sub>2) \<and>
                   rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
                   rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
                    Congruence_Closure
                    (representativeE
                      \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr> \<union>
                     pending_set pe \<union>
                     set urest')
                    (ba \<approx> c)))"
    using "*" CC_step 
    by metis
  then show "\<exists>c\<^sub>1 c\<^sub>2 c.
              eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>
                (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c urest') \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u[rep_b' := u1' # u ! rep_b'], 
lookup = update_lookup t (ufa_union l a b) u1', 
pending = pe, proof_forest = pf,
       pf_labels = pfl, input = ip\<rparr>
                (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c urest')" 
    unfolding congruence_closure.select_convs by blast
qed

paragraph \<open>Invariants after the entire loop\<close>

lemma lookup_invar_loop: 
  assumes "ufa_invar l"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "lookup_invar ?base") 
    "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
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
    with 1 have lookup_invar: "lookup_invar \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe',
                 proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" unfolding lookup_invar_def
      by auto
    from 1 have use_list_invar: "use_list_invar \<lparr>cc_list = l', use_list = u', lookup = t', pending = link_to_lookup t' l' u1' # pe',
                 proof_forest = pf', pf_labels = pfl', input = ip'\<rparr>" unfolding use_list_invar_def
      by auto
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
      unfolding pending_invar_def 
      by fastforce
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
    "lookup_invar2' \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> u_a"

    "\<forall> eq' \<in> set u_a . 
(\<exists> c\<^sub>1 c\<^sub>2 c . eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and> c\<^sub>1 < length l \<and> c\<^sub>2 < length l \<and> c < length l
\<and> (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c u_a)

\<and> 
(rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u, 
    lookup = t, 
    pending = pe,
    proof_forest = pf, 
    pf_labels = pfl, 
    input = ip\<rparr> (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c u_a)
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
      (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c (u1' # urest')) \<and>
    (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
     contains_similar_equation
      \<lparr>cc_list = ufa_union l a b, use_list = u, lookup = t, pending = pe, proof_forest = pf,
         pf_labels = pfl, input = ip\<rparr>
      (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c (u1' # urest'))" 
      by simp
 from 1(16) obtain k\<^sub>1 k\<^sub>2 k where u1'': "u1' = (F k\<^sub>1 k\<^sub>2 \<approx> k)"
    "k\<^sub>1 < length l" "k\<^sub>2 < length l" "k < length l" 
"rep_of l k\<^sub>1 = rep_of l a \<or> rep_of l k\<^sub>2 = rep_of l a"
    by auto
    have "rep_b' < length u" " rep_b' = rep_of l b "
      "rep_of l a = rep_of l c\<^sub>1 \<or> rep_of l a = rep_of l c\<^sub>2"
      apply (simp add: "1.prems"(11) "1.prems"(8))
       apply (simp add: "1.prems"(13))
      using u1'' 
      using u1'(1) by force
    with lookup_invar2_loop2[OF assms(1,2,3) 1(11,12,7) assms(4) lookup_None u1'(1) c_length 1(14)
_ *] 1(10,13) eq have 
      2: "lookup_invar2' ?loop2 urest'"  
      by blast
    have *: "ufa_invar (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)"
      by (simp_all add: c_length assms(1) assms(2) assms(3) ufa_union_invar)
    from lookup_invar2_prems_loop2[OF 1(8,12) _ _ lookup_None u1'(1,2,3,4)] eq  have 6: "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop2
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c urest') \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop2
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c urest')"
      using 1(14,10) "1.prems"(11) *(1) ufa_union_invar length_list_update 
      by simp
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
    with lookup_invar2_loop1[OF assms(1,2,3) 1(11,12,7)] 1 u1' have 
      2: "lookup_invar2' ?loop1 urest'" using c_length 
      by blast
    have *: "ufa_invar (ufa_union l a b)" "c\<^sub>1 < length (ufa_union l a b)" "c\<^sub>2 < length (ufa_union l a b)"
      by (simp_all add: c_length assms(1) assms(2) assms(3) ufa_union_invar)
   
    with lookup_invar2_prems_loop1[OF 1(8,12) *(1) lookup_Some u1'(1) *(2,3)] have 6: "\<forall>eq'\<in>set urest'.
       \<exists>c\<^sub>1 c\<^sub>2 c.
          eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c) \<and>
          c\<^sub>1 < length l \<and>
          c\<^sub>2 < length l \<and>
          c < length l \<and>
          (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop1
            (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c urest') \<and>
          (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
           contains_similar_equation
            ?loop1
            (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c urest')"
      using eq by fastforce
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
have " \<forall>j<length urest'. use_list_valid_element (urest' ! j) l (rep_of l a) " using 1(16) 
      by auto
    with 1(1)[OF 5(1) assms(1,2,3,4) 2 6 3] 1(2-) 2 3 4 lookup_Some show ?thesis 
      by auto
  qed
qed simp


lemma inv2_loop: 
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
    from invars u1' "1.prems" inv2_loop1 True 
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
      set (u1' # urest'))" unfolding cc_list_invar_def 
      by simp
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
      using "*" False unfolding cc_list_invar_def by force
    from "1.prems" inv2_loop2 u1' False have "Congruence_Closure
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

subsection \<open>The invariants remain invariant after propagate\<close>

paragraph \<open>Invariants before entering the propagate_loop.\<close>

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
  then have "cc_list ?base ! i = i \<and> cc_list ?base ! j = j" 
    by (metis assms(2) assms(3) assms(4) congruence_closure.select_convs(1) ufa_union_root)
  with assms i_j show "lookup_valid_element (lookup ?step) (cc_list ?step) i j"
    unfolding lookup_invar_def congruence_closure.select_convs
    using length_list_update list_update_same_conv nth_list_update rep_of_fun_upd' rep_of_idem 
    by (smt (verit, del_insts))
next
  show "quadratic_table (lookup ?step)"
    using assms lookup_invar_def by auto
qed

lemma use_list_invar_mini_step:
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
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

lemma inv2_mini_step:
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
  shows "Congruence_Closure (representativeE 
\<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq2, 
    input = ip\<rparr>
\<union> pending_set pe
\<union> set (u ! rep_of l a)) = 
Congruence_Closure 
(representativeE 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq2 # pe), 
proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
\<union> pending_set (eq2 # pe))"
    (is "Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a)) = ?right")
proof(induction rule: Congruence_Closure_eq)
  case (left eq)
  then consider
    (rep) c where "eq = c \<approx> rep_of (ufa_union l a b) c"
    "c < length (ufa_union l a b)" "(ufa_union l a b) ! c \<noteq> c"
    "rep_of l a \<noteq> rep_of l c"
  | (new_rep) c where "eq = c \<approx> rep_of (ufa_union l a b) c"
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
  then show ?case proof(cases)
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
    then have *: "Congruence_Closure (representativeE ?base)
     (c \<approx> (rep_of l c))"
      "Congruence_Closure (representativeE ?base)
     ((rep_of l a) \<approx> a)"
      "Congruence_Closure (representativeE ?base)
     (b \<approx> (rep_of l b))" using a_eq_rep_of_a_in_CC new_rep congruence_closure.select_convs(1) assms(2,3)
      by metis+
    from assms have "valid_vars_pending eq2 (cc_list ?base)"
      unfolding pending_invar_def by (metis assms(8) congruence_closure.select_convs(1) pending_invar_Cons)
    with pending_a_b_in_Congruence_Closure' 
    have **: "Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe))
     (a \<approx> b)"
      by (simp add: assms(4) assms(5))
    with * Congruence_Closure_union have "Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe))
     (c \<approx> a)" 
      by (metis new_rep(4) transitive1)
    with * ** Congruence_Closure_union have "Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe))
     (c \<approx> b)" by (metis transitive1)
    with * Congruence_Closure_union rep_union new_rep show ?thesis 
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
    have ***: "Congruence_Closure (representativeE ?base \<union> pending_set (eq2 # pe)) (a \<approx> b)" 
      using assms(4) assms(5) assms(8) pending_invar_Cons by force
    from assms * new_lookup have "(F a' b' \<approx> rep_of l c) \<in> (representativeE ?base)" 
      unfolding representativeE_def congruence_closure.select_convs by simp
    have "rep_of l (rep_of l c) = rep_of l a" 
      by (simp add: assms(1) assms(2) new_lookup(8) rep_of_idem)
    then have "Congruence_Closure (representativeE ?base) (rep_of l c \<approx> a)" 
      "Congruence_Closure (representativeE ?base) (b \<approx> rep_of l b)" 
      using CC_same_rep 
       apply (simp add: assms(1) assms(2) new_lookup(8) rep_of_less_length_l)
      by (simp add: CC_same_rep assms(1) assms(3) rep_of_idem rep_of_less_length_l)
    with new_lookup ** CC_rep_of_a_imp_a have "Congruence_Closure
     (representativeE ?base \<union> pending_set (eq2 # pe))
     (rep_of l c \<approx> b)" 
      by (meson "***" Congruence_Closure_split_rule transitive1)
    then have "Congruence_Closure
     (representativeE ?base \<union> pending_set (eq2 # pe))
     (rep_of l c \<approx> rep_of (ufa_union l a b) c)" 
      by (metis "**" Congruence_Closure_union \<open>Congruence_Closure (representativeE \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq2 # pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) b \<approx> rep_of l b\<close> transitive1)
    then show ?thesis 
      by (metis Congruence_Closure_union \<open>F a' b' \<approx> rep_of l c \<in> representativeE \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq2 # pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>\<close> base new_lookup(1) transitive2)
  next
    case urest
    have "rep_of l a < length l" "l ! (rep_of l a) = rep_of l a" 
       apply (simp add: assms(1) assms(2) rep_of_less_length_l)
      by (simp add: assms(1) assms(2) rep_of_min)
    with assms urest show ?thesis unfolding  congruence_closure.select_convs 
      sorry
  qed 
next
  case (right eq)
  then consider
    (rep) c where "eq = c \<approx> rep_of l c" "c < length l" "l ! c \<noteq> c"
  | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
    "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  | (new_eq) "eq \<in> pending_set [eq2]"
  | (pending) "eq \<in> pending_set pe"
    unfolding representativeE_def congruence_closure.select_convs 
    using pending_set_Cons
    by blast
  then show ?case proof(cases)
    case rep
    have "rep_of (ufa_union l a b) c = rep_of (ufa_union l a b) (rep_of l c)" 
      by (simp add: assms(1) assms(2) assms(3) rep(2) rep_of_idem rep_of_less_length_l ufa_union_aux)
    then have "Congruence_Closure (representativeE ?step) (c \<approx> rep_of l c)"
      using CC_same_rep using assms(1) rep(2) rep_of_less_length_l by auto
    then show ?thesis using Congruence_Closure_union rep(1) by blast
  next
    case lookup
    then show ?thesis proof(cases "a' = rep_of l a \<or> b' = rep_of l a")
      case True
      with assms lookup have  "(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set (u ! rep_of l a)"
        unfolding lookup_invar2'_def congruence_closure.select_convs 
        sorry
      then have cc1: "Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))
(F c\<^sub>1 c\<^sub>2 \<approx> c)"
        using Congruence_Closure_split_rule by blast
      from assms lookup have "rep_of (ufa_union l a b) c\<^sub>1 = rep_of (ufa_union l a b) a'"
        "c\<^sub>1 < length l" "rep_of (ufa_union l a b) c\<^sub>2 = rep_of (ufa_union l a b) b'"
        "c\<^sub>2 < length l"
        unfolding lookup_invar_def congruence_closure.select_convs 
        by (metis equation.inject(2) option.discI option.inject rep_of_iff ufa_union_aux)+
      with CC_same_rep lookup have cc2: "Congruence_Closure (representativeE ?step)
(c\<^sub>1 \<approx> a')"
        "Congruence_Closure (representativeE ?step)
(c\<^sub>2 \<approx> b')" 
        by force+
      from cc1 cc2 have *: "Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))
(F a' b' \<approx> c)" 
        using transitive3 Congruence_Closure_union by blast 
      have "rep_of (ufa_union l a b) (rep_of l c) = rep_of (ufa_union l a b) c"
        by (simp add: assms(1) assms(2) assms(3) lookup(4) rep_of_idem rep_of_less_length_l ufa_union_aux)
      with CC_same_rep
      have "Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))
(c \<approx> rep_of l c)" 
        using assms(1) lookup(4) rep_of_less_length_l Congruence_Closure_union 
        by simp
      with lookup transitive2 * show ?thesis  
        by presburger
    next
      case False
      with lookup have *: "(ufa_union l a b) ! a' = a'" "(ufa_union l a b) ! b' = b'" 
        by auto
      have "rep_of (ufa_union l a b) (rep_of l c) = rep_of (ufa_union l a b) c"
        by (simp add: assms(1) assms(2) assms(3) lookup(4) rep_of_idem rep_of_less_length_l ufa_union_aux)
      with a_eq_rep_of_a_in_CC have **: "Congruence_Closure (representativeE ?step \<union> pending_set pe \<union> set (u ! rep_of l a))
(rep_of (ufa_union l a b) c \<approx> rep_of l c)" 
        by (metis Congruence_Closure_union assms(1) congruence_closure.select_convs(1) length_list_update lookup(4) rep_of_less_length_l)
      from lookup * base Congruence_Closure_union
      have "Congruence_Closure (representativeE ?step)
(F a' b' \<approx> rep_of (ufa_union l a b) c)" unfolding representativeE_def congruence_closure.select_convs
        by force
      with ** transitive2 Congruence_Closure_union show ?thesis 
        using lookup(1) by blast
    qed
  next
    case new_eq
    with assms have "valid_vars_pending eq2 l" unfolding pending_invar_def 
      by fastforce
    with new_eq have eq: "eq = (a \<approx> b)"
      by (simp add: assms(4) assms(5))
    have "rep_of (ufa_union l a b) a = rep_of (ufa_union l a b) b" 
      by (simp add: assms(1) assms(2) assms(3) ufa_union_aux)
    then have "Congruence_Closure (representativeE ?step) (a \<approx> b)"
      using CC_same_rep assms by auto
    then show ?thesis using Congruence_Closure_union eq 
      by blast
  qed (simp add: base)
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
  shows "lookup_invar2' \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (u ! rep_of l a)"
    (is "lookup_invar2' ?mini_step (u ! rep_of l a)")
  unfolding lookup_invar2'_def congruence_closure.select_convs
proof(standard, standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix a' b' c c\<^sub>1 c\<^sub>2
  assume prems: "a' < length (ufa_union l a b)"
    "b' < length (ufa_union l a b)"
    "ufa_union l a b ! a' = a'"
    "ufa_union l a b ! b' = b'"
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  with assms have *: "l ! a' = a'" "l ! b' = b'" "a' < length l" "b' < length l"
    "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    using ufa_union_root apply blast+ 
    using prems by auto
  with assms obtain b\<^sub>1 b\<^sub>2 bc a\<^sub>1 a\<^sub>2 ac where 1: "
         (F b\<^sub>1 b\<^sub>2 \<approx> bc) \<in> set (u ! b') \<and>
         rep_of l b\<^sub>1 = rep_of l c\<^sub>1 \<and>
         rep_of l b\<^sub>2 = rep_of l c\<^sub>2 \<and>
         Congruence_Closure
          (representativeE
            \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr> \<union>
           pending_set (eq # pe))
          (bc \<approx> c)"
    "
         (F a\<^sub>1 a\<^sub>2 \<approx> ac) \<in> set (u ! a') \<and>
         rep_of l a\<^sub>1 = rep_of l c\<^sub>1 \<and>
         rep_of l a\<^sub>2 = rep_of l c\<^sub>2 \<and>
         Congruence_Closure
          (representativeE
            \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr> \<union>
           pending_set (eq # pe))
          (ac \<approx> c)" unfolding lookup_invar2'_def congruence_closure.select_convs
    by fastforce
  have 4: "aa < length l \<Longrightarrow> bb < length l \<Longrightarrow> 
rep_of l aa = rep_of l bb \<Longrightarrow> rep_of (ufa_union l a b) aa = rep_of (ufa_union l a b) bb" 
    for aa bb using assms rep_of_ufa_union_invar by blast
  from assms use_list_invar_less_n_in_set * 1
  have 5: "b\<^sub>1 < length l" "b\<^sub>2 < length l" "bc < length l"
    "a\<^sub>1 < length l" "a\<^sub>2 < length l" "ac < length l"
    by metis+
  from inv2_mini_step 
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
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                 proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr> \<union>
             pending_set pe \<union> set (u ! rep_of l a))
            (bc \<approx> c))
       ""
           (F a\<^sub>1 a\<^sub>2 \<approx> ac) \<in> set (u[rep_of l a := []] ! a') \<and>
           rep_of (ufa_union l a b) a\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) a\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                 proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr> \<union>
             pending_set pe \<union> set (u ! rep_of l a))
            (ac \<approx> c)" unfolding 6 3
    by blast+
  then show "(\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_of l a := []] ! a') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t,
                 pending = pe, proof_forest = add_edge pf a b,
                 pf_labels = add_label pfl pf a eq, input = ip\<rparr> \<union>
             pending_set pe \<union>
             set (u ! rep_of l a))
            (ba \<approx> c)) \<and>
       (\<exists>b\<^sub>1 b\<^sub>2 ba.
           (F b\<^sub>1 b\<^sub>2 \<approx> ba) \<in> set (u[rep_of l a := []] ! b') \<and>
           rep_of (ufa_union l a b) b\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and>
           rep_of (ufa_union l a b) b\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2 \<and>
           Congruence_Closure
            (representativeE
              \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t,
                 pending = pe, proof_forest = add_edge pf a b,
                 pf_labels = add_label pfl pf a eq, input = ip\<rparr> \<union>
             pending_set pe \<union>
             set (u ! rep_of l a))
            (ba \<approx> c)) "
    by auto
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

lemma inv_same_rep_classes_step:
  assumes  "ufa_invar l" "a < length l" "b < length l"
    "inv_same_rep_classes \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    (is "inv_same_rep_classes ?base")
    "rep_of pf a \<noteq> rep_of pf b" "ufa_invar pf" "length pf = length l"
  shows "inv_same_rep_classes (propagate_step l u t pe pf pfl ip a b eq)"
  unfolding inv_same_rep_classes_def
  using assms proof(induction rule: propagate_step_induct)
  case base
  show ?case proof(standard, standard, standard, standard)
    fix i j
    let ?step = "\<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                     proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>"
    assume i_j: "i < length (proof_forest ?step)" "j < length (proof_forest ?step)"
    with add_edge_preserves_length' assms have *:"length (proof_forest ?step) = length (proof_forest ?base)" 
      by simp
    with add_edge_preserves_length' assms have "length (cc_list ?step) = length (cc_list ?base)" 
      by simp
    with assms * have "(rep_of (cc_list ?base) i = rep_of (cc_list ?base) j) =
           (rep_of (proof_forest ?base) i = rep_of (proof_forest ?base) j)" unfolding inv_same_rep_classes_def using inv_same_rep_classes_not_divided 
      using i_j by presburger
        \<comment>\<open>The representative classes of add_edge and ufa_invar have the same behaviour\<close>
    with rep_of_add_edge_aux ufa_union_aux 
    show "(rep_of (cc_list ?step) i = rep_of (cc_list ?step) j) =
           (rep_of (proof_forest ?step) i = rep_of (proof_forest ?step) j) " 
      using assms * i_j inv_same_rep_classes_not_divided unfolding congruence_closure.select_convs 
      by (smt (z3) congruence_closure.select_convs(1) congruence_closure.select_convs(5))
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
    input = ip\<rparr> (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a))

\<and> 
(rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a))
)"
proof(standard)
  fix eq'
  assume eq': "eq' \<in> set (u ! rep_of l a)"
  with assms use_list_invar_less_n_in_set'
  obtain c\<^sub>1 c\<^sub>2 c where c: "eq' = (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    "c\<^sub>1 < length l" "c\<^sub>2 < length l" "c < length l" 
    by (metis rep_of_bound rep_of_root use_list_invar_less_n_in_set(1))
  with assms obtain b\<^sub>1 b\<^sub>2 bb where 
    b: "lookup_entry t l c\<^sub>1 c\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> bb)" 
    "Congruence_Closure (representativeE ?base \<union> pending_set (pending ?base)
                  \<union> set []) (bb \<approx> c)"
    unfolding use_list_invar2'_def 
    by (metis eq' congruence_closure.select_convs(1-3) rep_of_bound rep_of_min)
  with assms c rep_of_bound rep_of_min
  have *: "rep_of l c\<^sub>1 < length l" "l ! rep_of l c\<^sub>1 = rep_of l c\<^sub>1" 
    "rep_of l c\<^sub>2 < length l" "l ! rep_of l c\<^sub>2 = rep_of l c\<^sub>2" 
    "lookup_entry t l c\<^sub>1 c\<^sub>2 \<noteq> None"
    by auto
  with assms have c_eq_b: "rep_of l c\<^sub>1 = rep_of l b\<^sub>1" "rep_of l c\<^sub>2 = rep_of l b\<^sub>2"
    unfolding lookup_invar_def congruence_closure.select_convs 
    by (metis b(1) equation.inject(2) option.inject)+
  with assms * c b obtain d\<^sub>1 d\<^sub>2 d where d: "(F d\<^sub>1 d\<^sub>2 \<approx> d) \<in> set (u ! rep_of l b\<^sub>2)"
    "rep_of l d\<^sub>1 = rep_of l b\<^sub>1" 
    "rep_of l d\<^sub>2 = rep_of l b\<^sub>2"
    "Congruence_Closure (representativeE ?base \<union> pending_set (eq # pe)
            \<union> set []) (d \<approx> bb)"
    unfolding lookup_invar2'_def congruence_closure.select_convs by metis
  with b(2) transitive1 have CC_d_c: "Congruence_Closure (representativeE ?base \<union> pending_set (eq # pe)
            \<union> set []) (d \<approx> c)" 
    unfolding congruence_closure.select_convs by blast
  from c_eq_b * assms c d have c2_step: "rep_of l a \<noteq> rep_of l c\<^sub>2 \<Longrightarrow> 
(F d\<^sub>1 d\<^sub>2 \<approx> d) \<in> set ((u[rep_of l a := []]) ! rep_of (ufa_union l a b) c\<^sub>2) \<and> 
rep_of (ufa_union l a b) d\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and> 
rep_of (ufa_union l a b) d\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    by (metis ufa_union_aux nth_list_update_neq rep_of_ufa_union_invar use_list_invar_less_n_in_set(1,2))
  have CC_step: "Congruence_Closure (representativeE ?base \<union> pending_set (eq # pe)
            \<union> set []) = Congruence_Closure (representativeE \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> \<union> pending_set pe
            \<union> set (u ! rep_of l a))" 
    using assms inv2_mini_step by simp
  with assms * c b c_eq_b obtain e\<^sub>1 e\<^sub>2 e where e: "(F e\<^sub>1 e\<^sub>2 \<approx> e) \<in> set (u ! rep_of l b\<^sub>1)"
    "rep_of l e\<^sub>1 = rep_of l b\<^sub>1" 
    "rep_of l e\<^sub>2 = rep_of l b\<^sub>2"
    "Congruence_Closure (representativeE ?base \<union> pending_set (eq # pe)
            \<union> set []) (e \<approx> bb)"
    unfolding lookup_invar2'_def congruence_closure.select_convs by metis
  with b(2) transitive1 have CC_e_c: "Congruence_Closure (representativeE ?base \<union> pending_set (eq # pe)
            \<union> set []) (e \<approx> c)" 
    unfolding congruence_closure.select_convs by blast
  from e c_eq_b * assms c have c1_step: "rep_of l a \<noteq> rep_of l c\<^sub>1 \<Longrightarrow> 
(F e\<^sub>1 e\<^sub>2 \<approx> e) \<in> set ((u[rep_of l a := []]) ! rep_of (ufa_union l a b) c\<^sub>1) \<and> 
rep_of (ufa_union l a b) e\<^sub>1 = rep_of (ufa_union l a b) c\<^sub>1 \<and> 
rep_of (ufa_union l a b) e\<^sub>2 = rep_of (ufa_union l a b) c\<^sub>2"
    by (metis ufa_union_aux nth_list_update_neq rep_of_ufa_union_invar use_list_invar_less_n_in_set(1,2))
  with c c1_step c2_step CC_step have "eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
           c\<^sub>1 < length l \<and>
           c\<^sub>2 < length l \<and>
           c < length l \<and>
           (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
            contains_similar_equation
             \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>
             (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a)) \<and>
           (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
            contains_similar_equation
             \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>
             (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a))"
    unfolding congruence_closure.select_convs 
    by (metis (full_types) CC_d_c CC_e_c c_eq_b d(1) e(1) nth_list_update_neq)
  then show "\<exists>c\<^sub>1 c\<^sub>2 c.
              eq' = F c\<^sub>1 c\<^sub>2 \<approx> c \<and>
              c\<^sub>1 < length l \<and>
              c\<^sub>2 < length l \<and>
              c < length l \<and>
              (rep_of l c\<^sub>1 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                   proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>
                (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a)) \<and>
              (rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow>
               contains_similar_equation
                \<lparr>cc_list = ufa_union l a b, use_list = u[rep_of l a := []], lookup = t, pending = pe,
                   proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a eq, input = ip\<rparr>
                (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a))" 
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
  have 1: "lookup_invar2' ?mini_step (u ! rep_of l a)" 
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
    input = ip\<rparr> (rep_of l c\<^sub>1) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a))

\<and> 
(rep_of l c\<^sub>2 \<noteq> rep_of l a \<longrightarrow> 
contains_similar_equation \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr> (rep_of l c\<^sub>2) c\<^sub>1 c\<^sub>2 c (u ! rep_of l a))
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

lemma inv2_invar_step:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "use_list_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "lookup_invar2 \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "a < length l" "b < length l" "rep_of l a \<noteq> rep_of l b"
    "a = left eq" "b = right eq"
  shows "inv2 (propagate_step l u t pe pf pfl ip a b eq)" 
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
    unfolding inv_same_length_def by auto
  with invar have invars: "lookup_invar ?mini_step" "use_list_invar ?mini_step"
    "cc_list_invar ?mini_step"
    using assms(1,4,5) lookup_invar_mini_step apply blast
    using assms(1,4,5) use_list_invar_mini_step lengths invar apply presburger
    using assms unfolding cc_list_invar_def by (simp add: ufa_union_invar)
  from inv2_mini_step assms invar have base: "Congruence_Closure (representativeE ?mini_step
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
  with inv2_loop[of "a"
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
  with assms * base show ?thesis unfolding inv2_def congruence_closure.select_convs 
    by argo
qed


subsection \<open>The length of all lists in the data structure are equal to nr_vars\<close>

text \<open>The length of all arrays of congruence_closure is always nr_vars cc\<close>

lemma add_label_preserves_length:
  "add_label_dom (pfl, a, b, c) \<Longrightarrow> length (add_label pfl a b c) = length pfl"
  apply(induction pfl a b c rule: add_label.pinduct)
  by (simp add: add_label.psimps)

text \<open>TODO: propagate_loop doesn't change length\<close>
lemma propagate_preserves_length_cc_list:
  assumes "propagate_dom cc" 
  shows "nr_vars (propagate cc) = nr_vars cc"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
   apply simp using assms sorry

lemma propagate_preserves_length_use_list:
  assumes "propagate_dom cc" "length (use_list cc) = n"
  shows "length (use_list (propagate cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def 
  sorry

lemma propagate_preserves_length_lookup:
  assumes "propagate_dom cc" "length (lookup cc) = n" 
  shows "length (lookup (propagate cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  sorry

lemma propagate_preserves_length_proof_forest:
  assumes "propagate_dom cc" 
    "length (proof_forest cc) = nr_vars cc" "length (use_list cc) = nr_vars cc" 
    "length (lookup cc) = nr_vars cc"
    "proof_forest_invar cc" "lookup_invar cc" "use_list_invar cc"
    "ufa_invar (cc_list cc)" "pending_invar cc" "inv_same_rep_classes cc"
  shows "length (proof_forest (propagate cc)) = nr_vars cc"
  using assms proof(induction cc rule: propagate.pinduct)
  case (1 l u t pf pfl ip)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 l u t eq pe pf pfl ip)
  define a where "a = left eq"
  define b where "b = right eq"
  from 2 have *: "length pf = length l" "ufa_invar pf" 
    unfolding congruence_closure.select_convs proof_forest_invar_def by auto
  from 2 a_def b_def pending_left_right_valid have a_b: "a < length l" "b < length l"  
    by auto
  show ?case proof(cases "rep_of l a = rep_of l b")
    case True
    then have "propagate 
         \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
  = propagate \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" 
      using a_def b_def propagate.psimps unfolding Let_def by (metis "2.hyps")
    moreover have "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
      using "2.prems" pending_invar_Cons by blast
    ultimately show ?thesis using 2 True a_def b_def sorry
  next
    case False
    with 2 have rep_of_pf: "rep_of pf a \<noteq> rep_of pf b" 
      by (metis "*"(1) a_b inv_same_rep_classes_divided)
    with add_edge_domain a_b * have dom: "add_edge_dom (pf, a, b)"
      by metis
    with 2 add_edge_preserves_length * have length_add_edge: "length (add_edge pf a b) = length l"
      by presburger
    from 2(5) have length_ufa_union: "length (ufa_union l a b) = length l"
      by force
    from * a_b dom add_edge_ufa_invar_invar have "ufa_invar (add_edge pf a b)" 
      by (simp add: \<open>rep_of pf a \<noteq> rep_of pf b\<close>)
    have "length l = length l" "ufa_invar l"
      using length_ufa_union apply fastforce
      using "2.prems"(7) by auto(*
    with pending_invar_step 2 a_def have pending_invar: "pending_invar (pe @ map (link_to_lookup t l) (filter (lookup_Some t l) (u ! rep_of l a))) (length l)"
      by (metis congruence_closure.select_convs(2))
    from proof_forest_invar_step "2.prems" have proof_forest_invar: 
      "proof_forest_invar (propagate_step l u t pf pfl ip a b pe)" 
      using \<open>rep_of pf a \<noteq> rep_of pf b\<close> a_b add_edge_preserves_length dom length_add_edge by presburger
    have "ufa_invar pf" "ufa_invar l" "a < length pf" "b < length pf" "length pf = length l"
      using * a_b \<open>ufa_invar l\<close> \<open>length l = n\<close> by simp_all
    from inv_same_rep_classes_step[OF 2(13) rep_of_pf this] have inv_same_rep_classes: "inv_same_rep_classes (propagate_step l u t pf pfl ip a b pe)" by blast
    from "2.prems" have "a < length l" "b < length l" "length t = length l" "length u = length l" 
      by (auto simp add:  \<open>length l = n\<close> a_b) 
    with lookup_invar_step 2 have lookup_invar: "lookup_invar (propagate_step l u t pf pfl ip a b pe)"
      using \<open>ufa_invar l\<close> by presburger
    from use_list_invar_step have use_list_invar: "use_list_invar (propagate_step l u t pf pfl ip a b pe)"
      by (simp add: "2.prems" \<open>a < length l\<close> \<open>b < length l\<close> \<open>length u = length l\<close> \<open>ufa_invar l\<close> )
    have "ufa_invar (ufa_union l a b)" "length (lookup (propagate_step l u t pf pfl ip a b pe)) = n"
      using \<open>a < length pf\<close> \<open>b < length pf\<close> \<open>length pf = length l\<close> \<open>ufa_invar l\<close> ufa_union_invar
      by (simp_all add: \<open>length l = n\<close> \<open>length t = length l\<close> set_lookup_preserves_length)
    with 2(3)[OF a_def b_def False _ _ _ _ proof_forest_invar lookup_invar use_list_invar] False proof_forest_invar inv_same_rep_classes length_add_edge length_ufa_union pending_invar
    have "length (proof_forest
       (propagate (xs @ map (link_to_lookup t l) (filter (lookup_Some t l) (u ! rep_of l a)))
         (propagate_step l u t pf pfl ip a b pe))) = n" 
      by (metis "2.prems"(3) congruence_closure.select_convs(1,2,4) length_list_update)
    with False 2 propagate_simps show ?thesis unfolding a_def b_def
      by presburger*)
    show ?thesis sorry
  qed
qed

lemma propagate_preserves_length_pf_labels:
  assumes "propagate_dom cc" "length (pf_labels cc) = nr_vars cc" 
    "length (proof_forest cc) = nr_vars cc" "ufa_invar (proof_forest cc)"
    "pending_invar cc" "inv_same_rep_classes cc" "ufa_invar (cc_list cc)"
    "nr_vars cc = length (use_list cc)"
    "nr_vars cc = length (lookup cc)"
    "lookup_invar cc" "use_list_invar cc"
  shows "length (pf_labels (propagate cc)) = nr_vars cc"
  using assms proof(induction rule: propagate.pinduct)
  case (1 l u t pf pfl ip)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 l u t eq pe pf pfl ip)
  define a where "a = left eq"
  define b where "b = right eq"
  with "2.prems" a_def pending_left_right_valid have a_b: "a < length pf" "b < length pf"
    by force+
  with "2.prems" add_label_domain have "add_label_dom (pfl, pf, a, eq)"
    by force
  with add_label_preserves_length 2(4)
  have "length (add_label pfl pf a eq) = length l"
    by simp
  show ?case
  proof(cases "rep_of l a = rep_of l b")
    case True
    then show ?thesis 
      using 2 a_def b_def pending_invar_Cons propagate.psimps(2) unfolding Let_def sorry
  next
    case False
      (*then have rep_pf: "rep_of pf a \<noteq> rep_of pf b" 
      using "2.prems"(5) a_b inv_same_rep_classes_divided by auto
    with add_edge_domain "2.prems" a_b have "add_edge_dom (pf, a, b)" 
      by (metis congruence_closure.select_convs(4))
    with 2(5) add_edge_preserves_length
    have 1: "length (proof_forest (propagate_step l u t pf pfl ip a b pe)) = n" 
      by auto
    have 3: "proof_forest_invar_termination
     (propagate_step l u t pf pfl ip a b pe) " 
      using "2.prems"(3) rep_pf a_b add_edge_ufa_invar_invar by auto
    have "n = length l" "ufa_invar l" "length u = length l"
      using "2.prems" by auto
    with pending_invar_step[of pe xs l a u t pf pfl ip] 2 a_def have 4: "pending_invar
     (xs @ map (link_to_lookup t l) (filter (lookup_Some t l) (u ! rep_of l a))) (length l)"
      by metis
    from "2.prems" have 5: "inv_same_rep_classes (propagate_step l u t pf pfl ip a b pe)" 
      by (metis \<open>n = length l\<close> \<open>ufa_invar l\<close> a_b congruence_closure.select_convs(4) inv_same_rep_classes_step rep_pf)
    from "2.prems" have 6: "ufa_invar (cc_list (propagate_step l u t pf pfl ip a b pe))"
      by (metis a_b congruence_closure.select_convs(1,4) ufa_union_invar)
    from "2.prems" have 7: "nr_vars (propagate_step l u t pf pfl ip a b pe) =
    length (use_list (propagate_step l u t pf pfl ip a b pe))" 
      by (metis congruence_closure.select_convs(1,2) length_list_update)
    from lookup_invar_step "2.prems" a_b have 8: "lookup_invar (propagate_step l u t pf pfl ip a b pe)"
      by force
    from use_list_invar_step "2.prems" have 9: "use_list_invar (propagate_step l u t pf pfl ip a b pe)" 
      using \<open>length u = length l\<close> \<open>n = length l\<close> \<open>ufa_invar l\<close> a_b by auto
    with 2 rep_pf 1 3 4 5 6 7 8 9
    show ?thesis 
      by (metis False \<open>length (add_label pfl pf a pe) = n\<close> a_def b_def congruence_closure.select_convs(1,3,5) length_list_update propagate_simp3 set_lookup_preserves_length)
  qed*)
    show ?thesis sorry
  qed
qed

lemma length_propagate_cc:
  assumes "cc_invar cc"
    "propagate_dom cc"
  shows "nr_vars cc = nr_vars (propagate cc)"
    "nr_vars cc = length (use_list (propagate cc))"
    "nr_vars cc = length (lookup (propagate cc))"
    "nr_vars cc = length (proof_forest (propagate cc))"
    "nr_vars cc = length (pf_labels (propagate cc))"
  using assms propagate_preserves_length_use_list propagate_preserves_length_cc_list inv_same_length_def propagate_preserves_length_lookup
    cc_list_invar_def propagate_preserves_length_proof_forest propagate_preserves_length_pf_labels proof_forest_invar_def 
  by auto 

lemma inv_same_length_step:
  assumes "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "rep_of l a \<noteq> rep_of l b" "a = left eq" "b = right eq"
  shows "inv_same_length (propagate_step l u t pe pf pfl ip a b eq)
(nr_vars (propagate_step l u t pe pf pfl ip a b eq))" 
proof-
  from assms have pe_valid: "valid_vars_pending eq (length l)" 
    using pending_invar_Cons by auto
  show ?thesis unfolding inv_same_length_def
    apply(rule conjI)+
    apply blast
    using assms inv_same_length_def apply fastforce
    using assms inv_same_length_def  apply auto[1]
    using assms add_edge_preserves_length' pe_valid pending_left_right_valid' inv_same_rep_classes_divided length_list_update
    unfolding inv_same_length_def proof_forest_invar_def subgoal sorry
        (*apply (metis congruence_closure.select_convs(1) congruence_closure.select_convs(4))*)
    using assms add_label_preserves_length add_label_domain pending_left_right_valid' 
    unfolding proof_forest_invar_def inv_same_length_def 
    by auto
qed

subsection \<open>cc_invar lemmata\<close>

lemma cc_invar_initial_cc: "cc_invar (initial_cc n)"
proof(rule conjI)+
  show "cc_list_invar (initial_cc n)" unfolding cc_list_invar_def 
    by (simp add: ufa_init_invar)
  show "use_list_invar (initial_cc n)" unfolding use_list_invar_def
  proof(standard, standard, standard, standard, standard)
    fix i j 
    assume "i < nr_vars (initial_cc n)" "j < length (use_list (initial_cc n) ! i)"
      "cc_list (initial_cc n) ! i = i"
    then have "length (use_list (initial_cc n) ! i) = 0" 
      by fastforce
    then have "False" 
      using \<open>j < length (use_list (initial_cc n) ! i)\<close> by presburger
  qed simp
  show "lookup_invar (initial_cc n)" unfolding lookup_invar_def
  proof(standard, standard, standard, standard, standard, standard, standard)
    fix i j
    assume "i < nr_vars (initial_cc n)" "j < nr_vars (initial_cc n)"
      "cc_list (initial_cc n) ! i = i \<and> cc_list (initial_cc n) ! j = j"
    then show "lookup (initial_cc n) ! i ! j = None" 
      by force
  next
    show "quadratic_table (lookup (initial_cc n))" 
      by simp
  qed
  show "proof_forest_invar (initial_cc n)" unfolding proof_forest_invar_def
    by (simp add: ufa_init_invar)
  show "inv1 (initial_cc n)" unfolding inv1_def
    by simp
  show "inv2 (initial_cc n) (pending_set [])" unfolding inv2_def
  proof
    fix x
    have "representativeE (initial_cc n) \<union> pending_set [] = {}" unfolding representativeE_def by simp
    moreover have "input (initial_cc n) = {}"  by simp
    ultimately show "Congruence_Closure (representativeE (initial_cc n) \<union> pending_set []) x =
         Congruence_Closure (input (initial_cc n)) x" 
      by presburger
  qed
  show "inv_same_rep_classes (initial_cc n)" unfolding inv_same_rep_classes_def
  proof(standard, standard, standard, standard)
    fix i j
    assume "i < length (proof_forest (initial_cc n))"
      "j < length (proof_forest (initial_cc n))"
    then show "(rep_of (cc_list (initial_cc n)) i =
            rep_of (cc_list (initial_cc n)) j) =
           (rep_of (proof_forest (initial_cc n)) i =
            rep_of (proof_forest (initial_cc n)) j)" 
      by force
  qed
  show "inv_same_length (initial_cc n) (nr_vars (initial_cc n))" unfolding inv_same_length_def
    by simp
  show "pending_invar [] (nr_vars (initial_cc n))" 
    by simp
qed

lemma cc_invar_step:
  assumes "cc_invar_pending \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> (pe # xs)"
    "valid_vars_pending pe (length l)" "a = left pe" "b = right pe" "rep_of l a \<noteq> rep_of l b"
  shows "cc_invar_pending (propagate_step l u t pf pfl ip a b pe) xs"
  apply (rule conjI)+
  using assms cc_list_invar_def pending_left_right_valid' ufa_union_invar apply auto[1]
  using assms cc_list_invar_def inv_same_length_def pending_left_right_valid' use_list_invar_step apply auto[1]
  using assms cc_list_invar_def inv_same_length_def lookup_invar_step pending_left_right_valid' apply auto[1]
  using assms proof_forest_invar_step pending_left_right_valid' inv_same_rep_classes_divided 
  unfolding cc_list_invar_def inv_same_length_def 
  apply (metis (full_types) congruence_closure.select_convs(1) congruence_closure.select_convs(4))
  using inv1_def apply blast
  using assms inv2_invar_step apply blast
  using assms inv_same_rep_classes_step inv_same_rep_classes_divided pending_left_right_valid'
  unfolding cc_list_invar_def inv_same_length_def proof_forest_invar_def 
  apply (smt (verit, del_insts) congruence_closure.select_convs(1) congruence_closure.select_convs(4))
  using length_propagate_cc assms inv_same_length_step
  unfolding inv_same_length_def subgoal sorry
  using assms(1) apply auto
  done

end