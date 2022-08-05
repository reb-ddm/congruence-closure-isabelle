section \<open>Correctness proofs for congruence closure\<close>
theory CC_Correctness
  imports CC_Termination 
begin 

theorem cc_invar_merge: 
  assumes "cc_invar cc" "valid_vars eq (nr_vars cc)"
  shows "cc_invar (merge cc eq)"
  using assms proof(induction cc eq rule: merge.induct)
  case (1 l u t pe pf pfl ip a b)
  then have "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
      proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>" 
    using cc_invar_merge1 by simp
  with 1 propagate_domain' show ?case 
    using merge.simps(1) cc_invar_propagate 
    by (metis congruence_closure.select_convs(1))
next
  case (2 l u t pe pf pfl ip a\<^sub>1 a\<^sub>2 a)
  then show ?case 
  proof(cases "lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)")
    case True
    then have "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf,
            pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      using cc_invar_merge2 "2.prems" by blast
    with True 2 propagate_domain' show ?thesis 
      using merge.simps(2) cc_invar_propagate by (metis congruence_closure.select_convs(1))
  next
    case False
    then have "cc_invar \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
      using cc_invar_merge3 "2.prems" by blast
    with False show ?thesis 
      by simp
  qed
qed

subsection \<open>Initial cc\<close>

theorem cc_invar_initial_cc: "cc_invar (initial_cc n)"
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
  have "representativeE (initial_cc n) \<union> pending_set (pending (initial_cc n)) = {}" 
    unfolding representativeE_def by simp
  moreover have "input (initial_cc n) = {}"  by simp
  ultimately show "correctness_invar (initial_cc n)" unfolding correctness_invar_def
    by auto
  show "same_eq_classes_invar (initial_cc n)" unfolding same_eq_classes_invar_def
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
  show "same_length_invar (initial_cc n) (nr_vars (initial_cc n))" 
    unfolding same_length_invar_def by simp
  show "pending_invar (initial_cc n)" 
    unfolding pending_invar_def by simp
  show "lookup_invar2 (initial_cc n)" 
    unfolding lookup_invar2_def by simp
  show "use_list_invar2 (initial_cc n)" 
    unfolding use_list_invar2_def by auto
  show "pf_labels_invar (initial_cc n)"
    unfolding pf_labels_invar_def congruence_closure.select_convs by force
qed

subsection \<open>Correctness of merge\<close>

lemma pending_empty_after_propagate: 
  "propagate_dom cc \<Longrightarrow> pending (propagate cc) = []"
  apply(induction rule: propagate.pinduct)
   apply simp
  by (metis propagate_simps2 propagate_simps3)

lemma pending_empty_after_merge: 
  "cc_invar cc \<Longrightarrow> valid_vars x (nr_vars cc) \<Longrightarrow> pending cc = [] \<Longrightarrow> pending (merge cc x) = []"
proof(induction cc x rule: merge.induct)
  case (1 l u t pe pf pfl ip a b)
  then show ?case using pending_empty_after_propagate cc_invar_merge1 propagate_domain' 
    using merge.simps(1) by (metis congruence_closure.select_convs(1))
next
  case (2 l u t pe pf pfl ip a\<^sub>1 a\<^sub>2 a)
  then show ?case using pending_empty_after_propagate apply(cases "lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a)")
    using pending_empty_after_propagate cc_invar_merge2 propagate_domain'
    using merge.simps(2) apply (metis congruence_closure.select_convs(1))
    using merge.simps(2) by simp
qed

theorem representativeE_are_congruent: 
  assumes "cc_invar cc" "valid_vars eq (nr_vars cc)" "eq \<in> representativeE cc"
  shows "are_congruent cc eq"
proof-
  obtain l u t pe pf pfl ip where 
    cc: "cc = \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    using congruence_closure.cases by blast
  from assms have "ufa_invar l" 
    unfolding cc cc_list_invar_def by auto
  from assms cc consider
    (rep) c where "eq = (c \<approx> rep_of l c)" "c < length l" "l ! c \<noteq> c"
  | (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
    "c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    unfolding representativeE_def 
    by fastforce
  then show ?thesis 
  proof(cases)
    case rep
    with assms show ?thesis unfolding rep(1) cc are_congruent.simps 
      using \<open>ufa_invar l\<close> rep_of_idem by presburger
  next
    case lookup
    with assms show ?thesis unfolding lookup(1) cc are_congruent.simps 
      using \<open>ufa_invar l\<close> rep_of_idem by (simp add: rep_of_refl)
  qed
qed

subsection \<open>Lemmas about \<open>are_congruent\<close>\<close>

lemma CC_representativeE_valid_vars:
  assumes "eq \<in> Congruence_Closure (representativeE cc)" "cc_invar cc" 
    "\<nexists> a . eq = (a \<approx> a)"
  shows "valid_vars eq (nr_vars cc)"
  using assms proof(induction eq rule: Congruence_Closure.induct)
  case (base eqt)
  then consider a where "eqt = (a \<approx> rep_of (cc_list cc) a)" 
    "a < nr_vars cc" "(cc_list cc) ! a \<noteq> a" 
  | a' b' c c\<^sub>1 c\<^sub>2 where "eqt = F a' b' \<approx> rep_of (cc_list cc) c"  "a' < nr_vars cc"
    "b' < nr_vars cc"  "c < nr_vars cc"
    "cc_list cc ! a' = a'" "cc_list cc ! b' = b'"
    "lookup cc ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    unfolding representativeE_def by blast
  then show ?case proof(cases)
    case 1
    then show ?thesis 
      using base.prems cc_list_invar_def rep_of_bound by auto
  next
    case 2
    then show ?thesis 
      using base.prems cc_list_invar_def rep_of_bound valid_vars.simps(2) by blast
  qed
qed auto

lemma are_congruent_Function: 
  assumes "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (length l)"
    "are_congruent \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
(F a\<^sub>1 a\<^sub>2 \<approx> a)" "ufa_invar l"
    "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  obtains b\<^sub>1 b\<^sub>2 b where 
    "(t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b)" "rep_of l a = rep_of l b"
proof(cases "(t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2")
  case None
  then show ?thesis 
    using assms by auto
next
  case (Some a)
  with assms obtain c c\<^sub>1 c\<^sub>2 where "a = F c\<^sub>1 c\<^sub>2 \<approx> c" unfolding lookup_invar_def
    by (metis congruence_closure.select_convs(1) congruence_closure.select_convs(3) option.discI option.inject rep_of_less_length_l rep_of_min valid_vars.simps(2))
  show ?thesis
    using assms that Some \<open>a = F c\<^sub>1 c\<^sub>2 \<approx> c\<close> unfolding lookup_invar_def 
    by auto
qed

lemma are_congruent_transitive1:
  assumes "are_congruent cc (a \<approx> b)" "are_congruent cc (b \<approx> c)" 
  shows "are_congruent cc (a \<approx> c)"
  using assms proof(induction cc "a \<approx> b" rule: are_congruent.induct)
  case (1 l u t pe pf pfl ip)
  then show ?case 
    by simp
qed

lemma are_congruent_transitive2:
  assumes "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> b)" "are_congruent cc (b \<approx> c)" 
    "lookup_invar cc" "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> b) (nr_vars cc)" "valid_vars (b \<approx> c) (nr_vars cc)"
    "ufa_invar (cc_list cc)"
  shows "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> c)"
  using assms proof(induction cc "F a\<^sub>1 a\<^sub>2 \<approx> b" rule: are_congruent.induct)
  case (2 l u t pe pf pfl ip)
  with are_congruent_Function congruence_closure.cases obtain b\<^sub>1 b\<^sub>2 c where 
    "(t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> c)" "rep_of l b = rep_of l c"
    by (metis congruence_closure.select_convs(1))
  with 2 show ?case 
    by force
qed

lemma are_congruent_transitive3:
  assumes "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> a)"
    "are_congruent cc (a\<^sub>1 \<approx> b\<^sub>1)" "are_congruent cc (a\<^sub>2 \<approx> b\<^sub>2)" 
    "lookup_invar cc" 
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (nr_vars cc)" "valid_vars (a\<^sub>1 \<approx> b\<^sub>1) (nr_vars cc)" 
    "valid_vars (a\<^sub>2 \<approx> b\<^sub>2) (nr_vars cc)"
    "ufa_invar (cc_list cc)"
  shows "are_congruent cc (F b\<^sub>1 b\<^sub>2 \<approx> a)"
  using assms proof(induction cc "F a\<^sub>1 a\<^sub>2 \<approx> a" rule: are_congruent.induct)
  case (2 l u t pe pf pfl ip)
  with are_congruent_Function congruence_closure.cases obtain b\<^sub>1 b\<^sub>2 c where 
    "(t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> c)" "rep_of l a = rep_of l c"
    by (metis congruence_closure.select_convs(1))
  with 2 show ?case 
    by auto
qed

lemma are_congruent_monotonic:
  assumes "lookup_invar cc" 
    "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> a)" "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> b)"
    "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (nr_vars cc)" "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> b) (nr_vars cc)"
    "ufa_invar (cc_list cc)"
  shows "are_congruent cc (a \<approx> b)"
  using assms proof(induction cc "F a\<^sub>1 a\<^sub>2 \<approx> a" rule: are_congruent.induct)
  case (2 l u t pe pf pfl ip)
  with are_congruent_Function congruence_closure.cases obtain b\<^sub>1 b\<^sub>2 c where 
    "(t ! rep_of l a\<^sub>1) ! rep_of l a\<^sub>2 = Some (F b\<^sub>1 b\<^sub>2 \<approx> c)" "rep_of l a = rep_of l c"
    by (metis congruence_closure.select_convs(1))
  with 2 show ?case 
    by auto
qed

theorem are_congruent_correct: 
  assumes "valid_vars eq (nr_vars cc)" "cc_invar cc" "pending cc = []"
  shows "eq \<in> Congruence_Closure ((input cc)) \<longleftrightarrow> are_congruent cc eq"
proof-
  obtain l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    using congruence_closure.cases by blast
  have "correctness_invar cc" 
    by (simp add: assms(2))
  then have "eq \<in> Congruence_Closure (input cc) \<longleftrightarrow> eq \<in> Congruence_Closure (representativeE cc)"
    unfolding correctness_invar_def using assms 
    by simp
  also have "... \<longleftrightarrow> are_congruent cc eq"
  proof
    assume CC: "eq \<in> Congruence_Closure (representativeE cc)"
    from CC assms show "are_congruent cc eq"
    proof(induction eq rule: Congruence_Closure.induct)
      case (base eqt)
      with representativeE_are_congruent show ?case 
        by blast
    next
      case (reflexive a)
      then show ?case unfolding cc by simp
    next
      case (symmetric a b)
      then show ?case unfolding cc by simp
    next
      case (transitive1 a b c)
      then have "valid_vars (a \<approx> b) (nr_vars cc)" "valid_vars (b \<approx> c) (nr_vars cc)"
        using CC_representativeE_valid_vars 
        by (metis equation.inject(1) valid_vars.simps(1))+
      then show ?case 
        using are_congruent_transitive1 transitive1 by blast
    next
      case (transitive2 a\<^sub>1 a\<^sub>2 b c)
      then show ?case 
        using CC_representativeE_valid_vars are_congruent_transitive2 cc_list_invar_def by blast
    next
      case (transitive3 a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2)
      then show ?case 
        using CC_representativeE_valid_vars are_congruent_transitive3 cc_list_invar_def 
        by (metis (no_types, lifting) equation.distinct(1) valid_vars.simps)
    next
      case (monotonic a\<^sub>1 a\<^sub>2 a b)
      then have valid_vars1: "valid_vars (a \<approx> b) (nr_vars cc)"  
        "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (nr_vars cc)" "valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> b) (nr_vars cc)" 
        using monotonic CC_representativeE_valid_vars by blast+
      with monotonic have "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> a)" 
        "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> b)"
        by auto
      with monotonic are_congruent_monotonic show ?case 
        using cc_list_invar_def valid_vars1 by blast
    qed
  next
    assume are_congruent: "are_congruent cc eq"
    show "eq \<in> Congruence_Closure (representativeE cc)"
    proof(cases eq)
      case (Constants x11 x12)
      with are_congruent have "rep_of (cc_list cc) x11 = rep_of (cc_list cc) x12"
        using congruence_closure.cases
        by (metis are_congruent.simps(1) congruence_closure.select_convs(1) mem_Collect_eq)
      have "(x11 \<approx> rep_of (cc_list cc) x11) \<in> Congruence_Closure (representativeE cc)"
        using Constants a_eq_rep_of_a_in_CC(1) assms(1) valid_vars.simps(1) by blast
      moreover have "(rep_of (cc_list cc) x12 \<approx> x12) \<in> Congruence_Closure (representativeE cc)"
        using Constants a_eq_rep_of_a_in_CC(2) assms(1) valid_vars.simps(1) by blast
      ultimately show ?thesis 
        by (metis Constants \<open>rep_of (cc_list cc) x11 = rep_of (cc_list cc) x12\<close> transitive1)
    next
      case (Function x21 x22 x23)
      then obtain b\<^sub>1 b\<^sub>2 b where 
        "(t ! rep_of l x21) ! rep_of l x22 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b)" 
        "rep_of l x23 = rep_of l b"
        using are_congruent congruence_closure.cases assms
        by (metis are_congruent_Function cc cc_list_invar_def congruence_closure.select_convs(1))
      then have "rep_of l x21 < nr_vars cc \<and> rep_of l x22 < nr_vars cc \<and> b < nr_vars cc \<and>
                      cc_list cc ! rep_of l x21 = rep_of l x21 
\<and> cc_list cc ! rep_of l x22 = rep_of l x22 
\<and> lookup cc ! rep_of l x21 ! rep_of l x22 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b)" 
        by (metis Function assms(1) assms(2) cc cc_list_invar_def congruence_closure.select_convs(1) congruence_closure.select_convs(3) lookup_invar_less_n(3) rep_of_bound rep_of_min valid_vars.simps(2))
      then have F_rep: "(F (rep_of l x21) (rep_of l x22) \<approx> (rep_of l b)) \<in> representativeE cc"  
        unfolding representativeE_def 
        by (simp add: cc)
      have "(rep_of l x21 \<approx> x21) \<in> Congruence_Closure (representativeE cc)" 
        "(rep_of l x22 \<approx> x22) \<in> Congruence_Closure (representativeE cc)" 
        by (metis Function a_eq_rep_of_a_in_CC(2) assms(1) cc congruence_closure.select_convs(1) valid_vars.simps(2))+
      then have "(F x21 x22 \<approx> rep_of l b) \<in> Congruence_Closure (representativeE cc)" 
        by (metis F_rep base transitive3)
      with Function show ?thesis 
        by (metis \<open>rep_of l x23 = rep_of l b\<close> a_eq_rep_of_a_in_CC(2) assms(1) cc congruence_closure.select_convs(1) transitive2 valid_vars.simps(2))
    qed
  qed
  finally show ?thesis .
qed

end 