section \<open>Correctness proofs for congruence closure\<close>
theory Congruence_Closure_Proofs
  imports CC_Invars 
begin 

fun apply_merges :: "congruence_closure \<Rightarrow> equation list \<Rightarrow> congruence_closure"
  where
"apply_merges cc (eq # xs) = apply_merges (merge cc eq) xs"
| "apply_merges cc [] = cc"



lemma cc_\<alpha>_eq_CC_representativeE: "cc_\<alpha> cc (s \<approx> t) = Congruence_Closure (representativeE cc) (s \<approx> t)"
  oops

subsection \<open>Correctness of merge\<close>

lemma pending_empty_after_merge: 
"pending cc = [] \<Longrightarrow> pending (merge cc x) = []"
  sorry

lemma 
"valid_vars eq n \<Longrightarrow> cc_invar cc \<Longrightarrow> 
cc_\<alpha> (apply_merges (initial_cc n) xs) eq = Congruence_Closure (set xs) eq"
  oops

lemma representativeE_in_cc_\<alpha>: 
  assumes "cc_invar cc" "valid_vars eq (nr_vars cc)" "eq \<in> representativeE cc"
  shows "cc_\<alpha> cc eq"
proof-
  obtain l u t pe pf pfl ip where 
cc: "cc = \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    using congruence_closure.cases by blast
  from assms have "ufa_invar l" 
    unfolding cc cc_list_invar_def by auto
  from assms cc consider
(rep) c where "eq = c \<approx> rep_of l c" "c < length l" "l ! c \<noteq> c"
| (lookup) a' b' c c\<^sub>1 c\<^sub>2 where "eq = F a' b' \<approx> rep_of l c" "a' < length l" "b' < length l"
"c < length l" "l ! a' = a'" "l ! b' = b'" "t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
    unfolding representativeE_def 
    by fastforce
  then show ?thesis 
  proof(cases)
    case rep
    with assms have "are_congruent cc eq" unfolding cc_\<alpha>_def rep(1) cc are_congruent.simps 
      using \<open>ufa_invar l\<close> rep_of_idem by presburger
    with assms show ?thesis 
      unfolding cc_\<alpha>_def by auto
  next
    case lookup
    with assms have "are_congruent cc eq" unfolding cc_\<alpha>_def lookup(1) cc are_congruent.simps 
      using \<open>ufa_invar l\<close> rep_of_idem by (simp add: rep_of_refl)
    with assms show ?thesis 
      unfolding cc_\<alpha>_def by auto
  qed
qed

lemma CC_representativeE_valid_vars:
  assumes "Congruence_Closure (representativeE cc) eq" "cc_invar cc" 
  shows "valid_vars eq (nr_vars cc)"
using assms proof(induction "representativeE cc" eq rule: Congruence_Closure.induct)
  case (base eqt)
  then show ?case sorry
next
  case (reflexive a)
  then show ?case sorry
next
  case (symmetric a b)
  then show ?case sorry
next
  case (transitive1 a b c)
  then show ?case sorry
next
  case (transitive2 a\<^sub>1 a\<^sub>2 b c)
  then show ?case sorry
next
  case (transitive3 a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2)
  then show ?case sorry
next
  case (monotonic a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b)
  then show ?case sorry
qed

subsection \<open>Lemmas about are_congruent\<close>

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

(* Derived the lemma "False" from "CC_representativeE_valid_vars", "Congruence_Closure.reflexive", "congruence_closure.select_convs(1)", "len_greater_imp_nonempty", and "valid_vars.simps(1)", which could be due to a bug in Sledgehammer or to inconsistent axioms (including "sorry"s) *)
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
  assumes "are_congruent cc (F a\<^sub>1 a\<^sub>2 \<approx> a)" "are_congruent cc (F b\<^sub>1 b\<^sub>2 \<approx> b)"
"are_congruent cc (a\<^sub>1 \<approx> b\<^sub>1)" "are_congruent cc (a\<^sub>2 \<approx> b\<^sub>2)" 
"lookup_invar cc" 
"valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (nr_vars cc)" "valid_vars (F b\<^sub>1 b\<^sub>2 \<approx> b) (nr_vars cc)"
"valid_vars (a\<^sub>2 \<approx> b\<^sub>2) (nr_vars cc)" "valid_vars (a\<^sub>1 \<approx> b\<^sub>1) (nr_vars cc)" 
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

lemma 
  assumes "valid_vars eq (nr_vars cc)" "cc_invar cc" "pending cc = []"
  shows "Congruence_Closure ((input cc)) eq = cc_\<alpha> cc eq"
proof-
  have "inv2 cc" 
    by (simp add: assms(2))
  then have "Congruence_Closure (input cc) eq = Congruence_Closure (representativeE cc) eq"
    unfolding inv2_def using assms 
    by simp
  also have "... = cc_\<alpha> cc eq"
  proof
    assume CC: "Congruence_Closure (representativeE cc) eq"
    from CC assms show "cc_\<alpha> cc eq"
    proof(induction "(representativeE cc)" eq rule: Congruence_Closure.induct)
      case (base eqt)
      with representativeE_in_cc_\<alpha> show ?case 
        by blast
    next
      case (reflexive a)
      then show ?case 
        by (metis are_congruent.simps(1) cc_\<alpha>_def congruence_closure.surjective old.unit.exhaust)
    next
      case (symmetric a b)
      then show ?case 
        by (metis are_congruent.simps(1) cc_\<alpha>_def congruence_closure.surjective old.unit.exhaust valid_vars.simps(1))
    next
      case (transitive1 a b c)
      then have "valid_vars a \<approx> b (nr_vars cc)" "valid_vars b \<approx> c (nr_vars cc)"
        using CC_representativeE_valid_vars by blast+
      then show ?case 
        using are_congruent_transitive1 cc_\<alpha>_def transitive1 by blast
    next
      case (transitive2 a\<^sub>1 a\<^sub>2 b c)
      then show ?case 
        by (metis CC_representativeE_valid_vars are_congruent_transitive2 cc_\<alpha>_def cc_list_invar_def)
    next
      case (transitive3 a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2)
      then show ?case 
        by (metis CC_representativeE_valid_vars are_congruent_transitive3 cc_\<alpha>_def cc_list_invar_def)
    next
      case (monotonic a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b)
      then have "valid_vars a \<approx> b (nr_vars cc)" 
        by blast
      with monotonic are_congruent_monotonic show ?case unfolding cc_\<alpha>_def 
        using CC_representativeE_valid_vars cc_\<alpha>_def cc_list_invar_def monotonic.hyps(1) by blast
    qed
  next
    assume cc_\<alpha>: "cc_\<alpha> cc eq"
    show "Congruence_Closure (representativeE cc) eq"
      proof(cases eq)
        case (Constants x11 x12)
        with cc_\<alpha> have "rep_of (cc_list cc) x11 = rep_of (cc_list cc) x12"
          using congruence_closure.cases unfolding cc_\<alpha>_def 
          by (metis are_congruent.simps(1) congruence_closure.select_convs(1))
        have "Congruence_Closure (representativeE cc) (x11 \<approx> rep_of (cc_list cc) x11)"
          using Constants a_eq_rep_of_a_in_CC(1) assms(1) valid_vars.simps(1) by blast
        moreover have "Congruence_Closure (representativeE cc) (rep_of (cc_list cc) x12 \<approx> x12)"
          using Constants a_eq_rep_of_a_in_CC(2) assms(1) valid_vars.simps(1) by blast
        ultimately show ?thesis 
          by (metis Constants \<open>rep_of (cc_list cc) x11 = rep_of (cc_list cc) x12\<close> transitive1)
      next
        case (Function x21 x22 x23)
        then obtain l u t pe pf pfl ip where
cc: "cc = \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
          using congruence_closure.cases by blast
        then obtain b\<^sub>1 b\<^sub>2 b where 
"(t ! rep_of l x21) ! rep_of l x22 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b)" 
"rep_of l x23 = rep_of l b"
          using cc_\<alpha> Function congruence_closure.cases unfolding cc_\<alpha>_def cc
          by (metis are_congruent_Function assms(2) cc cc_list_invar_def congruence_closure.select_convs(1))
        then have "rep_of l x21 < nr_vars cc \<and> rep_of l x22 < nr_vars cc \<and> b < nr_vars cc \<and>
                      cc_list cc ! rep_of l x21 = rep_of l x21 
\<and> cc_list cc ! rep_of l x22 = rep_of l x22 
\<and> lookup cc ! rep_of l x21 ! rep_of l x22 = Some (F b\<^sub>1 b\<^sub>2 \<approx> b)" 
          by (metis Function assms(1) assms(2) cc cc_list_invar_def congruence_closure.select_convs(1) congruence_closure.select_convs(3) lookup_invar_less_n(3) rep_of_bound rep_of_min valid_vars.simps(2))
        then have "F (rep_of l x21) (rep_of l x22) \<approx> rep_of l b \<in> representativeE cc"  
          unfolding representativeE_def 
          by (simp add: cc)
        have "Congruence_Closure (representativeE cc) (rep_of l x21 \<approx> x21)" "Congruence_Closure (representativeE cc) (rep_of l x22 \<approx> x22)" 
          by (metis Function a_eq_rep_of_a_in_CC(2) assms(1) cc congruence_closure.select_convs(1) valid_vars.simps(2))+
        then have "Congruence_Closure (representativeE cc) (F x21 x22 \<approx> rep_of l b)" 
          by (metis \<open>F rep_of l x21 rep_of l x22 \<approx> rep_of l b \<in> representativeE cc\<close> base transitive3)
        with Function show ?thesis 
          by (metis \<open>rep_of l x23 = rep_of l b\<close> a_eq_rep_of_a_in_CC(2) assms(1) cc congruence_closure.select_convs(1) transitive2 valid_vars.simps(2))
      qed
  qed
  finally show ?thesis .
qed
  

subsection \<open>Correctness of are_congruent\<close>
lemma "valid_vars eq (nr_vars cc) \<Longrightarrow> are_congruent cc eq = cc_\<alpha> cc eq"
  unfolding cc_\<alpha>_def by simp

subsection \<open>Correctness of explain\<close>

lemma "are_congruent cc (a \<approx> b) \<Longrightarrow> cc_invar cc \<Longrightarrow>
  Congruence_Closure (cc_explain cc ([0..<nr_vars cc]) [(a, b)]) (a \<approx> b)"
  sorry

end 