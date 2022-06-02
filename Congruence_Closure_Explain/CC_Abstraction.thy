theory CC_Abstraction
  imports CC_Proofs
begin

section \<open>Abstract formalisation of congruence closure\<close>


text \<open>S is the set of input equations.
The Congruence Closure is the smallest relation that includes S and is closed under reflexivity,
symmetry, transitivity, and under function application.
Source: \<open>https://drops.dagstuhl.de/opus/volltexte/2021/14253/pdf/LIPIcs-FSCD-2021-15.pdf\<close>\<close>
         
inductive Congruence_Closure :: "equation set \<Rightarrow> equation \<Rightarrow> bool"
  where
    base: "eqt \<in> S \<Longrightarrow> Congruence_Closure S eqt"
  | reflexive: "Congruence_Closure S (a \<approx> a)"
  | symmetric: "Congruence_Closure S (a \<approx> b) \<Longrightarrow> Congruence_Closure S (b \<approx> a)"
  | transitive1: "Congruence_Closure S (a \<approx> b) \<Longrightarrow> Congruence_Closure S (b \<approx> c) \<Longrightarrow> Congruence_Closure S (a \<approx> c)"
  | transitive2: "Congruence_Closure S (F a\<^sub>1 a\<^sub>2 \<approx> b) \<Longrightarrow> Congruence_Closure S (b \<approx> c) \<Longrightarrow> Congruence_Closure S (F a\<^sub>1 a\<^sub>2 \<approx> c)"
  | transitive3: "Congruence_Closure S (F a\<^sub>1 a\<^sub>2 \<approx> a)
\<Longrightarrow> Congruence_Closure S (a\<^sub>1 \<approx> b\<^sub>1) \<Longrightarrow> Congruence_Closure S (a\<^sub>2 \<approx> b\<^sub>2)
\<Longrightarrow> Congruence_Closure S (F b\<^sub>1 b\<^sub>2 \<approx> a)"
| monotonic: "Congruence_Closure S (F a\<^sub>1 a\<^sub>2 \<approx> a) \<Longrightarrow> Congruence_Closure S (F b\<^sub>1 b\<^sub>2 \<approx> b)
\<Longrightarrow> Congruence_Closure S (a\<^sub>1 \<approx> b\<^sub>1) \<Longrightarrow> Congruence_Closure S (a\<^sub>2 \<approx> b\<^sub>2)
\<Longrightarrow> Congruence_Closure S (a \<approx> b)"

definition CC_union :: "(equation \<Rightarrow> bool) \<Rightarrow> equation \<Rightarrow> equation \<Rightarrow> bool"
  where
    "CC_union CC eq' = Congruence_Closure ({eq | eq. CC eq} \<union> {eq'})"

lemma Congruence_Closure_union:
  "Congruence_Closure S eqt \<Longrightarrow> Congruence_Closure (S \<union> S') eqt"
  apply(induction rule: Congruence_Closure.induct)
  using base apply blast
  using reflexive apply blast
  using symmetric apply blast
  using transitive1 apply blast
  using transitive2 apply blast
  using transitive3 apply blast
  using monotonic apply blast
  done

lemma Congruence_Closure_union':
  "Congruence_Closure S eqt \<Longrightarrow> Congruence_Closure (S' \<union> S) eqt"
  by (metis Congruence_Closure_union sup_commute)

lemma Congruence_Closure_split_rule:
  assumes "k \<notin> B \<Longrightarrow> Congruence_Closure A k"
  shows "Congruence_Closure (A \<union> B) k"
  using assms
  by (metis Congruence_Closure_union base sup_commute)

lemma CC_union_correct: 
  "CC_union (Congruence_Closure S) eq' eq = Congruence_Closure (S \<union> {eq'}) eq"
proof
  show "CC_union (Congruence_Closure S) eq' eq \<Longrightarrow> Congruence_Closure (S \<union> {eq'}) eq"
    unfolding CC_union_def
    apply(induction "{eqa |eqa. Congruence_Closure S eqa} \<union> {eq'}" eq rule: Congruence_Closure.induct)
    using base Congruence_Closure_union apply blast
    using reflexive apply blast
    using symmetric apply blast
    using transitive1 apply blast
    using transitive2 apply blast
    using transitive3 apply blast
    using monotonic apply blast
    done
next
  show "Congruence_Closure (S \<union> {eq'}) eq \<Longrightarrow> CC_union (Congruence_Closure S) eq' eq"
    apply(induction "S \<union> {eq'}" eq rule: Congruence_Closure.induct)
    unfolding CC_union_def 
    using base apply auto[1]
    using reflexive apply auto[1]
    using symmetric apply auto[1]
    using transitive1 apply blast
    using transitive2 apply blast
    using transitive3 apply blast
    using monotonic apply blast
    done
qed
thm Congruence_Closure.induct

lemma Congruence_Closure_not_empty_F:
"Congruence_Closure A (F a b \<approx> c) \<Longrightarrow> A \<noteq> {}"
  apply(induction A "(F a b \<approx> c)" arbitrary: a b c rule: Congruence_Closure.induct)
   apply auto[1]
  by simp

lemma Congruence_Closure_not_empty:
"Congruence_Closure A (a \<approx> b) \<Longrightarrow> a \<noteq> b \<Longrightarrow> A \<noteq> {}"
  apply(induction A "(a \<approx> b)" arbitrary: a b rule: Congruence_Closure.induct)
      apply auto[2]
  using symmetric apply blast
  using transitive1 apply blast
  using Congruence_Closure_not_empty_F apply simp
  done

lemma Congruence_Closure_empty_aux:
"Congruence_Closure A x \<Longrightarrow> A = {} \<Longrightarrow> (\<exists> a . x = (a \<approx> a))"
  apply(induction A x arbitrary: rule: Congruence_Closure.induct)
  by auto

lemma Congruence_Closure_empty:
"Congruence_Closure {} x \<longleftrightarrow> (\<exists> a . x = (a \<approx> a))"
proof
  from Congruence_Closure_empty_aux show "Congruence_Closure {} x \<Longrightarrow> \<exists>a. x = a \<approx> a" 
    by blast
  from Congruence_Closure.intros show "\<exists>a. x = a \<approx> a \<Longrightarrow> Congruence_Closure {} x"
    by blast
qed

text \<open>Rule to find if the congruence closure of two sets is equal\<close>
lemma Congruence_Closure_imp: 
  assumes "Congruence_Closure A x" "\<And> a. a \<in> A \<Longrightarrow> Congruence_Closure B a"
  shows "Congruence_Closure B x"
  using assms apply(induction A x rule: Congruence_Closure.induct)
        apply auto[1]
    using reflexive apply simp
    using symmetric apply blast
    using transitive1 apply blast
    using transitive2 apply blast
    using transitive3 apply blast
    using monotonic apply blast
    done

lemma Congruence_Closure_eq[case_names left right]:
  assumes "\<And> a. a \<in> A \<Longrightarrow> Congruence_Closure B a"
"\<And> b. b \<in> B \<Longrightarrow> Congruence_Closure A b"
shows "Congruence_Closure A = Congruence_Closure B"
proof(standard, standard)
  fix x 
  assume CC_A: "Congruence_Closure A x"
  show "Congruence_Closure B x"
    using CC_A Congruence_Closure_imp assms(1) by blast
next 
  fix x
  assume CC_B: "Congruence_Closure B x"
  show "Congruence_Closure A x"
    using CC_B Congruence_Closure_imp assms(2) by blast
qed

fun valid_vars :: "equation \<Rightarrow> nat \<Rightarrow> bool"
  where
    "valid_vars (a \<approx> b) n = (a < n \<and> b < n)"
  | "valid_vars (F a b \<approx> c) n = (a < n \<and> b < n \<and> c < n)"

fun valid_vars_pending :: "pending_equation \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "valid_vars_pending (One (a \<approx> b)) l = (valid_vars (a \<approx> b) (length l))"
  | "valid_vars_pending (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)) l = 
        (valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) (length l) \<and> valid_vars (F b\<^sub>1 b\<^sub>2 \<approx> b) (length l)
\<and> rep_of l a\<^sub>1 = rep_of l b\<^sub>1 \<and> rep_of l a\<^sub>2 = rep_of l b\<^sub>2)"
  | "valid_vars_pending _ _ = False"

lemma valid_vars_pending_iff: 
  "valid_vars_pending a l \<longleftrightarrow> (\<exists> b c . b < length l \<and> c < length l \<and> a = (One (b \<approx> c))) \<or>
(\<exists> b c d e f g . b < length l \<and> c < length l \<and> d < length l \<and> e < length l \<and> f < length l
 \<and> g < length l \<and> a = (Two (F b c \<approx> d) (F e f \<approx> g))
\<and> rep_of l b = rep_of l e \<and> rep_of l c = rep_of l f)"
  (is "?P \<longleftrightarrow> ?Q")
proof
  show "?P \<Longrightarrow> ?Q" apply(cases a) 
    using valid_vars_pending.elims(2) apply fastforce 
    using valid_vars_pending.elims by (metis pending_equation.distinct(1) valid_vars.simps(2))
  show "?Q \<Longrightarrow> ?P"
    apply(cases a) 
    by auto
qed

lemma valid_vars_pending_cases[consumes 1, case_names One Two]:
  assumes "valid_vars_pending eq l"
  obtains a b where "eq = One (a \<approx> b)" "a < length l" "b < length l"
  | a\<^sub>1 a\<^sub>2 a b\<^sub>1 b\<^sub>2 b where "eq = Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)" 
"a\<^sub>1 < length l" "a\<^sub>2 < length l" "a < length l" "b\<^sub>1 < length l" "b\<^sub>2 < length l" "b < length l"
"rep_of l a\<^sub>1 = rep_of l b\<^sub>1" "rep_of l a\<^sub>2 = rep_of l b\<^sub>2"
  using assms valid_vars_pending_iff by force

abbreviation nr_vars :: "congruence_closure \<Rightarrow> nat"
  where
    "nr_vars cc \<equiv> length (cc_list cc)"

definition cc_\<alpha> :: "congruence_closure \<Rightarrow> equation \<Rightarrow> bool"
  where
    "cc_\<alpha> cc x \<equiv> valid_vars x (nr_vars cc) \<and> are_congruent cc x"

definition representativeE :: "congruence_closure \<Rightarrow> equation set"
  where
    "representativeE cc = {a \<approx> rep_of (cc_list cc) a |a. a < nr_vars cc \<and> cc_list cc ! a \<noteq> a}
\<union> {F a' b' \<approx> rep_of (cc_list cc) c | a' b' c c\<^sub>1 c\<^sub>2 . a' < nr_vars cc \<and> b' < nr_vars cc \<and> c < nr_vars cc \<and>
                      cc_list cc ! a' = a' \<and> cc_list cc ! b' = b' \<and> lookup cc ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)}"


text \<open>Converts the list of pending equations to a set of pending equations.\<close>
fun pending_set :: "pending_equation list \<Rightarrow> equation set"
  where
"pending_set [] = {}"
| "pending_set ((One a)#xs) = {a} \<union> pending_set xs"
| "pending_set ((Two a b)#xs) = {a, b} \<union> pending_set xs"

lemma pending_set_empty_iff_pending_empty:
 "pending_set pe = {} \<longleftrightarrow> pe = []"
proof
  show "pending_set pe = {} \<Longrightarrow> pe = []"
    apply(induction pe rule: pending_set.induct)
    by(simp_all)
  show "pe = [] \<Longrightarrow> pending_set pe = {}" by simp
qed


lemma pending_set_union: 
"pending_set (xs @ ys) = pending_set xs \<union> pending_set ys"
  apply(induction xs rule: pending_set.induct)
  by simp_all

lemma pending_set_Cons: 
"pending_set (x # ys) = pending_set [x] \<union> pending_set ys"
  by (metis append.left_neutral append_Cons pending_set_union)

lemma pending_set_union':
 "a \<in> pending_set (xs @ ys) \<longleftrightarrow> a \<in> pending_set xs \<or> a \<in> pending_set ys" 
  by (simp add: pending_set_union)

subsection \<open>Invariants\<close>
text \<open>As described in the paper\<close>

text \<open>For cc_list_invar we use ufa_invar\<close>

text \<open>for each representative i, UseList (i) is a list of input equations \<open>f(b\<^sub>1, b\<^sub>2)=b\<close>
such that i is the representative of \<open>b\<^sub>1\<close> or of \<open>b\<^sub>2\<close> (or of both).\<close>
abbreviation use_list_valid_element
  where
"use_list_valid_element u_i_j l i \<equiv> 
    (\<exists> b\<^sub>1 b\<^sub>2 b . u_i_j = (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and> 
      ((i = rep_of l b\<^sub>1) \<or> i = rep_of l b\<^sub>2) \<and>
      (b\<^sub>1 < length l \<and> b\<^sub>2 < length l \<and> b < length l)
  )"

abbreviation use_list_invar_correctness :: "congruence_closure \<Rightarrow> bool"
  where
    "use_list_invar_correctness cc \<equiv> 
(\<forall> i < nr_vars cc . 
    (cc_list cc) ! i = i \<longrightarrow> (\<forall> j < length ((use_list cc) ! i) . 
      use_list_valid_element ((use_list cc) ! i ! j) (cc_list cc) i
  )
)"

text \<open>for all pairs of representatives (i, j), Lookup(i, j) is some input equation
\<open>f(a\<^sub>1, a\<^sub>2)=a\<close> such that i and j are the current respective representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close> whenever
such an equation exists. Otherwise, Lookup(i, j) is \<bottom>\<close>
abbreviation lookup_invar_correctness :: "congruence_closure \<Rightarrow> bool"
  where
    "lookup_invar_correctness cc \<equiv> (\<forall> i < nr_vars cc . 
  (\<forall> j < nr_vars cc .
    (cc_list cc) ! i = i \<and> (cc_list cc) ! j = j \<longrightarrow> 
    lookup_valid_element (lookup cc) (cc_list cc) i j 
  )
)"

text \<open>These invariants are needed for the termination proofs:\<close>

abbreviation proof_forest_invar_termination :: "congruence_closure \<Rightarrow> bool"
  where
    "proof_forest_invar_termination cc \<equiv> ufa_invar (proof_forest cc)"

abbreviation cc_list_invar_termination :: "congruence_closure \<Rightarrow> bool"
  where
    "cc_list_invar_termination cc \<equiv> ufa_invar (cc_list cc)"

text \<open>These invariants are needed for the validity proofs:\<close>

definition pending_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "pending_invar cc \<equiv> (\<forall> i < length (pending cc) . 
                          valid_vars_pending ((pending cc) ! i) (cc_list cc))"

lemma pending_invar_Cons: 
  "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (pe # xs), proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
\<longleftrightarrow> 
pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = xs, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
\<and> valid_vars_pending pe l"
(is "?left \<longleftrightarrow> ?right")
proof
  show "?left \<Longrightarrow> ?right"
    unfolding pending_invar_def congruence_closure.select_convs
    by fastforce
next 
  show "?right \<Longrightarrow> ?left"
    unfolding pending_invar_def congruence_closure.select_convs
    by (metis in_set_conv_nth set_ConsD)
qed

lemma pending_left_right_valid': 
  assumes valid: "valid_vars_pending pe l"
  shows "right pe < length l \<and> left pe < length l"
proof(cases pe)
  case (One x1)
  with One valid obtain x11 x12 where Constants: "x1 = (x11 \<approx> x12)" 
    by (metis equation.exhaust valid_vars_pending.simps(3))
  with One have "left pe = x11" by simp
  with Constants One valid show ?thesis by auto
next
  case (Two x21 x22)
  with valid obtain x211 x212 x213 x221 x222 x223 
    where Function: "x21 = (F x211 x212 \<approx> x213)"  "x22 = (F x221 x222 \<approx> x223)" 
    by (metis Two equation.exhaust valid_vars_pending.simps(4) valid_vars_pending.simps(5))
  then show ?thesis using Two valid by auto
qed

lemma pending_left_right_valid: 
  assumes "pending_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = (pe # xs), proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "right pe < length l \<and> left pe < length l"
  using assms pending_left_right_valid' 
  unfolding pending_invar_def congruence_closure.select_convs
  by (metis in_set_conv_nth list.set_intros(1))

text \<open>Here the invariants are put together:\<close>

definition cc_list_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "cc_list_invar cc = cc_list_invar_termination cc"

definition use_list_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "use_list_invar cc = use_list_invar_correctness cc"

definition lookup_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "lookup_invar cc \<equiv> lookup_invar_correctness cc \<and> quadratic_table (lookup cc)"

definition proof_forest_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "proof_forest_invar cc = proof_forest_invar_termination cc"

text \<open>TODO: 
Inv1: RepresentativeE is in standard form;
A set of equations E is in standard form if its equations are of the form a = b or
of the form f(a, b) = c whose (respective) left hand side terms a and f(a, b) only occur once
in E.\<close>
definition inv1 :: "congruence_closure \<Rightarrow> bool"
  where
    "inv1 cc = True"

definition inv2 :: "congruence_closure \<Rightarrow> bool"
  where
    "inv2 cc \<equiv> 
Congruence_Closure (representativeE cc \<union> pending_set (pending cc)) = Congruence_Closure (input cc)"

text \<open>The union find data structure and the proof forest have the same equivalence classes. \<close>
abbreviation pf_l_same_eq_classes :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "pf_l_same_eq_classes pf l \<equiv> (\<forall> i < length pf . (\<forall> j < length pf . rep_of l i = rep_of l j 
\<longleftrightarrow> rep_of pf i = rep_of pf j))"

definition inv_same_rep_classes :: "congruence_closure \<Rightarrow> bool"
  where
    "inv_same_rep_classes cc \<equiv> pf_l_same_eq_classes (proof_forest cc) (cc_list cc)"

lemma inv_same_rep_classes_not_divided: 
  assumes "i < length (proof_forest cc)" "j < length (proof_forest cc)" "inv_same_rep_classes cc"
  shows "rep_of (cc_list cc) i = rep_of (cc_list cc) j \<longleftrightarrow> rep_of (proof_forest cc) i = rep_of (proof_forest cc) j"
  using assms unfolding inv_same_rep_classes_def by presburger

lemma inv_same_rep_classes_divided: 
  assumes "i < length pf" "j < length pf" 
    "inv_same_rep_classes \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "rep_of l i = rep_of l j \<longleftrightarrow> rep_of pf i = rep_of pf j"
  using assms unfolding inv_same_rep_classes_def congruence_closure.select_convs by blast

text \<open>The lists in the data structure all have the same length.\<close>
definition inv_same_length :: "congruence_closure \<Rightarrow> nat \<Rightarrow> bool"
  where
    "inv_same_length cc n \<equiv> 
(((nr_vars cc = n \<and> length (use_list cc) = n) \<and> length (lookup cc) = n) \<and> 
length (proof_forest cc) = n) \<and> length (pf_labels cc) = n"

text \<open>All equations in the lookup table are also present in both relevant use_lists.\<close>
definition lookup_invar2 :: "congruence_closure \<Rightarrow> bool"
  where
"lookup_invar2 cc = (\<forall> a' b' c c\<^sub>1 c\<^sub>2.
a' < nr_vars cc \<longrightarrow> b' < nr_vars cc \<longrightarrow> (cc_list cc) ! a' = a' \<longrightarrow> (cc_list cc) ! b' = b' 
\<longrightarrow> (lookup cc) ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)
\<longrightarrow>
(F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set ((use_list cc) ! a')
\<and> (F c\<^sub>1 c\<^sub>2 \<approx> c) \<in> set ((use_list cc) ! b')
)"

text \<open>All equations in use_list are also in the congruence_closure of the data structure.\<close>
definition use_list_invar2 :: "congruence_closure \<Rightarrow> bool"
  where
"use_list_invar2 cc = (\<forall> a' eq.
a' < nr_vars cc \<longrightarrow> (cc_list cc) ! a' = a'
\<longrightarrow>
eq \<in> set ((use_list cc) ! a')
\<longrightarrow> Congruence_Closure (representativeE cc \<union> pending_set (pending cc)) eq
)"


text \<open>Invariant for the whole data structure.\<close>
abbreviation cc_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "cc_invar cc \<equiv> (((((((cc_list_invar cc \<and> use_list_invar cc) \<and> lookup_invar cc) 
        \<and> proof_forest_invar cc) \<and> inv1 cc) \<and> inv2 cc) \<and> inv_same_rep_classes cc) 
        \<and> inv_same_length cc (nr_vars cc)) \<and> pending_invar cc"




text \<open>
(1) Prove that the invariant is preserved by the two cases of propagate_loop.
(2) Then prove that it holds for a generic input of propagate_loop.
(3) Prove that it works for this specific input.
\<close>
lemma propagate_step_induct[consumes 3, case_names base update_pending update_lookup]:
  assumes 
"ufa_invar l" "a < length l" "b < length l"

"P \<lparr>cc_list = ufa_union l a b, 
    use_list = u[rep_of l a := []], 
    lookup = t, 
    pending = pe,
    proof_forest = add_edge pf a b, 
    pf_labels = add_label pfl pf a eq, 
    input = ip\<rparr>"

"\<And> l u t pe pf pfl ip u1.
P \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
\<Longrightarrow> lookup_Some t l u1
\<Longrightarrow> P \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l u1#pe,
            proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"

"\<And> l u t pe pf pfl ip u1 rep_b.
P \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr> 
\<Longrightarrow> \<not>lookup_Some t l u1
\<Longrightarrow> rep_of l b = rep_b
\<Longrightarrow>
P \<lparr>cc_list = l,
            use_list = u[rep_b := u1#(u ! rep_b)],
            lookup = update_lookup t l u1, 
            pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"

shows "P (propagate_step l u t pe pf pfl ip a b eq)"
proof-
  have loop: "P \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
\<Longrightarrow> rep_of l b = rep_b
\<Longrightarrow> 
P (propagate_loop rep_b urest 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>)"
    for l u t pe pf pfl ip rep_b urest
    proof(induction rep_b urest "\<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
arbitrary: l u t pe pf pfl ip rule: propagate_loop.induct)
      case (1 rep_b1 u11 urest1 l1 u1 t1 pe1 pf1 pfl1 ip1)
      then have *:"lookup_Some t1 l1 u11 \<Longrightarrow> P \<lparr>cc_list = l1, use_list = u1, lookup = t1, pending = link_to_lookup t1 l1 u11 # pe1, proof_forest = pf1,
             pf_labels = pfl1, input = ip1\<rparr>" using assms 
        using "1.hyps"(2) "1.prems"(1) by blast
then have **: "\<not>lookup_Some t1 l1 u11 \<Longrightarrow> P \<lparr>cc_list = l1, use_list = u1[rep_b1 := u11 # u1 ! rep_b1], lookup = update_lookup t1 l1 u11, pending = pe1,
                    proof_forest = pf1, pf_labels = pfl1, input = ip1\<rparr>" using assms 
        using "1.hyps"(2) "1.prems"(1) 
        by (simp add: "1.prems"(2) )
      with * 1 show ?case apply(cases "lookup_Some t1 l1 u11") 
        by force+
  next
    case (2 uu)
    then show ?case 
      by simp
  qed
  have "rep_of l b = rep_of (ufa_union l a b) b" 
    using assms ufa_union_aux by auto
  with loop assms show ?thesis 
    by force
qed

subsection \<open>Lemmata for Congruence_Closure with our congruence_closure data structure\<close>

lemma a_eq_rep_of_a_in_CC:
  assumes "a < length (cc_list cc)"
  shows
"Congruence_Closure (representativeE cc) (a \<approx> rep_of (cc_list cc) a)"
"Congruence_Closure (representativeE cc) (rep_of (cc_list cc) a \<approx> a)"
proof-
  have *: "rep_of (cc_list cc) a = a \<Longrightarrow> Congruence_Closure (representativeE cc) a \<approx> rep_of (cc_list cc) a" 
    using reflexive by simp
  have "rep_of (cc_list cc) a \<noteq> a \<Longrightarrow> (a \<approx> rep_of (cc_list cc) a) \<in> (representativeE cc)" unfolding representativeE_def
    using assms rep_of_refl by force
  then have "rep_of (cc_list cc) a \<noteq> a \<Longrightarrow> Congruence_Closure (representativeE cc) a \<approx> rep_of (cc_list cc) a" 
    using base by simp
  with * show "Congruence_Closure (representativeE cc) (a \<approx> rep_of (cc_list cc) a)" 
    by blast
  with symmetric show "Congruence_Closure (representativeE cc) (rep_of (cc_list cc) a \<approx> a)" 
    by simp
qed

lemma CC_F_rep_of_a_imp_F_a:
  assumes "Congruence_Closure (representativeE cc) 
(F (rep_of (cc_list cc) a) (rep_of (cc_list cc) b) \<approx> (rep_of (cc_list cc) c))"
"a < nr_vars cc" "b < nr_vars cc" "c < nr_vars cc"
  shows "Congruence_Closure (representativeE cc) (F a b \<approx> c)"
proof-
  from assms a_eq_rep_of_a_in_CC have "Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) a) \<approx> a)"
"Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) b) \<approx> b)"
"Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) c) \<approx> c)"
    by blast+
  with assms show ?thesis using Congruence_Closure.intros by metis 
qed

lemma CC_rep_of_a_imp_a:
  assumes "Congruence_Closure (representativeE cc) 
(rep_of (cc_list cc) a \<approx> rep_of (cc_list cc) c)"
"a < nr_vars cc" "c < nr_vars cc"
  shows "Congruence_Closure (representativeE cc) (a \<approx> c)"
proof-
  from assms a_eq_rep_of_a_in_CC have "Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) a) \<approx> a)"
"Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) c) \<approx> c)"
    by blast+
  with assms show ?thesis using Congruence_Closure.intros by metis 
qed

lemma CC_lookup_entry_in_CC:
  assumes "lookup_invar cc"
"(cc_list cc) ! a = a" "(cc_list cc) ! b = b" "(lookup cc) ! a ! b = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
"a < nr_vars cc" "b < nr_vars cc" "c < nr_vars cc"
  shows "Congruence_Closure (representativeE cc) (F c\<^sub>1 c\<^sub>2 \<approx> c)"
proof-
  from assms base have base: "Congruence_Closure (representativeE cc) (F a b \<approx> rep_of (cc_list cc) c)"
    unfolding representativeE_def 
    by simp
  from assms  have "c\<^sub>1 < nr_vars cc" "c\<^sub>2 < nr_vars cc" "c < nr_vars cc"
    unfolding lookup_invar_def 
    by (metis equation.inject(2) option.distinct(1) option.inject)+
  with assms a_eq_rep_of_a_in_CC have rep:
"Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) c\<^sub>1) \<approx> c\<^sub>1)"
"Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) c\<^sub>2) \<approx> c\<^sub>2)"
"Congruence_Closure (representativeE cc) ((rep_of (cc_list cc) c) \<approx> c)"
    by blast+
  from assms have a_b: "rep_of (cc_list cc) c\<^sub>1 = a" "rep_of (cc_list cc) c\<^sub>2 = b" unfolding lookup_invar_def  
    by (metis equation.inject(2) option.distinct(1) option.inject)+
  have "Congruence_Closure (representativeE cc) (F c\<^sub>1 c\<^sub>2 \<approx> rep_of (cc_list cc) c)" 
    using a_b(1) a_b(2) local.base rep transitive3 by blast
  with assms show ?thesis using Congruence_Closure.intros rep 
    by fast
qed

lemma CC_same_rep:
  assumes "rep_of (cc_list cc) a = rep_of (cc_list cc) b"
"a < nr_vars cc" "b < nr_vars cc"
shows "Congruence_Closure (representativeE cc) (a \<approx> b)"
proof-
  have "Congruence_Closure (representativeE cc) (a \<approx> rep_of (cc_list cc) a)"
"Congruence_Closure (representativeE cc) (rep_of (cc_list cc) b \<approx> b)"
     apply (simp add: a_eq_rep_of_a_in_CC(1) assms(2))
    by (simp add: a_eq_rep_of_a_in_CC(2) assms(3))
  then show ?thesis 
    by (metis assms(1) transitive1)
qed

lemma pending_a_b_in_Congruence_Closure:
  assumes "valid_vars_pending eq (cc_list cc)" "a = left eq" "b = right eq" 
  shows "Congruence_Closure (representativeE cc \<union> pending_set [eq]) (a \<approx> b)"
using assms(1) proof(induction rule: valid_vars_pending_cases)
  case (One a b)
  then show ?case 
    using assms(2) assms(3) base by auto
next
  case (Two a\<^sub>1 a\<^sub>2 a' b\<^sub>1 b\<^sub>2 b')
  have "Congruence_Closure (representativeE cc) (a\<^sub>1 \<approx> rep_of (cc_list cc) a\<^sub>1)"
"Congruence_Closure (representativeE cc) (a\<^sub>2 \<approx> rep_of (cc_list cc) a\<^sub>2)"
"Congruence_Closure (representativeE cc) (b\<^sub>1 \<approx> rep_of (cc_list cc) b\<^sub>1)"
"Congruence_Closure (representativeE cc) (b\<^sub>2 \<approx> rep_of (cc_list cc) b\<^sub>2)"
       apply (simp add: Two.hyps(2) a_eq_rep_of_a_in_CC(1))
      apply (simp add: Two.hyps(3) a_eq_rep_of_a_in_CC(1))
    apply (simp add: Two.hyps(5) a_eq_rep_of_a_in_CC(1))
    by (simp add: Two.hyps(6) a_eq_rep_of_a_in_CC(1))
  then have *: "Congruence_Closure (representativeE cc) (a\<^sub>1 \<approx> b\<^sub>1)"
"Congruence_Closure (representativeE cc) (a\<^sub>2 \<approx> b\<^sub>2)"
    using Congruence_Closure.symmetric Two.hyps(8,9) transitive1 by presburger+
  have **: "Congruence_Closure (pending_set [eq]) (F a\<^sub>1 a\<^sub>2 \<approx> a')"
"Congruence_Closure (pending_set [eq]) (F b\<^sub>1 b\<^sub>2 \<approx> b')"
    apply (simp add: Two.hyps(1) base)
    by (simp add: Two.hyps(1) base)
  have a_b: "a' = a" "b' = b" 
    apply (simp add: Two.hyps(1) assms(2))
    by (simp add: Two.hyps(1) assms(3))
  have "Congruence_Closure (pending_set [eq]) eq' \<Longrightarrow> Congruence_Closure (representativeE cc \<union> pending_set [eq]) eq'"
"Congruence_Closure (representativeE cc) eq' \<Longrightarrow> Congruence_Closure (representativeE cc \<union> pending_set [eq]) eq'"
   for eq' 
     apply (metis Congruence_Closure_union')
  by (simp add: Congruence_Closure_union)
  with * ** a_b monotonic show ?case
    by blast
qed

lemma pending_a_b_in_Congruence_Closure':
  assumes "valid_vars_pending eq (cc_list cc)" "a = left eq" "b = right eq" 
  shows "Congruence_Closure (representativeE cc \<union> pending_set (eq#pe)) (a \<approx> b)"
  by (metis Congruence_Closure_union assms pending_a_b_in_Congruence_Closure pending_set_Cons sup_assoc)

subsection \<open>add_edge correctness lemmata\<close>

lemma hd_tl_list: "length xs > 1 \<Longrightarrow> hd (tl xs) = xs ! 1"
  by (metis One_nat_def drop0 drop_Suc hd_drop_conv_nth)

text \<open>If the representative changes after a list update, then it must be equal to 
      the representative of the updated element.\<close>
lemma rep_of_fun_upd3:
  assumes "ufa_invar l" "x < length l" "y < length l""x' < length l" "y' < length l"
    "rep_of l x = rep_of l y" "rep_of (CONST list_update l x' y') x \<noteq> rep_of (CONST list_update l x' y') y"
    "rep_of l y = rep_of (CONST list_update l x' y') y"  "rep_of l x' \<noteq> rep_of l y'"
  shows "rep_of (CONST list_update l x' y') x = rep_of (CONST list_update l x' y') y'"
  using assms proof(induction rule: rep_of_induct)
  case (base i)
  then have "i = x'" 
    by (metis nth_list_update' rep_of_refl)
  from base have "ufa_invar (l[x' := y'])" 
    by (simp add: ufa_invar_fun_upd')
  with base show ?case 
    by (metis \<open>i = x'\<close> rep_of_fun_upd_rep_of rep_of_refl)
next
  case (step i)
  then show ?case proof(cases "rep_of (l[x' := y']) (l ! i) = rep_of (l[x' := y']) y")
    case True
    with step have "i = x'" 
      by (metis length_list_update nth_list_update_neq rep_of_idx ufa_invar_fun_upd')
    from step have "ufa_invar (l[x' := y'])" 
      using ufa_invar_fun_upd' by presburger
    then show ?thesis 
      by (metis \<open>i = x'\<close> length_list_update nth_list_update_eq rep_of_idx step.prems(2))
  next
    case False
    with step have "rep_of (l[x' := y']) (l ! i) = rep_of (l[x' := y']) y'"
      using rep_of_idx by presburger
    with step show ?thesis 
      by (metis length_list_update nth_list_update_eq nth_list_update_neq rep_of_idx ufa_invar_fun_upd')
  qed
qed

text \<open>The \<open>rep_of (add_edge l x y)\<close> behaves exactly the same as \<open>rep_of (ufa_union l x y)\<close>.\<close>
lemma rep_of_add_edge_aux:
  assumes "ufa_invar l"
    and "x < length l"
    and "y < length l"
    and "i < length l"
    and "rep_of l x \<noteq> rep_of l y"
  shows "rep_of (add_edge l x y) i = (if rep_of l i = rep_of l x then rep_of l y else rep_of l i)"
proof-
  from assms have dom: "add_edge_dom (l, x, y)" 
    by (simp add: add_edge_domain)
  with assms have "ufa_invar (add_edge l x y)" 
    by (simp add: add_edge_ufa_invar_invar)
  from dom assms show ?thesis 
  proof(induction rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case 
    proof(cases "pf ! e = e")
      case True
        \<comment>\<open>e is a root, only one edge to e' is added\<close>
      then have add_edge: "add_edge pf e e' = pf[e := e']" 
        by (simp add: "1.hyps" add_edge.psimps)
      have "rep_of pf e = e" 
        by (simp add: True rep_of_refl)
      \<comment>\<open>the new rep of i is either e', if it was e, or it doesn't change.\<close>
      then show ?thesis proof(cases "rep_of pf i = e")
        case True
        then show ?thesis 
          using "1.prems" add_edge \<open>rep_of pf e = e\<close> rep_of_fun_upd_rep_of by auto
      next
        case False
        with rep_of_fun_upd' show ?thesis 
          using "1.prems" \<open>rep_of pf e = e\<close> add_edge by force
      qed
    next
      case False
      \<comment>\<open>Inductive step: first we need to prove the assumptions of the inductive hypothesis.\<close>
      then have add_edge: "add_edge pf e e' = add_edge (pf[e := e']) (pf ! e) e"
        by (simp add: "1.hyps" add_edge.psimps)
      from False add_edge_correctness "1.prems" 
        \<comment>\<open>Paths are useful for proving that certain nodes are in the same connected component,
            which means they have the same representative.\<close>
      have inverted_p: "path (add_edge pf e e') e' ([e'] @ rev (path_to_root pf e)) (rep_of pf e)" 
        by auto
      have invar: "ufa_invar (pf[e := e'])" 
        by (simp add: "1.prems" ufa_invar_fun_upd')
      have "add_edge pf e e' ! e = e'" 
        by (simp add: "1.prems" nth_add_edge_e_eq_e')
      with "1.prems" have "hd (tl ([e'] @ rev (path_to_root pf e))) = e" 
        by (metis empty_append_eq_id hd_rev list.sel(3) path_last path_to_root_correct snoc_eq_iff_butlast' tl_append2)
      with path_to_root_length "1.prems" have length_path: "length ([e'] @ rev (path_to_root pf e)) > 1 "
        by simp
      with "1.prems" have "([e'] @ rev (path_to_root pf e)) ! 1 = e"
        by (metis \<open>hd (tl ([e'] @ rev (path_to_root pf e))) = e\<close> hd_tl_list)             
      have "ufa_invar (add_edge pf e e')" 
        using 1 add_edge_ufa_invar_invar by auto
      with nodes_path_rep_of inverted_p length_path have "rep_of (add_edge pf e e') e = rep_of (add_edge pf e e') e'"
        using \<open>([e'] @ rev (path_to_root pf e)) ! 1 = e\<close> by fastforce
      from rep_of_fun_upd "1.prems" have rep_of_parent: "rep_of (pf[e := e']) (pf ! e) = rep_of pf (pf ! e)" 
        by (metis False path_remove_child path_to_root_correct ufa_invarD(2))
      with "1.prems" have  "rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e" 
        by (metis invar length_list_update nth_list_update_eq rep_of_fun_upd' rep_of_idx)
          \<comment>\<open>The induction hypothesis tells us that the claim holds for the parent of e\<close>
      with 1(2)[OF False invar] 1 have IH: "rep_of (add_edge (pf[e := e']) (pf ! e) e) i =
    (if rep_of (pf[e := e']) i = rep_of (pf[e := e']) (pf ! e) then rep_of (pf[e := e']) e
     else rep_of (pf[e := e']) i)" 
        by (metis length_list_update ufa_invarD(2))     
      then show ?thesis 
      proof(cases "rep_of pf i = rep_of pf e")
        case True
        then show ?thesis proof(cases "rep_of (pf[e := e']) i = rep_of (pf[e := e']) (pf ! e)")
          case True
          \<comment>\<open>i was in the same connected component as e, and after adding the edge (e,e'), 
          i is in the same connected component as the parent of e, 
          therefore i is nearer to the root than e.\<close>
          with "1.prems" show ?thesis 
            by (metis IH add_edge invar length_list_update nth_list_update_eq rep_of_fun_upd' rep_of_idx rep_of_parent)
        next
          case False
            \<comment>\<open>i was in the same connected component as e, and after adding the edge (e,e'), 
          i is not in the same connected component as the parent of e.
          Therefore e is nearer to the root than i, and the new representative of i
          is rep_of e', which is also the new representative of e.\<close>
          with True rep_of_fun_upd3 "1.prems" have *: "rep_of (pf[e := e']) i = rep_of (pf[e := e']) e" 
            by (metis \<open>rep_of (pf[e := e']) (pf ! e) \<noteq> rep_of (pf[e := e']) e\<close> rep_of_parent rep_of_step ufa_invarD(2))
          with "1.prems" have "rep_of (pf[e := e']) e = rep_of (pf[e := e']) e'" 
            by (metis False rep_of_fun_upd3 rep_of_idx rep_of_parent ufa_invarD(2))
          then show ?thesis 
            using "1.prems" IH True * add_edge rep_of_fun_upd' by presburger
        qed   
      next
        case False
        then show ?thesis 
          using "1.prems" add_edge IH rep_of_parent rep_of_fun_upd' rep_of_idx by presburger
      qed
    qed
  qed
qed

lemma rep_of_add_edge_invar: 
  assumes "rep_of l a = rep_of l b" "rep_of l x1 \<noteq> rep_of l x2"
    "ufa_invar l" "a < length l" "b < length l " "x1 < length l " "x2 < length l"
  shows "rep_of (add_edge l x1 x2) a = rep_of (add_edge l x1 x2) b"
  by (simp add: assms rep_of_add_edge_aux)

lemma add_edge_preserves_length:
  "add_edge_dom (pf, a, b) \<Longrightarrow> length (add_edge pf a b) = length pf"
  apply(induction pf a b rule: add_edge.pinduct)
  by (simp add: add_edge.psimps)

lemma add_edge_preserves_length':
  assumes "ufa_invar pf" "a < length pf" "b < length pf" "rep_of pf a \<noteq> rep_of pf b" 
  shows "length (add_edge pf a b) = length pf"
  using add_edge_domain add_edge_preserves_length assms by blast

lemma add_edge_inv_same_rep_classes_invar:  
  assumes  "pf_l_same_eq_classes pf l" "ufa_invar pf" "ufa_invar l"
    "a < length l" "b < length l"
    "rep_of l a \<noteq> rep_of l b" "length pf = length l"
  shows "pf_l_same_eq_classes (add_edge pf a b) (ufa_union l a b)"
proof(standard, standard, standard, standard)
  fix i j 
  assume i_j: "i < length (add_edge pf a b)" "j < length (add_edge pf a b)"
  from assms have "add_edge_dom (pf, a, b)" 
    using add_edge_domain by auto
  then have "length (add_edge pf a b) = length pf" 
    by (simp add: add_edge_preserves_length)
  then show "(rep_of (ufa_union l a b) i = rep_of (ufa_union l a b) j) =
           (rep_of (add_edge pf a b) i = rep_of (add_edge pf a b) j)" 
    using assms i_j rep_of_add_edge_aux ufa_union_aux by auto
qed

subsection \<open>Additional helper lemmata\<close>

lemma update_lookup_unchanged:
  assumes "rep_of l c\<^sub>1 \<noteq> a' \<or> rep_of l c\<^sub>2 \<noteq> b'"
  shows "update_lookup t l (F c\<^sub>1 c\<^sub>2 \<approx> c) ! a' ! b' = t ! a' ! b'"
  using assms unfolding update_lookup.simps 
  by (metis nth_list_update_eq nth_list_update_neq nth_update_invalid)

lemma lookup_step_unchanged_step:
  assumes "ufa_invar l" "a < length l" "b < length l"
"t ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)"
  shows "(lookup (propagate_step l u t pe pf pfl ip a b eq)) ! a' ! b' = t ! a' ! b'"
using assms proof(induction rule: propagate_step_induct)
  case base
  then show ?case 
    by simp
next
  case (update_pending l u t pe pf pfl ip u1)
  then show ?case 
    by auto
next
  case (update_lookup l u t pe pf pfl ip u1 rep_b)
  then show ?case proof(cases u1)
    case (Constants x11 x12)
    then show ?thesis 
      using update_lookup.IH update_lookup.prems by auto
  next
    case (Function x21 x22 x23)
    then show ?thesis 
      by (metis congruence_closure.select_convs(3) is_none_code(2) lookup_Some.simps(1) update_lookup.IH update_lookup.hyps(1) update_lookup.prems update_lookup_unchanged)
  qed
qed

lemma use_list_invar_function: 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "i < length l" "j < length (u ! i)" "l ! i = i"
  obtains a\<^sub>1 a\<^sub>2 a where "(u ! i) ! j = (F a\<^sub>1 a\<^sub>2 \<approx> a)"
  using assms unfolding use_list_invar_def by fastforce

lemma use_list_invar_less_n: 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe,  proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "i < length l" "j < length (u ! i)" "l ! i = i" "(u ! i) ! j = (F a b \<approx> c)"
  shows "a < length l" "b < length l" "c < length l"
  using assms unfolding use_list_invar_def by fastforce+

lemma use_list_invar_rep_eq_i: 
  assumes "use_list_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "i < length l"  "l ! i = i" "(F a b \<approx> c) \<in> set (u ! i)"
  shows "rep_of l a = i \<or> rep_of l b = i"
proof-
  from assms(4) obtain j where "j < length (u ! i)" "u ! i ! j = (F a b \<approx> c)"
    by (metis in_set_conv_nth)
  with assms show ?thesis unfolding use_list_invar_def by fastforce
qed

lemma lookup_invar_less_n:
  assumes "lookup_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
    "(t ! i) ! j = Some (F f g \<approx> h)" "i < length l" "j < length l" "l ! i = i" "l ! j = j"
  shows "f < length l" "g < length l" "h < length l"
  using assms unfolding lookup_invar_def by fastforce+


end