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
  | transitive: "Congruence_Closure S (a \<approx> b) \<Longrightarrow> Congruence_Closure S (b \<approx> c) \<Longrightarrow> Congruence_Closure S (a \<approx> c)"
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
  using transitive apply blast
  using monotonic apply blast
  done

lemma CC_union_correct: 
  "CC_union (Congruence_Closure S) eq' eq = Congruence_Closure (S \<union> {eq'}) eq"
proof
  show "CC_union (Congruence_Closure S) eq' eq \<Longrightarrow> Congruence_Closure (S \<union> {eq'}) eq"
    unfolding CC_union_def
    apply(induction "{eqa |eqa. Congruence_Closure S eqa} \<union> {eq'}" eq rule: Congruence_Closure.induct)
    using base Congruence_Closure_union apply blast
    using reflexive apply blast
    using symmetric apply blast
    using transitive apply blast
    using monotonic apply blast
    done
next
  show "Congruence_Closure (S \<union> {eq'}) eq \<Longrightarrow> CC_union (Congruence_Closure S) eq' eq"
    apply(induction "S \<union> {eq'}" eq rule: Congruence_Closure.induct)
    unfolding CC_union_def 
    using base apply auto[1]
    using reflexive apply auto[1]
    using symmetric apply auto[1]
    using transitive apply blast
    using monotonic apply blast
    done
qed


fun valid_vars :: "equation \<Rightarrow> nat \<Rightarrow> bool"
  where
    "valid_vars (a \<approx> b) n = (a < n \<and> b < n)"
  | "valid_vars (F a b \<approx> c) n = (a < n \<and> b < n \<and> c < n)"

fun valid_vars_pending :: "pending_equation \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "valid_vars_pending (One (a \<approx> b)) pf n = (valid_vars (a \<approx> b) n)"
  | "valid_vars_pending (Two (F a\<^sub>1 a\<^sub>2 \<approx> a) (F b\<^sub>1 b\<^sub>2 \<approx> b)) pf n = 
        (valid_vars (F a\<^sub>1 a\<^sub>2 \<approx> a) n \<and> valid_vars (F b\<^sub>1 b\<^sub>2 \<approx> b) n)"
  | "valid_vars_pending _ _ _ = False"

abbreviation nr_vars :: "congruence_closure \<Rightarrow> nat"
  where
    "nr_vars cc \<equiv> length (cc_list cc)"

definition cc_\<alpha> :: "congruence_closure \<Rightarrow> equation \<Rightarrow> bool"
  where
    "cc_\<alpha> cc x \<equiv> valid_vars x (nr_vars cc) \<and> are_congruent cc x"


subsection \<open>Invariants\<close>
text \<open>As described in the paper\<close>

text \<open>For cc_list_invar we use ufa_invar\<close>

text \<open>for each representative i, UseList (i) is a list of input equations \<open>f(b\<^sub>1, b\<^sub>2)=b\<close>
such that i is the representative of \<open>b\<^sub>1\<close> or of \<open>b\<^sub>2\<close> (or of both).\<close>
abbreviation use_list_invar_correctness :: "congruence_closure \<Rightarrow> bool"
  where
    "use_list_invar_correctness cc \<equiv> (\<forall> i < nr_vars cc . (\<forall> j < length ((use_list cc) ! i) . 
(cc_list cc) ! i = i \<longrightarrow> (\<exists> b\<^sub>1 b\<^sub>2 b .
use_list cc ! i ! j = (F b\<^sub>1 b\<^sub>2 \<approx> b) \<and> 
(i = rep_of (cc_list cc) b\<^sub>1) \<or> i = rep_of (cc_list cc) b\<^sub>2)))"

text \<open>for all pairs of representatives (i, j), Lookup(i, j) is some input equation
\<open>f(a\<^sub>1, a\<^sub>2)=a\<close> such that i and j are the current respective representatives of \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close> whenever
such an equation exists. Otherwise, Lookup(i, j) is \<bottom>\<close>
abbreviation lookup_invar_correctness :: "congruence_closure \<Rightarrow> bool"
  where
    "lookup_invar_correctness cc \<equiv> (\<forall> i < nr_vars cc . (\<forall> j < nr_vars cc . 
(cc_list cc) ! i = i \<and> (cc_list cc) ! j = j \<longrightarrow>
lookup cc ! i ! j = None \<or> (\<exists> a\<^sub>1 a\<^sub>2 a . lookup cc ! i ! j = Some (F a\<^sub>1 a\<^sub>2 \<approx> a) \<and> 
rep_of (cc_list cc) a\<^sub>1 = i \<and> rep_of (cc_list cc) a\<^sub>2 = j)))"

definition representativeE :: "congruence_closure \<Rightarrow> equation set"
  where
    "representativeE cc = {a \<approx> rep_of (cc_list cc) a |a.  a < nr_vars cc \<and> cc_list cc ! a \<noteq> a}
\<union> {F a' b' \<approx> rep_of (cc_list cc) c | a' b' c c\<^sub>1 c\<^sub>2 . a' < nr_vars cc \<and> b' < nr_vars cc \<and> c < nr_vars cc \<and>
                      cc_list cc ! a' = a' \<and> cc_list cc ! b' = b' \<and> lookup cc ! a' ! b' = Some (F c\<^sub>1 c\<^sub>2 \<approx> c)}"

text \<open>These invariants are needed for the termination proofs:\<close>

abbreviation proof_forest_invar_termination :: "congruence_closure \<Rightarrow> bool"
  where
    "proof_forest_invar_termination cc \<equiv> ufa_invar (proof_forest cc)"

text \<open>These invariants are needed for the validity proofs:\<close>

abbreviation pending_invar :: "pending_equation list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "pending_invar pe pf n \<equiv> (\<forall> i < length pe . valid_vars_pending (pe ! i) pf n)"

lemma pending_invar_Cons: 
  "pending_invar (pe # xs) pf n \<longleftrightarrow> pending_invar xs pf n \<and> valid_vars_pending pe pf n"
proof
  show "pending_invar (pe # xs) pf n \<Longrightarrow> pending_invar xs pf n \<and> valid_vars_pending pe pf n"
    by fastforce
next 
  show "pending_invar xs pf n \<and> valid_vars_pending pe pf n \<Longrightarrow> pending_invar (pe # xs) pf n"
    by (metis in_set_conv_nth set_ConsD)
qed

lemma pending_left_right_valid: 
  assumes "pending_invar (pe # xs) pf n"
  shows "right pe < n \<and> left pe < n"
proof(cases pe)
  case (One x1)
  have valid: "valid_vars_pending pe pf n" 
    using assms by auto
  with One valid obtain x11 x12 where Constants: "x1 = (x11 \<approx> x12)" 
    by (metis equation.exhaust valid_vars_pending.simps(3))
  with One have "left pe = x11" by simp
  with Constants One valid show ?thesis by auto
next
  case (Two x21 x22)
  have valid: "valid_vars_pending pe pf n" 
    using assms by auto
  with valid obtain x211 x212 x213 x221 x222 x223 
    where Function: "x21 = (F x211 x212 \<approx> x213)"  "x22 = (F x221 x222 \<approx> x223)" 
    by (metis Two equation.exhaust valid_vars_pending.simps(4) valid_vars_pending.simps(5))
  then show ?thesis using Two valid by auto
qed



text \<open>Here the invariants are put together:\<close>

definition use_list_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "use_list_invar cc = use_list_invar_correctness cc"

definition lookup_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "lookup_invar cc \<equiv> lookup_invar_correctness cc"

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
Congruence_Closure (representativeE cc) = Congruence_Closure (set (input cc))"

text \<open>The union find data structure and the proof forest have the same equivalence classes. \<close>
abbreviation pf_l_same_eq_classes :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "pf_l_same_eq_classes pf l \<equiv> (\<forall> i < length pf . (\<forall> j < length pf . rep_of l i = rep_of l j 
\<longleftrightarrow> rep_of pf i = rep_of pf j))"

definition inv3 :: "congruence_closure \<Rightarrow> bool"
  where
    "inv3 cc \<equiv> pf_l_same_eq_classes (proof_forest cc) (cc_list cc)"

lemma inv3_divided: 
  assumes "i < length pf" "j < length pf" 
    "inv3 \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>"
  shows "rep_of l i = rep_of l j \<longleftrightarrow> rep_of pf i = rep_of pf j"
  using assms unfolding inv3_def congruence_closure.select_convs by blast

lemma cc_\<alpha>_eq_CC_representativeE: "cc_\<alpha> cc (s \<approx> t) = Congruence_Closure (representativeE cc) (s \<approx> t)"
  sorry

abbreviation cc_invar :: "congruence_closure \<Rightarrow> bool"
  where
    "cc_invar cc \<equiv> use_list_invar cc \<and> lookup_invar cc \<and> proof_forest_invar cc \<and> inv1 cc \<and> inv2 cc \<and> inv3 cc"

lemma cc_invar_initial_cc: "cc_invar (initial_cc n)"
  sorry


text \<open>The length of all arrays of congruence_closure is always nr_vars cc\<close>
lemma length_initial_cc:
  "nr_vars (initial_cc n) = n"
  "nr_vars (initial_cc n) = length (use_list (initial_cc n))"
  "nr_vars (initial_cc n) = length (lookup (initial_cc n))"
  "nr_vars (initial_cc n) = length (proof_forest (initial_cc n))"
  "nr_vars (initial_cc n) = length (pf_labels (initial_cc n))"
  by auto

lemma set_lookup_preserves_length:
  "length t = n \<Longrightarrow> length (set_lookup t a b) = n"
  apply(induction t a b rule: set_lookup.induct)
  by auto

lemma add_edge_preserves_length:
  "add_edge_dom (pf, a, b) \<Longrightarrow> length pf = n \<Longrightarrow> length (add_edge pf a b) = n"
  apply(induction pf a b rule: add_edge.pinduct)
  by (simp add: add_edge.psimps)

lemma add_label_preserves_length:
  "add_label_dom (pfl, a, b, c) \<Longrightarrow> length pfl = n \<Longrightarrow> length (add_label pfl a b c) = n"
  apply(induction pfl a b c rule: add_label.pinduct)
  by (simp add: add_label.psimps)

lemma propagate_preserves_length_cc_list:
  assumes "propagate_dom (a, cc)" 
  shows "nr_vars cc = n \<Longrightarrow> nr_vars (propagate a cc) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  by auto

lemma propagate_preserves_length_use_list:
  assumes "propagate_dom (a, cc)" "length (use_list cc) = n "
  shows "length (use_list (propagate a cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def 
  by auto

lemma propagate_preserves_length_lookup:
  assumes "propagate_dom (a, cc)" "length (lookup cc) = n" 
  shows "length (lookup (propagate a cc)) = n"
  using assms apply(induction rule: propagate.pinduct)
  unfolding propagate.psimps Let_def
  using set_lookup_preserves_length
  by auto


lemma hd_tl_list: "length xs > 1 \<Longrightarrow>hd(tl xs) = xs ! 1"
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
      then have add_edge: "add_edge pf e e' = pf[e := e']" 
        by (simp add: "1.hyps" add_edge.psimps)
      have "rep_of pf e = e" 
        by (simp add: True rep_of_refl)
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
      then have add_edge: "add_edge pf e e' = add_edge (pf[e := e']) (pf ! e) e"
        by (simp add: "1.hyps" add_edge.psimps)
      from False add_edge_correctness "1.prems" 
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
      with 1(2)[OF False invar] 1 have IH: "rep_of (add_edge (pf[e := e']) (pf ! e) e) i =
    (if rep_of (pf[e := e']) i = rep_of (pf[e := e']) (pf ! e) then rep_of (pf[e := e']) e
     else rep_of (pf[e := e']) i)" 
        by (metis length_list_update ufa_invarD(2))     
      then show ?thesis 
      proof(cases "rep_of pf i = rep_of pf e")
        case True
        then show ?thesis proof(cases "rep_of (pf[e := e']) i = rep_of (pf[e := e']) (pf ! e)")
          case True
          with "1.prems" show ?thesis 
            by (metis IH add_edge invar length_list_update nth_list_update_eq rep_of_fun_upd' rep_of_idx rep_of_parent)
        next
          case False
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
    "ufa_invar l" "a < length l" "b < length l ""x1 < length l ""x2 < length l"
  shows "rep_of (add_edge l x1 x2) a = rep_of (add_edge l x1 x2) b"
proof-
  from assms have dom: "add_edge_dom (l, x1, x2)" 
    by (simp add: add_edge_domain)
  from dom assms show ?thesis 
  proof(induction rule: add_edge.pinduct)
    case (1 pf e e')
    then show ?case 
    proof(cases "pf ! e = e")
      case True
      then have "add_edge pf e e' = pf[e := e']" 
        by (simp add: "1.hyps" add_edge.psimps)
      then show ?thesis 
        by (metis "1.prems" rep_of_add_edge_aux)
    next
      case False
      then show ?thesis 
        by (simp add: "1.prems" rep_of_add_edge_aux)
    qed
  qed
qed

lemma add_edge_inv3_invar:  
  assumes  "pf_l_same_eq_classes pf l" "ufa_invar pf" "ufa_invar l"
    "a < length pf" "b < length pf" "a < length l" "b < length l"
    "rep_of l a \<noteq> rep_of l b"
  shows "pf_l_same_eq_classes (add_edge pf a b) (ufa_union l a b)"
proof(standard, standard, standard, standard)
  fix i j 
  assume i_j: "i < length (add_edge pf a b)" "j < length (add_edge pf a b)"
  from assms have "add_edge_dom (pf, a, b)" 
    using add_edge_domain by auto
  then have "length (add_edge pf a b) = length pf" 
    by (simp add: add_edge_preserves_length)
  show "(rep_of (ufa_union l a b) i = rep_of (ufa_union l a b) j) =
           (rep_of (add_edge pf a b) i = rep_of (add_edge pf a b) j)" 
  proof (cases "rep_of l i = rep_of l j")
    case True
    with assms i_j show ?thesis 
      by (metis (no_types, lifting) \<open>length (add_edge pf a b) = length pf\<close> rep_of_add_edge rep_of_ufa_union)
  next
    case False
    from rep_of_ufa_union[OF assms(3,6,7)] rep_of_add_edge[OF assms(2,4,5)] assms i_j show ?thesis 
      sorry
      by (metis (no_types, lifting) \<open>length (add_edge pf a b) = length pf\<close>)
qed


lemma propagate_preserves_length_proof_forest:
  assumes "propagate_dom (a, cc)" "length (proof_forest cc) = n" "length (cc_list cc) = n" "proof_forest_invar cc"
    "pending_invar a (proof_forest cc) n" "inv3 cc"
  shows "length (proof_forest (propagate a cc)) = n"
  using assms proof(induction a cc rule: propagate.pinduct)
  case (1 cc)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 pe xs l u t pf pfl ip) 
  define a where "a = left pe"
  define b where "b = right pe"
  from 2 have *: "length pf = n" "ufa_invar pf" 
    unfolding congruence_closure.select_convs proof_forest_invar_def by auto
  from 2 a_def b_def pending_left_right_valid have a_b: "a < n" "b < n"  
    by auto
  show ?case proof(cases "rep_of l a = rep_of l b")
    case True
    then have "propagate (pe # xs)
         \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
  = propagate xs \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>" using a_def b_def propagate_simps
      by (metis "2.hyps" propagate_simp2')
    moreover have "pending_invar xs
     (proof_forest \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>) n"
      using "2.prems"(3) pending_invar_Cons by blast
    ultimately show ?thesis using 2 True a_def b_def by metis
next
  case False
  with 2 have "rep_of pf a \<noteq> rep_of pf b" 
    by (metis "*"(1) a_b(1) a_b(2) inv3_divided)
  with add_edge_domain a_b * have dom: "add_edge_dom (pf, a, b)"
    by metis
  with 2 add_edge_preserves_length * have "length (add_edge pf a b) = n"
    by presburger
  from * a_b dom add_edge_ufa_invar_invar have "ufa_invar (add_edge pf a b)" 
    by (simp add: \<open>rep_of pf a \<noteq> rep_of pf b\<close>)
  have " pending_invar (xs @ map (link_to_lookup t) (filter (lookup_Some t) (u ! rep_of l a))) (add_edge pf a b)
     n "sorry
  have "propagate (pe # xs)
         \<lparr>cc_list = l, use_list = u, lookup = t, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
              = propagate (xs @ (map (link_to_lookup t) (filter (lookup_Some t) (u ! rep_of l a))))
              \<lparr>cc_list = ufa_union l a b, 
              use_list = (u[rep_of l a := []])[rep_of l b := (u ! rep_of l b) @ (filter (lookup_None t) (u ! rep_of l a))], 
              lookup = set_lookup t (filter (lookup_None t) (u ! rep_of l a)) l,
              proof_forest = add_edge pf a b, pf_labels = add_label pfl pf a pe, input = ip\<rparr>" 
    using "2.hyps" False a_def b_def propagate_simp3 by blast
  with False 2 propagate_simps show ?thesis unfolding a_def b_def 
  proof_forest_invar_def inv3_def
congruence_closure.select_convs  sorry
qed

  
qed

lemma propagate_preserves_length_pf_labels:
  assumes "propagate_dom (a, cc)" "length (pf_labels cc) = n" "ufa_invar (proof_forest cc)"
  shows "length (pf_labels (propagate a cc)) = n"
  using assms proof(induction rule: propagate.pinduct)
  case (1 cc)
  then show ?case 
    by (simp add: propagate.psimps(1))
next
  case (2 pe xs l u t pf pfl ip)
  define a where "a = left pe"
  have "a < length pf" sorry
  then have "add_label_dom (pfl, pf, a, pe)"
    sorry
  with 2 add_label_preserves_length a_def propagate.psimps(2) show ?case 
    by (smt (verit) congruence_closure.select_convs(5) )
qed


lemma rep_of_ufa_union:
  assumes  "ufa_invar l" "a < length l" "b < length l"
  shows"rep_of l k = rep_of l a \<Longrightarrow> rep_of (ufa_union l a b) k = rep_of l b" 
"rep_of l k = rep_of l b \<Longrightarrow> rep_of (ufa_union l a b) k = rep_of l b" 
"rep_of l k \<noteq> rep_of l a \<Longrightarrow> rep_of l k \<noteq> rep_of l b \<Longrightarrow> rep_of (ufa_union l a b) k = rep_of l k" 
  sorry

lemma rep_of_add_edge:
  assumes "ufa_invar pf" "a < length pf" "b < length pf"
  shows  "rep_of pf k = rep_of pf a \<Longrightarrow> rep_of (add_edge pf a b) k = rep_of pf b" 
"rep_of pf k = rep_of pf b \<Longrightarrow> rep_of (add_edge pf a b) k = rep_of pf b"
"rep_of pf k \<noteq> rep_of pf a \<Longrightarrow> rep_of l k \<noteq> rep_of l b \<Longrightarrow> rep_of (add_edge pf a b) k = rep_of pf k"
  sorry

end