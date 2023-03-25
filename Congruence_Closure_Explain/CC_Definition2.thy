chapter \<open>Congruence Closure Algorithm with Explain Operation\<close>
theory CC_Definition2
  imports CC_Explain_Correctness_TODO
begin 

text \<open>We extend the congruence closure data structure with timestamps for the edges,
which tell us in which order the edges were added. \<close>

record congruence_closure_t =
  congruence_closure + 
  time :: "nat"
  timestamps :: "nat list" 

text \<open>Implementation of the timestamps\<close>

function (domintros) add_timestamp :: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
"add_timestamp pf ti e e' k = 
(if pf ! e = e then (ti[e := k]) else add_timestamp (pf[e := e']) (ti[e := k]) (pf ! e) e (ti ! e))"
  by pat_completeness auto

lemma add_timestamp_dom_if_add_edge_dom:
   "add_edge_dom (pf, e, e') \<longleftrightarrow> add_timestamp_dom (pf, ti, e, e', k)"
proof
  show "add_edge_dom (pf, e, e') \<Longrightarrow> add_timestamp_dom (pf, ti, e, e', k)"
    apply(induction arbitrary: ti k rule: add_edge.pinduct)
    using add_timestamp.domintros by blast
  show "add_timestamp_dom (pf, ti, e, e', k) \<Longrightarrow> add_edge_dom (pf, e, e')"
    apply(induction arbitrary: ti k rule: add_timestamp.pinduct)
    using add_edge.domintros by blast
qed

lemma add_timestamp_domain: 
  assumes "ufa_invar l" "y < length l" "y' < length l" "rep_of l y \<noteq> rep_of l y'"
  shows "add_timestamp_dom (l, ti, y, y', k)"
  using add_edge_domain add_timestamp_dom_if_add_edge_dom assms by auto

abbreviation propagate_step_t
  where 
    "propagate_step_t l u t pe pf pfl ip a b eq k ti \<equiv>
 congruence_closure.extend (propagate_step l u t pe pf pfl ip a b eq)
    \<lparr>time = k + 1,
    timestamps = add_timestamp pf ti a b k\<rparr>"

function (domintros) propagate_t :: "congruence_closure_t \<Rightarrow> congruence_closure_t"
  where
    "propagate_t cc = 
(let l = cc_list cc;
u = use_list cc;
t = lookup cc;
pe = pending cc;
pf = proof_forest cc;
pfl = pf_labels cc;
ip = input cc;
k = time cc;
ti = timestamps cc
 in (case pe of 
[] \<Rightarrow> cc |
eq # pe \<Rightarrow>
(let a = left eq; b = right eq in
  (if rep_of l a = rep_of l b 
    then propagate_t \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
f_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>
    else
      propagate_t (propagate_step_t l u t pe pf pfl ip a b eq k ti)
))))"
  by pat_completeness auto

lemma propagate_t_simps1[simp]:
  assumes "propagate_t_dom cc"
    "pending cc = []"
  shows "propagate_t cc = cc"
  using assms propagate_t.psimps by fastforce

lemma propagate_t_simps2[simp]:
  assumes "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>"
    "rep_of l (left eq) = rep_of l (right eq)"
  shows "propagate_t 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr>
 = propagate_t \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, 
pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>"
  using assms propagate_t.psimps unfolding Let_def Case_def by auto

lemma propagate_simps3[simp]:
  assumes "propagate_t_dom \<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), 
proof_forest = pf, pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>"
    "rep_of l (left eq) \<noteq> rep_of l (right eq)"
  shows "propagate_t 
\<lparr>cc_list = l, use_list = u, lookup = t, pending = (eq # pe), proof_forest = pf, pf_labels = pfl, 
input = ip, time = k, timestamps = ti\<rparr>
 = propagate_t (propagate_step_t l u t pe pf pfl ip (left eq) (right eq) eq k ti)"
  using assms propagate_t.psimps unfolding Let_def Case_def by auto

fun merge_t :: "congruence_closure_t \<Rightarrow> equation \<Rightarrow> congruence_closure_t"
  where 
    "merge_t cc
(a \<approx> b) =
(let l = cc_list cc;
u = use_list cc;
t = lookup cc;
pe = pending cc;
pf = proof_forest cc;
pfl = pf_labels cc;
ip = input cc;
k = time cc;
ti = timestamps cc
 in 
  propagate_t 
    \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b)#pe, 
proof_forest = pf, pf_labels = pfl, input = insert (a \<approx> b) ip, time = k, timestamps = ti\<rparr>)"

| "merge_t cc 
(F a\<^sub>1 a\<^sub>2 \<approx> a) =
(let l = cc_list cc;
u = use_list cc;
t = lookup cc;
pe = pending cc;
pf = proof_forest cc;
pfl = pf_labels cc;
ip = input cc;
k = time cc;
ti = timestamps cc
 in 
(if (lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a))
  then propagate_t \<lparr>cc_list = l, use_list = u, lookup = t, 
            pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a)#pe, proof_forest = pf, pf_labels = pfl, 
input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, time = k, timestamps = ti\<rparr>
  else \<lparr>cc_list = l, 
          use_list = (u[rep_of l a\<^sub>1 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>1)])[rep_of l a\<^sub>2 := (F a\<^sub>1 a\<^sub>2 \<approx> a)#(u ! rep_of l a\<^sub>2)], 
          lookup = update_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a), 
          pending = pe, proof_forest = pf, pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip, 
          time = k, timestamps = ti\<rparr>)
)"

text \<open>For the initialisation of the congruence closure algorithm.\<close>
abbreviation 
  "initial_cc_t n \<equiv> congruence_closure.extend 
(initial_cc n) \<lparr>time = 0, timestamps = replicate n 0\<rparr>"

lemma propagate_step_propagate_step_t_equivalence:
  "propagate_step l u t pe pf pfl ip a b eq = 
congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip a b eq k ti)" 
  unfolding congruence_closure.truncate_def congruence_closure.extend_def 
  by simp

thm propagate_step_propagate_step_t_equivalence[of l b u a t pe pf pfl eq ip]
lemma propagate_propagate_t_domain:
  shows "propagate_dom cc =
propagate_t_dom (congruence_closure.extend cc
\<lparr>time = k, timestamps = ti\<rparr>)"
proof
  show "propagate_dom cc 
\<Longrightarrow> propagate_t_dom (congruence_closure.extend cc \<lparr>time = k, timestamps = ti\<rparr>)"
  proof(induction cc arbitrary: k ti rule: propagate.pinduct)
    case (1 l u t pf pfl ip)
    then show ?case using propagate_t.domintros unfolding congruence_closure.extend_def 
        congruence_closure.select_convs 
      by (metis congruence_closure.select_convs(4) list.discI)
  next
    case (2 l u t eq pe pf pfl ip)
    then show ?case  
    proof(cases "rep_of l (left eq) = rep_of l (right eq)")
      case True
      then have "propagate_t_dom
     (congruence_closure.extend
       \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl, input = ip\<rparr>
       \<lparr>time = k, timestamps = ti\<rparr>)" 
        using "2.IH"(1) by blast
      then show ?thesis using propagate_t.domintros True unfolding congruence_closure.extend_def 
          congruence_closure.select_convs congruence_closure_t.select_convs 
        by (smt (verit) congruence_closure.select_convs(1) congruence_closure.select_convs(2) congruence_closure.select_convs(3) congruence_closure.select_convs(4) congruence_closure.select_convs(5) congruence_closure.select_convs(6) congruence_closure.select_convs(7) congruence_closure_t.select_convs(1) congruence_closure_t.select_convs(2) list_tail_coinc)
    next
      case False   
      then have "propagate_t_dom
     (congruence_closure.extend (propagate_step l u t pe pf pfl ip (left eq) (right eq) eq) 
\<lparr>time = k, timestamps = ti\<rparr>)" 
        using "2.IH"(2) by blast
      then show ?thesis using propagate_t.domintros False unfolding congruence_closure.extend_def 
          congruence_closure.select_convs congruence_closure_t.select_convs 
        by (smt (verit) "2.IH"(2) congruence_closure.select_convs(1) congruence_closure.select_convs(2) congruence_closure.select_convs(3) congruence_closure.select_convs(4) congruence_closure.select_convs(5) congruence_closure.select_convs(6) congruence_closure.select_convs(7) list_tail_coinc propagate_t.domintros)   
    qed
  qed
next
  obtain cc_l u t pe pf pfl ip where cc: "cc = 
\<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using congruence_closure.cases by blast
  assume "propagate_t_dom (congruence_closure.extend cc \<lparr>time = k, timestamps = ti\<rparr>) "
  then show "propagate_dom cc"
    using cc proof(induction "(congruence_closure.extend cc \<lparr>time = k, timestamps = ti\<rparr>)" 
      arbitrary: cc k ti cc_l u t pe pf pfl ip rule: propagate_t.pinduct)
    case 1
    then show ?case proof(cases pe)
      case Nil
      then show ?thesis using 1(4) propagate.domintros 
        by auto
    next
      case (Cons eq list)
      then show ?thesis proof(cases "rep_of cc_l (left eq) = rep_of cc_l (right eq)")
        case True
        have "propagate_dom
      \<lparr>cc_list = cc_l, use_list = u, lookup = t, pending = list, proof_forest = pf, pf_labels = pfl,
         input = ip\<rparr>" using 1(2) Cons True
          unfolding 1(4) congruence_closure.extend_def congruence_closure.select_convs 
            congruence_closure_t.select_convs by simp
        then show ?thesis 
          using 1(4) propagate.domintros True Cons by blast
      next
        case False
        have "propagate_dom
      (propagate_step cc_l u t list pf pfl ip (left eq) (right eq) eq)" 
          using 1(3)[of cc_l u t pe pf pfl ip k ti eq list "left eq" "right eq"] Cons False
          unfolding 1(4) congruence_closure.extend_def congruence_closure.select_convs 
            congruence_closure_t.select_convs 
          by (smt (verit) congruence_closure.surjective old.unit.exhaust)
        then show ?thesis 
          using 1(4) propagate.domintros False Cons by blast
      qed
    qed
  qed
qed

lemma propagate_propagate_t_equivalence:
  assumes "cc_invar cc"
    "nr_vars cc > 0"
  shows "propagate cc =
congruence_closure.truncate (propagate_t (congruence_closure.extend cc 
\<lparr>time = k, timestamps = ti\<rparr>))" 
proof-
  have "propagate_dom cc" using propagate_domain assms by auto
  then show ?thesis 
  proof(induction arbitrary: k ti rule: propagate.pinduct)
    case (1 l u t pf pfl ip)
    then have t_dom: "propagate_t_dom
        \<lparr>cc_list = l, use_list = u, lookup = t, pending = [], proof_forest = pf,
               pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>" 
      using propagate_propagate_t_domain[of " \<lparr>cc_list = l, use_list = u, lookup = t, pending = [], proof_forest = pf,
               pf_labels = pfl, input = ip\<rparr>"] unfolding congruence_closure.extend_def 
      by simp
    show ?case 
      unfolding propagate.psimps(1)[OF 1] propagate_t.psimps(1)[OF t_dom]
        Let_def congruence_closure.select_convs 
        congruence_closure.extend_def congruence_closure.truncate_def 
        congruence_closure_t.select_convs
      by force
  next
    case (2 l u t eq pe pf pfl ip)
    then have t_dom: "propagate_t_dom
      \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
            pf_labels = pfl, input = ip, time = k, timestamps = ti\<rparr>" 
      using propagate_propagate_t_domain[of "\<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
            pf_labels = pfl, input = ip\<rparr>"] unfolding congruence_closure.extend_def 
      by simp
    show ?case 
    proof(cases "rep_of l (left eq) = rep_of l (right eq)")
      case True
      have IH: "propagate
     \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf, pf_labels = pfl,
        input = ip\<rparr> =
    congruence_closure.truncate
     (propagate_t
       (congruence_closure.extend
         \<lparr>cc_list = l, use_list = u, lookup = t, pending = pe, proof_forest = pf,
            pf_labels = pfl, input = ip\<rparr>
         \<lparr>time = k, timestamps = ti\<rparr>))" using 2 True by blast
      then show ?thesis unfolding propagate.psimps(2)[OF 2(1)] propagate_t.psimps[OF t_dom]
          Let_def congruence_closure.select_convs 
          congruence_closure.extend_def congruence_closure.truncate_def 
          congruence_closure_t.select_convs 
        using True by force
    next
      case False
      then have IH: "propagate (propagate_step l u t pe pf pfl ip (left eq) (right eq) eq) =
    congruence_closure.truncate
     (propagate_t
       (congruence_closure.extend (propagate_step l u t pe pf pfl ip (left eq) (right eq) eq)
         \<lparr>time = k, timestamps = ti\<rparr>))" using 2 False by blast
      have *:"(propagate_t
       (congruence_closure.extend
         \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
            pf_labels = pfl, input = ip\<rparr>
         \<lparr>time = k, timestamps = ti\<rparr>)) = 
propagate_t (propagate_step_t l u t pe pf pfl ip (left eq) (right eq) eq k ti)
\<and> (propagate
         \<lparr>cc_list = l, use_list = u, lookup = t, pending = eq # pe, proof_forest = pf,
            pf_labels = pfl, input = ip\<rparr> = 
propagate (propagate_step l u t pe pf pfl ip (left eq) (right eq) eq))"
        unfolding propagate.psimps(2)[OF 2(1)] propagate_t.psimps[OF t_dom] 
          Let_def congruence_closure.extend_def congruence_closure.select_convs
        using False by simp
      have "(propagate_step l u t pe pf pfl ip (left eq) (right eq) eq) =
congruence_closure.truncate (propagate_step_t l u t pe pf pfl ip (left eq) (right eq) eq k ti)"
        using False IH
          propagate_step_propagate_step_t_equivalence 
        by fast
      then have "propagate (propagate_step l u t pe pf pfl ip (left eq) (right eq) eq) =
    congruence_closure.truncate
     (propagate_t (propagate_step_t l u t pe pf pfl ip (left eq) (right eq) eq k ti))"
        using "2.IH"(2) False by blast
      then show ?thesis using False IH *
        by argo
    qed
  qed
qed

lemma merge_merge_t_equivalence:
  assumes "cc_invar cc"
    "nr_vars cc > 0"
    "valid_vars eq (nr_vars cc)"
  shows "merge cc eq = 
congruence_closure.truncate (merge_t (congruence_closure.extend cc \<lparr>time = k, timestamps = ti\<rparr>) eq)" 
  using assms proof(induction cc eq rule: merge.induct)
  case (1 l u t pe pf pfl ip a b)
  then have "cc_invar \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b) # pe, proof_forest = pf,
        pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"
    "nr_vars \<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b) # pe, proof_forest = pf,
        pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr> > 0" using cc_invar_merge1 by auto
  then show ?case 
    unfolding merge_t.simps(1) merge.simps(1) Let_def congruence_closure.select_convs 
      congruence_closure.extend_def congruence_closure.truncate_def congruence_closure_t.select_convs 
    using propagate_propagate_t_equivalence[of "\<lparr>cc_list = l, use_list = u, lookup = t, pending = One (a \<approx> b) # pe, proof_forest = pf,
        pf_labels = pfl, input = insert (a \<approx> b) ip\<rparr>"] unfolding congruence_closure.extend_def congruence_closure.truncate_def 
    by auto
next
  case (2 l u t pe pf pfl ip a\<^sub>1 a\<^sub>2 a)
  then have " lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a) \<Longrightarrow> cc_invar \<lparr>cc_list = l, use_list = u, lookup = t,
             pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) # pe, proof_forest = pf,
             pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"
    "nr_vars \<lparr>cc_list = l, use_list = u, lookup = t,
             pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) # pe, proof_forest = pf,
             pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr> > 0" 
    using cc_invar_merge2 by auto
  then show ?case 
    apply (cases "(lookup_Some t l (F a\<^sub>1 a\<^sub>2 \<approx> a))")
    using propagate_propagate_t_equivalence[of "\<lparr>cc_list = l, use_list = u, lookup = t,
             pending = link_to_lookup t l (F a\<^sub>1 a\<^sub>2 \<approx> a) # pe, proof_forest = pf,
             pf_labels = pfl, input = insert (F a\<^sub>1 a\<^sub>2 \<approx> a) ip\<rparr>"]
    unfolding merge_t.simps(2) merge.simps(2) Let_def congruence_closure.select_convs If_def
      congruence_closure.extend_def congruence_closure.truncate_def congruence_closure_t.select_convs
    unfolding congruence_closure.extend_def congruence_closure.truncate_def
    by auto
qed

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



end
