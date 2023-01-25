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

text \<open>Implementation of the proof forest\<close>

abbreviation propagate_step_t
  where 
"propagate_step_t l u t pe pf pfl ip a b eq k ti \<equiv>
 congruence_closure.extend (propagate_step l u t pe pf pfl ip a b eq)
    \<lparr>time = k + 1,
    timestamps = ti[rep_of l a := k]\<rparr>"

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


end