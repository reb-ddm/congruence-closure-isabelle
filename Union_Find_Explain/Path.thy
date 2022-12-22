section \<open>Path\<close>
theory Path
  imports Explain_Definition
begin 

text \<open>A path is defined from a node to a descendant, 
      the graph is represented by an array containing the parents of each node,
      as used in the union find algorithm.\<close>

inductive path :: "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  single: "n < length l \<Longrightarrow> path l n [n] n" |
  step: "r < length l \<Longrightarrow> l ! u = r \<Longrightarrow> l ! u \<noteq> u \<Longrightarrow>  path l u p v \<Longrightarrow> path l r (r # p) v"

lemma path_not_empty: "path l u p v \<Longrightarrow> p \<noteq> []"
  by(induction rule:path.induct,auto)

lemma path_concat1: "path l u p1 v \<Longrightarrow> path l v p2 w \<Longrightarrow> path l u (p1 @ tl p2) w"
proof(induction rule: path.induct)
  case (single n l)
  then show ?case 
    by (metis append_Cons append_eq_append_conv2 append_self_conv list.distinct(1) list.exhaust_sel list.sel(1) list.sel(3) path.simps)
qed(simp add: path.step)

lemma path_concat2: "path l u p1 v \<Longrightarrow> path l v p2 w \<Longrightarrow> path l u (butlast p1 @ p2) w"
proof(induction rule: path.induct)
  case (step r l u p v)
  then show ?case 
    using path.cases path.step by fastforce
qed simp

lemma path_snoc: 
  "path l u p (l ! v) \<Longrightarrow> v < length l \<Longrightarrow> l ! v < length l \<Longrightarrow> l ! v \<noteq> v \<Longrightarrow> path l u (p @ [v]) v"
proof-
  assume p: "path l u p (l!v)" and "v < length l" and a: "l ! v < length l" and b:"l ! v \<noteq> v"
  then have "path l v [v] v" 
    by (simp add: single)
  with a b have "path l (l!v) [l!v,v] v" 
    by (simp add: step)
  with p path_concat1 show "path l u (p@[v]) v" 
    by fastforce
qed

lemma path_divide1: 
  "path l u (p1 @ p2) v \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> path l u p1 (last p1) \<and> path l (last p1) (last p1 # p2) v"
proof(induction l u "p1 @ p2" v arbitrary: p1 p2 rule: path.induct)
  case (single n l)
  then show ?case 
    by (simp add: path.single)
next
  case (step r l u p v)
  show ?case 
  proof(cases "p2")
    case Nil
    then show ?thesis 
      by (metis append_self_conv last.simps path.step single step(1-6))
  next
    case (Cons a list)
    with step have "tl p1 \<noteq> [] \<Longrightarrow> path l u (tl p1) (last (tl p1)) \<and>
    path l (last (tl p1)) (last (tl p1) # p2) v"
      by (metis list.sel(3) tl_append2)
    with step path.step single show ?thesis 
      by (metis hd_Cons_tl hd_append2 last_ConsL last_tl list.sel(1) self_append_conv2 tl_append2)
  qed
qed

lemma path_divide2: "path l u (p1 @ p2) v \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> path l u (p1 @ [hd p2]) (hd p2) \<and> path l (hd p2) p2 v"
proof(induction l u "p1 @ p2" v arbitrary: p1 p2 rule: path.induct)
  case (single n l)
  then show ?case 
    by (simp add: path.single)
next
  case (step r l u p v)
  show ?case 
  proof(cases "p1")
    case Nil
    then show ?thesis 
      by (metis append_self_conv2 list.sel(1) path.step single step(1,2,3,4,6))
  next
    case (Cons a list)
    then show ?thesis 
      using path.step step by auto
  qed
qed

lemma path_hd: "path l u p v \<Longrightarrow> hd p = u"
  by(induction rule: path.induct, auto)
lemma hd_path: "path l k p v \<Longrightarrow> hd p = u \<Longrightarrow> u = k"
  by(induction rule: path.induct, auto)

lemma path_last: "path l u p v \<Longrightarrow> last p = v"
proof(induction rule: path.induct)
  case (step r l u p v)
  then show ?case 
    by (metis last_ConsR list.distinct(1) path.cases)
qed auto
lemma last_path: "path l k p v \<Longrightarrow> last p = u \<Longrightarrow> u = v"
proof(induction rule: path.induct)
  case (step r l u p v)
  then show ?case 
    by (simp add: path_not_empty)
qed auto

lemma path_penultimate: "path l u p v \<Longrightarrow> length p > 1 \<Longrightarrow> last (butlast p) = l ! v"
proof(induction rule: path.induct)
  case (single n l)
  have "False" 
    using single.prems by auto
  then show ?case by simp
next
  case (step r l u p v)
  then show ?case 
  proof(cases "length p = 1")
    case True
    with step show ?thesis  
      by (metis One_nat_def Suc_to_right butlast.simps(2) last_ConsL length_butlast less_numeral_extra(1) less_numeral_extra(3) list_decomp_1 list_tail_coinc path.cases path_last)
  next
    case False
    with step show ?thesis 
      by (metis butlast.simps(2) last_ConsR length_Cons length_butlast less_SucE less_numeral_extra(3) list.size(3) zero_less_diff)
  qed
qed

corollary paths_iff: 
  "path l u p1 v \<and> path l v p2 w \<longleftrightarrow> hd p2 = v \<and> last p1 = v \<and> p2 \<noteq> [] \<and> p1 \<noteq> [] \<and> path l u (p1 @ tl p2) w"
proof
  assume assms:"path l u p1 v \<and> path l v p2 w"
  then have "last p1 = v" and "hd p2 = v"
    using path_last path_hd by auto
  with assms have "p2 \<noteq> []" and "p1 \<noteq> []" 
    by (metis list.discI path.cases)+
  then show "hd p2 = v \<and> last p1 = v \<and> p2 \<noteq> [] \<and> p1 \<noteq> [] \<and> path l u (p1 @ tl p2) w"
    using assms path_concat1 \<open>last p1 = v\<close> \<open>hd p2 = v\<close> by blast
next
  assume assms: "hd p2 = v \<and> last p1 = v \<and> p2 \<noteq> [] \<and> p1 \<noteq> [] \<and> path l u (p1 @ tl p2) w"
  then show "path l u p1 v \<and> path l v p2 w" 
    by (metis path_divide1 list.collapse)
qed

inductive_cases path_single: "path l u [k] v"

lemma path_length_1: "path l u [k] v \<longleftrightarrow> u = k \<and> v = k \<and> length l > k"
proof   
  assume "path l u [k] v"
  with path_single path_not_empty show "u = k \<and> v = k \<and> length l > k" 
    by metis
next 
  assume "u = k \<and> v = k \<and> length l > k"
  then show "path l u [k] v"
    by (simp add: single)
qed

lemma path_nodes_lt_length_l: "path l u p v \<Longrightarrow> u < length l \<and> v < length l"
  by (induction rule: path.induct, auto)

lemma path_unique_if_length_eq:
  assumes "path l x p1 v"
    and "path l y p2 v"
    and "ufa_invar l"
    and "length p1 = length p2"
  shows "p1 = p2 \<and> x = y"
  using assms proof(induction arbitrary: p2 y rule: path.induct)
  case (single n l)
  obtain k where "path l y [k] n" and "p2 = [k]"
    using list_decomp_1 single.prems by fastforce
  then show ?case 
    by (simp add: path_length_1)
next
  case (step r l u p v)
  then have "tl p2 = p \<and> hd (tl p2) = u"
    by (metis len_greater_imp_nonempty length_tl list.sel(3) list_eq_iff_nth_eq path.cases path_hd)
  with step show ?case
    by (metis list.sel(3) path.cases path_hd path_not_empty)
qed

lemma path_properties: 
  assumes "path l x p y"
  shows "p \<noteq> [] \<and> (\<forall> i > 0 . i < length p \<longrightarrow> l ! (p ! i) = (p ! (i - 1))) \<and> hd p = x \<and> last p = y
         \<and> (\<forall> i < length p . p ! i < length l) \<and> (\<forall> i > 0 . i < length p \<longrightarrow> p ! i \<noteq> (p ! (i - 1)))"
  using assms proof(induction rule: path.induct)
  case (single n l)
  then show ?case by auto
next
  case (step r l u p v)
  then have *:"(\<forall>i>1. i < Suc (length p) \<longrightarrow> l ! (p ! (i - 1)) = (r # p) ! (i - 1))"
    by (metis One_nat_def Suc_diff_1 Suc_lessD Suc_less_eq  nth_Cons_pos)
  from step have "(\<forall> i < length p. p!i < length l)" by simp
  then have **:"(\<forall> i < length (r#p). (r#p)!i < length l)"
    by (simp add: nth_Cons' step.hyps(1))
  with step  have "\<forall>i>0. i < length (r # p) \<longrightarrow> (r # p) ! i \<noteq> (r # p) ! (i - 1)"
    by (metis (no_types, lifting) One_nat_def Suc_pred hd_conv_nth length_Cons nat_neq_iff not_less_eq nth_Cons')
  with step show ?case 
    by (metis * ** hd_conv_nth last_ConsR length_Cons list.discI list.sel(1) neq0_conv nth_Cons_pos zero_less_diff)
qed

corollary path_parent:
  assumes "path l x p y" "i < length p" "i > 0"
  shows "l ! (p ! i) = (p ! (i - 1))"
  using assms path_properties by presburger

lemma path_no_cycle: 
  assumes invar: "ufa_invar l"
    and n: "n < length l"
    and path: "path l n p n"
  shows "p = [n]" 
proof(rule ccontr)
  assume contr: "p \<noteq> [n]"
  have "p \<noteq> [] \<and> hd p = n \<and> last p = n"
    using assms(3) paths_iff by blast
  then have p_length: "length p > 1"
    by (metis contr last.simps less_one list_decomp_1 nat_neq_iff slice_complete slice_eq_bounds_empty)
  have "\<not> rep_of_dom (l, n)"
    using invar n path contr p_length
  proof(induction arbitrary: p rule: rep_of_induct)
    case (base i)
    from base(4) base(3) have "p = [i]" 
      using path_single 
      by(induction rule: path.induct,simp,blast)
    with base.prems(2) show ?case 
      by simp
  next
    case (step i)
    from step(5,7) have penultimate: "last (butlast p) = l ! i" 
      by (rule path_penultimate)
    have p:"(butlast p) @ [i] = p" 
      by (metis paths_iff snoc_eq_iff_butlast step.prems(1))
    then have "path l i ((butlast p) @ [i]) i" and "(butlast p) \<noteq> []" 
      using p step.prems(1,2) by auto
    then have "path l i (butlast p) (l ! i)"
      and "path l (l ! i) [l ! i, i] i"
      using path_divide1 penultimate 
      by metis+ 
    then have "path l (l ! i) ([l ! i, i]@ tl (butlast p)) (l ! i)"
      using path_concat1 by blast
    then have "\<not> rep_of_dom (l, l ! i)" 
      using step.IH by auto
    then show ?case 
      using rep_of_domain by metis
  qed
  with assms show "False" 
    using path_nodes_lt_length_l ufa_invarD(1) by auto
qed

lemma path_to_root_has_length_1: "ufa_invar l \<Longrightarrow> path l u p1 v \<Longrightarrow> l ! v = v \<Longrightarrow> p1 = [v]"
proof(induction "length p1" arbitrary: p1)
  case 0
  then show ?case 
    by (simp add: path_not_empty)
next
  case (Suc x)
  then show ?case 
  proof(cases x)
    case 0
    with path_length_1 Suc show ?thesis 
      by (metis length_0_conv length_Suc_conv)
  next
    case Suc':(Suc nat)
    then have "path l u (butlast p1) (last (butlast p1))" 
      using Suc path_divide1 path_divide2
      by (metis butlast_snoc len_greater_imp_nonempty length_Suc_rev_conv lessI)
    then have *: "path l u (butlast p1) (last (butlast p1))" 
      using Suc path_divide1 path_divide2
      by metis
    with Suc have **: "l ! (p1 ! (length p1 - 1)) = (p1 ! (length p1 - 1 - 1))" 
      by (metis diff_less length_butlast length_greater_0_conv path_properties zero_less_one)
    with Suc have "l ! v = last (butlast p1)" 
      by (metis (mono_tags, lifting) Suc.prems(2) * diff_less last_conv_nth length_butlast length_greater_0_conv nth_butlast path_last path_not_empty zero_less_one)
    with Suc.prems have "v = last (butlast p1)" 
      by auto
    with Suc have "p1 ! (length p1 - 1) = p1 ! (length p1 - 1 - 1)"
      by (metis ** last_conv_nth length_upt list.size(3) not_one_less_zero path_last upt_rec)
    with path_properties Suc have "False" 
      by (metis *  diff_less length_butlast length_greater_0_conv zero_less_one)
    then show ?thesis by simp
  qed
qed

text \<open>The path between two nodes is unique.\<close>

theorem path_unique: "ufa_invar l \<Longrightarrow> path l u p1 v \<Longrightarrow> path l u p2 v \<Longrightarrow> p1 = p2"
proof-
  assume a1: "ufa_invar l" and a2: "path l u p1 v" and a3: "path l u p2 v"
  have a4: "v < length l"
    using a2 path_nodes_lt_length_l by auto
  show "p1 = p2"
    using a1 a4 a2 a3
  proof(induction arbitrary: p1 p2 rule: rep_of_induct)
    case (base i)
    then have "p1 = [i]" "p2 = [i]" using path_to_root_has_length_1 
      by blast+
    then show ?case 
      by blast
  next
    case (step i)
    then show ?case 
    proof(cases "length p1 > 1 \<and> length p2 > 1")
      case True
      have **: "path l u (butlast p1) (last (butlast p1))" 
        using step path_divide1 path_divide2
        by (metis True append_butlast_last_id length_butlast less_numeral_extra(3) less_or_eq_imp_le list.size(3) not_one_le_zero zero_less_diff)
      then have *: "path l u (butlast p2) (last (butlast p2))" 
        using step path_divide1 path_divide2
        by (metis True append_butlast_last_id length_butlast less_numeral_extra(3) less_or_eq_imp_le list.size(3) not_one_le_zero zero_less_diff)
      then have "l ! (p2 ! (length p2 - 1)) = (p2 ! (length p2 - 1 - 1))" 
        by (metis One_nat_def Suc_lessD True diff_less path_properties step.prems(2) zero_less_diff zero_less_one)
      then have last_p2: "l ! i = last (butlast p2)" 
        by (metis (mono_tags, opaque_lifting) * butlast_update' last_list_update length_butlast list_update_id path_last path_not_empty step.prems(2))
      then have "l ! (p1 ! (length p1 - 1)) = (p1 ! (length p1 - 1 - 1))" 
        using True path_properties step.prems(1) by force
      then have "l ! (p1 ! (length p1 - 1)) = last (butlast p1)"  
        by (metis True last_conv_nth path_last path_not_empty path_penultimate step.prems(1))
      then have "l ! i = last (butlast p1)" 
        using True path_penultimate step.prems(1) by auto
      with step show ?thesis
        by (metis last_p2 * ** append_butlast_last_id path_properties)
    next
      case False
      with path_not_empty have length_p: "length p1 = 1 \<or> length p2 = 1" 
        by (metis length_0_conv less_one linorder_neqE_nat step.prems(1) step.prems(2))
      then have "i = u" 
        by (metis list_decomp_1 path_length_1 step.prems)
      then have "p1 = [i] \<and> p2 = [i]" 
        using a1 path_no_cycle step by blast
      then show ?thesis by simp
    qed
  qed
qed

lemma path_rep_eq: "path l v p u \<Longrightarrow> ufa_invar l \<Longrightarrow> rep_of l v = rep_of l u"
proof(induction rule: path.induct)
  case (single n l)
  then show ?case by auto
next
  case (step r l u p v)
  then have "rep_of l u = rep_of l r"
    using path_nodes_lt_length_l rep_of_idx by auto
  with step show ?case 
    by simp
qed

lemma path_to_rep_of: 
  assumes "ufa_invar l"
    and "x < length l"
  obtains p where "path l (rep_of l x) p x"
  using assms proof(induction arbitrary: thesis rule: rep_of_induct)
  case (base i)
  then have "rep_of l i = i"
    by (simp add: rep_of_refl)
  then show ?case 
    using base path_length_1 by blast
next
  case (step i)
  from step(4) obtain p where p: "path l (rep_of l (l ! i)) p (l ! i)"
    by blast
  have "path l (l ! i) [l ! i, i] i" 
    by (simp add: path.step single step ufa_invarD(2))
  then have "path l (rep_of l (l ! i)) (p @ [i]) i" 
    using p path_concat1 by force
  then show ?case 
    using rep_of_idx step by auto
qed

lemma path_root: "path l x p r \<Longrightarrow> l ! r = r \<Longrightarrow> x = r"
  by(induction rule: path.induct, auto) 

lemma path_no_root: "path l y p x \<Longrightarrow> x \<noteq> y \<Longrightarrow> l ! x \<noteq> x"
  using path_root by auto

lemma path_butlast: "path l y p v \<Longrightarrow> y \<noteq> v \<Longrightarrow> path l y (butlast p) (l ! v)"
proof-
  assume path:"path l y p v"
    and "y \<noteq> v"
  then have "v < length l" 
    by (simp add: path_nodes_lt_length_l)
  have "v \<noteq> l ! v" 
    using \<open>y \<noteq> v\<close> path path_root by auto
  have "length p > 1" 
    by (metis \<open>y \<noteq> v\<close> last.simps length_greater_0_conv less_one linorder_neq_iff list_decomp_1 nth_append_length path path.cases path_last path_not_empty)
  have penultimate: "last (butlast p) = l ! v" 
    using \<open>1 < length p\<close> path path_penultimate by blast
  then have "path l (l ! v) [l ! v, v] v" 
    by (metis (mono_tags, lifting) \<open>y \<noteq> v\<close> append_butlast_last_id hd_rev last.simps path path_divide1 path_hd path_last rev.simps)
  then show ?thesis 
    by (metis penultimate \<open>y \<noteq> v\<close> append_butlast_last_id empty_append_eq_id list.sel(1) path path_divide1 path_hd path_last path_not_empty)
qed

lemma path_not_first_no_root:
  assumes "path l x p y"
    and "i < length p"
    and "i > 0"
  shows "l ! (p ! i) \<noteq> p ! i"
  using assms proof(induction arbitrary: i rule: path.induct)
  case (single n l)
  then show ?case by auto
next
  case (step r l u p v)
  have "(r # p) ! i = p ! (i - 1)" 
    by (simp add: step.prems(2))
  then show ?case 
  proof(cases "i = 1")
    case True
    with step show ?thesis 
      by (metis \<open>(r # p) ! i = p ! (i - 1)\<close> cancel_comm_monoid_add_class.diff_cancel hd_conv_nth path_properties)
  next
    case False
    with step show ?thesis 
      by (metis One_nat_def Suc_diff_1 Suc_less_eq \<open>(r # p) ! i = p ! (i - 1)\<close> length_Cons not_gr_zero)
  qed
qed

lemma nodes_path_lt_length_l:
  assumes "path l x p y"
    and "i < length p"
  shows "p ! i < length l"
proof-
  have "path l x (take i p @ [p ! i]) (p ! i)"
    by (metis Cons_nth_drop_Suc append_take_drop_id assms(1) assms(2) hd_drop_conv_nth list.discI path_divide2)
  then show ?thesis 
    using path_nodes_lt_length_l by auto
qed

lemma nodes_path_rep_of:
  assumes "path l x p y"
    and "i < length p"
    and "ufa_invar l"
  shows "rep_of l (p ! i) = rep_of l x"
    and "rep_of l (p ! i) = rep_of l y"
proof-
  have "path l x (take i p @ [p ! i]) (p ! i)" "path l (p ! i) (drop i p) y"
    by (metis Cons_nth_drop_Suc append_take_drop_id assms(1) assms(2) hd_drop_conv_nth list.discI path_divide2)+
  with assms show "rep_of l (p ! i) = rep_of l x"
    and "rep_of l (p ! i) = rep_of l y"
    using path_rep_eq by metis+
qed

lemma path_root_rep_of_dom: "path l root p i \<Longrightarrow> l ! root = root \<Longrightarrow> rep_of_dom (l, i)"
proof(induction "length p" arbitrary: p i)
  case 0
  then have "length p > 0" 
    using path_not_empty by auto
  then show ?case 
    by (simp add: "0.hyps")
next
  case (Suc x)
  then show ?case proof(cases "x = 0")
    case True
    with Suc have "hd p = root" "last p = i"
      by (auto simp add: path_hd path_last)
    with True have "i = root" 
      by (metis Suc.hyps(2) last_replicate le_antisym length_0_conv length_greater_0_conv lessI remdups_adj_length remdups_adj_length_ge1 remdups_adj_singleton_iff)
    then show ?thesis 
      using Suc.prems(2) rep_of.domintros by auto
  next
    case False
    have "path l root (butlast p) (l ! i)" 
      by (metis False Suc.hyps(2) Suc.prems(1) Suc.prems(2) length_Suc_rev_conv list.size(3) list_e_eq_lel(2) path.cases path_butlast path_root) 
    have "x = length (butlast p)" 
      by (simp add: Suc.hyps(2) Suc_to_right)
    then have "rep_of_dom (l, l ! i)" 
      using Suc.hyps(1) Suc.prems(2) \<open>path l root (butlast p) (l ! i)\<close> by blast
    then show ?thesis 
      using rep_of.domintros by blast
  qed
qed

lemma path_fun_upd:
  assumes "path l x p y" "i \<notin> set (tl p)"
  shows "path (CONST list_update l i k) x p y"
  using assms proof(induction rule: path.induct)
  case (single n l)
  then show ?case 
    by (simp add: path.single)
next
  case (step r l u p v)
  then show ?case 
    by (metis (no_types, lifting) in_set_tlD length_list_update list.sel(3) list.set_intros(1) nth_list_update_neq path.cases path.step)
qed

text \<open>The paths of nodes with a different root are disjoint.\<close>

lemma path_rep_of_neq_not_in_path: 
  assumes "path l y\<^sub>2 p\<^sub>2 x\<^sub>2"
    "i\<^sub>2 < length p\<^sub>2"
    "rep_of l n \<noteq> rep_of l x\<^sub>2"
    "ufa_invar l"
  shows "n \<noteq> p\<^sub>2 ! i\<^sub>2"
proof
  assume n_in_path: "n = p\<^sub>2 ! i\<^sub>2"
  then have "rep_of l (p\<^sub>2 ! i\<^sub>2) = rep_of l x\<^sub>2" 
    using nodes_path_rep_of(2) assms by blast
  with n_in_path have "rep_of l x\<^sub>2 = rep_of l n" 
    by simp
  with assms show "False" 
    by argo
qed

lemma path_rep_of_neq_disjoint: 
  assumes "path l y\<^sub>1 p\<^sub>1 x\<^sub>1" "path l y\<^sub>2 p\<^sub>2 x\<^sub>2"
    "i\<^sub>1 < length p\<^sub>1" "i\<^sub>2 < length p\<^sub>2"
    "rep_of l x\<^sub>1 \<noteq> rep_of l x\<^sub>2"
    "ufa_invar l"
  shows "p\<^sub>1 ! i\<^sub>1 \<noteq> p\<^sub>2 ! i\<^sub>2"
  using assms proof(induction l y\<^sub>1 p\<^sub>1 x\<^sub>1 arbitrary: i\<^sub>1 rule: path.induct)
  case (single n l)
  then have "[n] ! i\<^sub>1 = n" 
    by force
  then show ?case 
    using path_rep_of_neq_not_in_path single.prems by auto
next
  case (step r l u p v)
  then show ?case 
  proof(cases "i\<^sub>1")
    case 0
    then have "(r # p) ! i\<^sub>1 = r" 
      by simp
    with step show ?thesis 
      by (metis path_nodes_lt_length_l path_rep_eq path_rep_of_neq_not_in_path rep_of_idx)
  next
    case (Suc nat)
    then have "(r # p) ! i\<^sub>1 = p ! (i\<^sub>1 - 1)" 
      by simp
    then show ?thesis 
      using Suc step by auto
  qed
qed

lemma path_remove_left: 
  assumes "path l i (i#pia) ia"
    "ufa_invar l"
  shows "i \<notin> set pia"
proof
  assume "i \<in> set pia"
  then obtain p\<^sub>1 p\<^sub>2 where "pia = p\<^sub>1 @ [i] @ p\<^sub>2" 
    by (metis Cons_eq_append_conv append_Nil in_set_conv_decomp_first)
  with assms have "path l i ([i] @ p\<^sub>1 @ [i]) i" 
    by (metis Cons_eq_appendI append_is_Nil_conv empty_append_eq_id list.sel(1) path_divide2 snoc_eq_iff_butlast)
  with path_unique assms show "False" 
    by (metis append_self_conv last_ConsL path_divide1 snoc_eq_iff_butlast)
qed

lemma path_remove_right: 
  assumes "path l ia pia i"
    "ufa_invar l"
  shows "i \<notin> set (butlast pia)"
proof
  have pia: "pia = (butlast pia) @ [i]" 
    by (metis assms(1) path_last path_not_empty snoc_eq_iff_butlast)
  assume "i \<in> set (butlast pia)"
  then obtain p\<^sub>1 p\<^sub>2 where "butlast pia = p\<^sub>1 @ [i] @ p\<^sub>2" 
    by (metis Cons_eq_append_conv append_Nil in_set_conv_decomp_first)
  with assms have "path l i ([i] @ p\<^sub>2 @ [i]) i" 
    using pia path_divide2 by fastforce
  with path_unique assms show "False" 
    by (metis append_self_conv last_ConsL path_divide1 snoc_eq_iff_butlast)
qed

lemma path_remove_child: 
  assumes "path l ia pia (l ! i)"
    "ufa_invar l" "i < length l" "l ! i \<noteq> i"
  shows "i \<notin> set pia"
proof-
  from assms have "path l (l ! i) [l ! i, i] i" 
    by (metis path.step single ufa_invarD(2))
  have pia: "path l ia (pia @ [i]) i" 
    by (simp add: assms path_snoc ufa_invarD(2))
  with path_remove_right show ?thesis 
    by (metis assms(2) butlast_snoc)
qed

lemma path_previous_node: 
  assumes "path l y p x" "i < length p - 1" "p ! (i + 1) = n"
  shows "p ! i = l ! n"
  using assms proof(induction arbitrary: i rule: path.induct)
  case (single n l)
  then show ?case by auto 
next
  case (step r l u p v)
  then show ?case proof(cases i)
    case 0
    have "p \<noteq> []" 
      using path_not_empty step.hyps(4) by blast
    with step 0 have "hd p = n" 
      by (simp add: hd_conv_nth)
    with step have "u = n" 
      using hd_path by blast
    with step show ?thesis 
      by (metis "0" nth_Cons_0)
  next
    case (Suc nat)
    with step show ?thesis by auto
  qed
qed

lemma path_hd_and_last:
  assumes "path l y p x" "length p > 1"
  shows "p = y # (tl (butlast p)) @ [x]"
proof-
  have "p = butlast p @ [x]" 
    by (metis append_butlast_last_id assms(1) path_last path_not_empty)
  have "length (butlast p) > 0" 
    using add.right_neutral assms(2) by auto
  then have "butlast p @ [x] = y # (tl (butlast p) @ [x])" 
    by (metis Cons_eq_appendI assms(1) assms(2) hd_Cons_tl hd_butlast hd_path length_greater_0_conv) 
  then show ?thesis 
    using \<open>p = butlast p @ [x]\<close> by auto
qed

lemma path_longer:
  assumes "ufa_invar l" "path l b p1 a" "path l c p2 a" "length p1 > length p2"
  shows "path l b (take (length p1 - length p2 + 1) p1) c"
    (is "path l b ?p3 c")
proof-
  let ?p4 = "(drop (length p1 - length p2 + 1) p1)"
  have "path l b (?p3 @ ?p4) a" 
    by (simp add: assms(2))
  moreover have "?p3 \<noteq> []" 
    by (metis Suc_eq_plus1_left Zero_not_Suc ab_semigroup_add_class.add.commute assms(4) len_greater_imp_nonempty take_eq_Nil)
  ultimately have path_split: "path l b ?p3 (last ?p3)"  "path l (last ?p3) (last ?p3 # ?p4) a"
    using path_divide1 by blast+
  have "length (last ?p3 # ?p4) = length p2" 
    by (metis (no_types, lifting) One_nat_def ab_semigroup_add_class.add.commute add_diff_cancel_right add_diff_inverse_nat assms(3) assms(4) length_drop length_greater_0_conv less_Suc_eq list.discI list.size(4) not_less_eq path.simps)
  then have "(last ?p3) = c" 
    using path_unique_if_length_eq assms path_split by blast
  then show ?thesis 
    using path_split(1) by blast
qed

lemma complement_of_subpath:
  assumes "ufa_invar l" "path l b p1 a" "path l c p2 a" "b \<notin> set p2"
  shows "path l b (take (length p1 - length p2 + 1) p1) c"
    (is "path l b ?p3 c")
proof-
  let ?p4 = "(drop (length p1 - length p2 + 1) p1)"
  have "length p1 > length p2" 
  proof(rule ccontr)
    assume p2_longer: "\<not> length p2 < length p1"
    then have "b \<in> set p2" proof(cases "length p2 = length p1")
      case True
      then have "b = c" 
        using assms(1) assms(2) assms(3) path_unique_if_length_eq by auto
      then show ?thesis 
        by (metis assms(3) in_set_member member_rec(1) path.cases)
    next
      case False
      then have "length p1 < length p2" 
        using p2_longer by linarith
      then obtain p5 where "path l c p5 b" 
        using path_longer assms by blast
      then have "path l c (p5 @ tl p1) a" 
        using assms(2) paths_iff by blast
      then show ?thesis 
        by (metis (no_types, lifting) \<open>path l c p5 b\<close> assms(1) assms(2) assms(3) in_set_conv_decomp path.simps path_concat2 path_unique)
    qed
    then show "False" using assms(4) 
      by blast
  qed
  then show ?thesis 
    using assms(1) assms(2) assms(3) path_longer by blast
qed

lemma path_take_two:
  assumes "ufa_invar l" "i < length p" "i \<noteq> 0" "path l a p b"
  shows "path l (l ! (p ! i)) [l ! (p ! i), (p ! i)] (p ! i)"
proof
  show "l ! (p ! i) < length l" using assms 
    by (simp add: nodes_path_lt_length_l ufa_invarD(2))
  show "l ! (p ! i) = l ! (p ! i)" ..
  show "l ! (p ! i) \<noteq> (p ! i)"
    by (metis assms(2) assms(3) assms(4) bot_nat_0.not_eq_extremum path_not_first_no_root)
  show "path l (p ! i) [p ! i] (p ! i)" 
    using assms nodes_path_lt_length_l single by blast
qed

lemma path_contains_no_root:
  assumes "x \<in> set (tl p)" "ufa_invar l"
    "path l a p b"
  shows "l ! x \<noteq> x"
proof-
  from assms obtain i where "i < length (tl p)" "tl p ! i = x" 
    by (meson in_set_conv_nth)
  with path_not_first_no_root assms show ?thesis 
    by (metis List.nth_tl Suc_mono gr0_conv_Suc in_set_tlD length_Suc_conv length_pos_if_in_set list.sel(3))
qed

end
