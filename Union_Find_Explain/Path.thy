section \<open>Path\<close>
theory Path
  imports Explain 
begin 

text \<open>A path is defined from a node to a descendant, 
      the graph is represented by an array containing the parents of each node,
      as used in the union find algorithm.\<close>

inductive path :: "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  single: "n < length l \<Longrightarrow> path l n [n] n" |
  step: "r < length l \<Longrightarrow> l ! u = r \<Longrightarrow> l ! u \<noteq> u \<Longrightarrow>  path l u p v \<Longrightarrow> path l r (r # p) v"

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

lemma path_last: "path l u p v \<Longrightarrow> last p = v"
proof(induction rule: path.induct)
  case (step r l u p v)
  then show ?case 
    by (metis last_ConsR list.distinct(1) path.cases)
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

lemma path_not_empty: "path l u p v \<Longrightarrow> p \<noteq> []"
  by(induction rule:path.induct,auto)

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

text \<open>The path between two nodes is unique.\<close>

lemma path_unique: "ufa_invar l \<Longrightarrow> path l u p1 v \<Longrightarrow> path l u p2 v \<Longrightarrow> p1 = p2"
proof-
  assume a1: "ufa_invar l" and a2: "path l u p1 v" and a3: "path l u p2 v"
  have a4: "v < length l"
    using a2 path_nodes_lt_length_l by auto
  show "p1 = p2"
    using a1 a4 a2 a3
  proof(induction arbitrary: p1 p2 rule: rep_of_induct)
    case (base i)
    from base(4,5,1,2,3) have "i = u" 
    proof(induction "length p1" arbitrary: p1 i)
      case 0
      then show ?case 
        by (simp add: path_not_empty)
    next
      case (Suc x)
      then show ?case 
      proof(cases x)
        case 0
        with Suc show ?thesis 
          by (metis length_0_conv length_Suc_conv list_tail_coinc path.cases path_not_empty)
      next
        case Suc':(Suc nat)
        then have "path l u (butlast p1) (last (butlast p1))" 
          using Suc path_divide1 path_divide2
          by (metis butlast_snoc len_greater_imp_nonempty length_Suc_rev_conv lessI)
        then have *: "path l u (butlast p2) (last (butlast p2))" 
          using Suc path_divide1 path_divide2
          by (metis a1 append_butlast_last_id append_self_conv2 butlast.simps(1) path_no_cycle path_last path_length_1)
        with Suc have **: "l ! (p2 ! (length p2 - 1)) = (p2 ! (length p2 - 1 - 1))" 
          by (metis diff_less length_butlast length_greater_0_conv path_properties zero_less_one)
        with Suc have "l ! i = last (butlast p2)" 
          by (metis (mono_tags, lifting) Suc.prems(2) * diff_less last_conv_nth length_butlast length_greater_0_conv nth_butlast path_last path_not_empty zero_less_one)
        with Suc.prems have "i = last (butlast p2)" 
          by auto
        then have "p2 ! (length p2 - 1) = p2 ! (length p2 - 1 - 1)"
          by (metis Suc.prems(2) Suc.prems(5) ** last_conv_nth length_upt list.size(3) not_one_less_zero path_last upt_rec)
        with path_properties have "False" 
          by (metis * base.prems(2) diff_less length_butlast length_greater_0_conv zero_less_one)
        then show ?thesis by simp
      qed
    qed
    then show ?case 
      using a1 base path_no_cycle by blast
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
      then have last_p2:"l ! i = last (butlast p2)" 
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
      show ?thesis 
      proof-
        from length_p have "u = i" 
          by (metis list_decomp_1 path_length_1 step.prems(1) step.prems(2))
        then have "p1 = [i]"
          using a1 path_no_cycle step.prems path_nodes_lt_length_l by auto
        then have "p2 = [i]" 
          using \<open>u = i\<close> a1 path_no_cycle step.prems path_nodes_lt_length_l by blast
        with \<open>p1 = [i]\<close> show ?thesis 
          by auto
      qed
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

lemma path_no_root:"path l y p x \<Longrightarrow> x \<noteq> y \<Longrightarrow> l ! x \<noteq> x"
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

end