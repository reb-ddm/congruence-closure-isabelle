section \<open>Correctness proofs for Explain\<close>
theory Explain_Proofs2
  imports Explain_Proofs
begin 


paragraph \<open>Invariant: the edges near the root are newer.\<close>

lemma edges_near_root_newer:
  assumes invar: "ufe_invar ufe"
    and lt_length: "i < length (uf_list ufe)"
  assumes no_root: "(uf_list ufe) ! i \<noteq> (uf_list ufe) ! ((uf_list ufe) ! i)"
  shows "(au ufe) ! i < (au ufe) ! ((uf_list ufe) ! i)"
  using assms proof(induction rule: apply_unions_induct)
  case initial
  then show ?case by simp
next
  case (union pufe x y)
  have i: "i < length (uf_list pufe)" 
    using ufe_union_length_uf_list union.prems(1) by auto
  then show ?case 
  proof(cases "uf_list pufe ! i = uf_list pufe ! (uf_list pufe ! i)")
    case True
      \<comment> \<open>(l ! i) was a root.\<close>
    with union ufe_invar_imp_ufa_invar have inv: "ufa_invar (uf_list pufe)" 
      by blast
    obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>" 
      using ufe_data_structure.cases by blast
    then have rep_neq: "rep_of l1 x \<noteq> rep_of l1 y" 
      using True union.prems(2) by force
    with pufe union have i_no_root: "l1 ! i \<noteq> i "
      by (metis i inv nth_list_update_eq nth_list_update_neq rep_of_root ufe_data_structure.select_convs(1) ufe_union2_uf_list)
    from rep_neq have *: "au (ufe_union \<lparr>uf_list = l1, unions = u1, au = a1\<rparr> x y) = a1[rep_of l1 x := Some (length u1)]"
      by simp
        \<comment> \<open>(l ! i) is not a root any more.\<close>
    from i_no_root rep_of_root have **: "rep_of l1 x = l1 ! i" 
      by (metis True inv nth_list_update_neq pufe rep_neq ufe_data_structure.select_convs(1) ufe_union2_uf_list union.hyps(2) union.hyps(3) union.prems(2))
    from inv union have length_l1: "l1 ! i < length l1" 
      by (metis i pufe ufa_invarD(2) ufe_data_structure.select_convs(1))
    from union length_au pufe have length_a1: "length l1 = length a1" 
      by (metis ufe_data_structure.select_convs(1,3))
    with pufe * have au_parent: "au (ufe_union pufe x y) ! (l1 ! i) = Some (length u1)"  
      by (metis length_l1 ** nth_list_update_eq)
    with au_Some_valid union * have "au (ufe_union pufe x y) ! i < Some (length u1)" 
      by (metis length_l1 length_a1 ** au_valid i i_no_root nth_list_update pufe ufe_data_structure.select_convs(1-3))
    then show ?thesis
      by (metis au_parent ** i_no_root nth_list_update_neq pufe rep_neq ufe_data_structure.select_convs(1) ufe_union2_uf_list)
  next
    case False
      \<comment> \<open>(l ! i) was not a root.\<close>
    with au_none_iff_root obtain k where k: "au pufe ! ((uf_list pufe) ! i) = Some k" 
      using i union.hyps(1) by (metis less_option_None not_None_eq union.IH)
    have "uf_list (ufe_union pufe x y) ! i \<noteq> uf_list (ufe_union pufe x y) ! (uf_list (ufe_union pufe x y) ! i)"
      using union.prems(2) by blast
    with au_ufe_union_Some_invar False
    have a: "au (ufe_union pufe x y) ! (uf_list pufe ! i) = au pufe ! (uf_list pufe ! i)" 
      using k union by presburger
    from union have b: "au pufe ! i < au pufe ! (uf_list pufe ! i)" 
      using False i by linarith
    then have "au pufe ! (uf_list pufe ! i) \<noteq> None" 
      by (metis less_option_None)
    from False have *: "uf_list pufe ! i \<noteq> i" 
      by auto
    obtain l1 u1 a1 where pufe: "pufe = \<lparr>uf_list = l1, unions = u1, au = a1\<rparr>"
      using ufe_data_structure.cases by blast
    with * obtain k2 where k2: "a1 ! i = Some k2" 
      using i union.hyps(1) au_none_iff_root by force
    have "uf_list (ufe_union pufe x y) ! i \<noteq> i" 
      using union.prems(2) by auto
    then have c: "au (ufe_union pufe x y) ! i = au pufe ! i" 
      using au_ufe_union_Some_invar pufe k2 union 
      by (metis ufe_data_structure.select_convs(3))
    have "au (ufe_union pufe x y) ! (uf_list (ufe_union pufe x y) ! i)
            = au pufe ! (uf_list pufe ! i)" using no_root_ufe_union_invar
      using * a pufe union.hyps by auto
    with a b c show ?thesis by auto
  qed
qed



end