theory BetaSound
  imports Consistency
begin

lemma consis_returns: assumes v_f: "is_fun f"
  shows "consis_list (map snd [(A, B)\<leftarrow>f . A \<sqsubseteq> C])"
  apply auto by (meson upper_bound_join v_f) 
  
(* This version follows Alessi et al. 2005 *)
lemma beta_sound_aux:
    "\<lbrakk> (v1::val) \<sqsubseteq> v2; v1 = VFun f1; v2 = VFun f2; is_val v2; (A1,B1) \<in> set f1 \<rbrakk>
    \<Longrightarrow> \<exists> B2s. \<Squnion> (map snd [(A2, B2)\<leftarrow>f2 . A2 \<sqsubseteq> A1]) = Some B2s \<and> B1 \<sqsubseteq> B2s" 
proof (induction arbitrary: f1 f2 A1 B1 rule: val_le.induct)
  case (le_refl v f1 f2 A1 B1)
  let ?L = "map snd [(A2, B2)\<leftarrow>f2 . A2 \<sqsubseteq> A1]"
  have a1_a1: "A1 \<sqsubseteq> A1" by blast
  have b1_L: "B1 \<in> set ?L" using le_refl a1_a1 
    by (metis (no_types, lifting) filter_set image_eqI member_filter old.prod.case set_map snd_conv val.inject(2))      
  then have ll: "0 < length ?L" by force
  have f_f2: "is_fun f2" using le_refl by auto
  have cl: "consis_list ?L" using f_f2 consis_returns by blast
  obtain Ls where ls: "\<Squnion>?L = Some Ls" using ll cl upper_bound_consis_list apply blast done
  have b1_ls: "B1 \<sqsubseteq> Ls" using b1_L using join_list_sub ls by blast  
  show ?case using ls b1_ls by blast
next
  case (le_trans v1 v2 v3 f1 f3 A1 B1)
    (* need is_val v2! *)
  then show ?case sorry
next
  case (le_bot f)
  then show ?case sorry
next
  case (le_fun_append_left f1 f2)
  then show ?case sorry
next
  case (le_fun_append_right f2 f1)
  then show ?case sorry
next
  case (le_fun_left_join f1 f3 f2)
  then show ?case sorry
next
  case (le_arrow v2 v1 v1' v2')
  then show ?case sorry
next
  case (le_distr v1 v2 v12 v)
  then show ?case sorry
qed


(* This version follows Alessi et al. 2005 *)
lemma beta_sound_aux2:
    "\<lbrakk> (v1::val) \<sqsubseteq> v2; v1 = VFun f1; v2 = VFun f2; (A1,B1) \<in> set f1;
       \<Squnion> (map snd [(A2, B2)\<leftarrow>f2 . A2 \<sqsubseteq> A1]) = Some B2s \<rbrakk> \<Longrightarrow> B1 \<sqsubseteq> B2s" 
proof (induction arbitrary: f1 f2 A1 B1 B2s rule: val_le.induct)
  case (le_refl v)
  let ?L = "map snd [(A,B)\<leftarrow>f1.  A \<sqsubseteq> A1]"
  have "B1 \<in> set ?L" using le_refl apply (subgoal_tac "A1 \<sqsubseteq> A1") prefer 2 apply blast
      apply force done
  then show "B1 \<sqsubseteq> B2s" using le_refl join_list_sub[of B1 ?L] by force 
next
  case (le_trans v1 v2 v3 f1 f3 A1 B1 B3s)
  obtain f2 where v2: "v2 = VFun f2" using le_trans(1) le_trans(5) 
    using le_fun_any_inv by blast
  let ?L3 = "\<lambda> A2. map snd [(A3,B3)\<leftarrow>f3. A3 \<sqsubseteq> A2]"
  have IH2: "\<And> A2 B2 B3. \<lbrakk> (A2, B2) \<in> set f2; \<Squnion>(?L3 A2) = Some B3 \<rbrakk> \<Longrightarrow>
    B2 \<sqsubseteq> B3" using le_trans.IH(2)[of f2 f3] v2 le_trans(6) by blast

  let ?L2 = "map snd [(A2,B2)\<leftarrow>f2. A2 \<sqsubseteq> A1]"
  obtain B2s where b2: "\<Squnion> ?L2 = Some B2s" sorry
  (* Need to require is_val to get self consistency *)
  from le_trans.IH(1)[of f1 f2] le_trans(5) v2 le_trans(7) le_trans(8) b2
  have d_b2: "B1 \<sqsubseteq> B2s" by blast
 
  have b3s: "\<Squnion> (?L3 A1) = Some B3s" using le_trans by blast
      
  have b2_b3: "B2s \<sqsubseteq> B3s"
  proof -
    have 1: "\<forall> B2. B2 \<in> set ?L2 \<longrightarrow> B2 \<sqsubseteq> B3s"
    proof clarify
      fix B2 assume b2_l2: "B2 \<in> set ?L2"
      obtain A2 where a2b2_f2: "(A2,B2) \<in> set f2" and a1_a2: "A2 \<sqsubseteq> A1" using b2_l2 by auto
      obtain B3s' where b3sp: "\<Squnion> (?L3 A2) = Some B3s'" sorry
      have b3sp_b3s: "B3s' \<sqsubseteq> B3s"
      proof -
        have all3s: "\<forall>B3. B3 \<in> set (?L3 A2) \<longrightarrow> B3 \<sqsubseteq> B3s"
        proof clarify
          fix B3 assume b3_l3: "B3 \<in> set (?L3 A2)"
          obtain A3 where a3b3_f3: "(A3,B3) \<in> set f3" and a2_a3: "A3 \<sqsubseteq> A2" using b3_l3 by auto
          have "A3 \<sqsubseteq> A1" using a1_a2 a2_a3 Values.le_trans by blast
          then have "B3 \<in> set (?L3 A1)" using a3b3_f3 by force
          then show "B3 \<sqsubseteq> B3s" using b3s join_list_sub by blast
        qed
        show ?thesis using join_list_glb[of "?L3 A2" B3s B3s'] b3sp all3s by blast
      qed
      have "B2 \<sqsubseteq> B3s'" using IH2[of A2 B2 B3s'] a2b2_f2 b3sp by blast
      then show "B2 \<sqsubseteq> B3s" using b3sp_b3s Values.le_trans by blast
    qed
    show ?thesis using 1 b2 join_list_glb by blast
  qed
  show ?case using d_b2 b2_b3 Values.le_trans[of B1 B2s B3s] by blast
next
  case (le_bot f)
  then show ?case by auto     
(*
next
  case (le_join_left v1 v2 v12 f1 f12)
  obtain f2 where v2: "v2 = VFun f2" and f12: "f12 = f1@f2"
    using le_join_left apply (cases v2) apply auto done
  let ?L12 = "map snd [(A2,B2)\<leftarrow>f12. A2 \<sqsubseteq> A1]"
  have "(A1,B1) \<in> set f12" using le_join_left f12 by auto
  then have "B1 \<in> set ?L12" by force 
  then show "B1 \<sqsubseteq> B2s" using join_list_sub le_join_left(5) by blast
next
  case (le_join_right v1 v2 v12 f2 f12)
  obtain f1 where v2: "v2 = VFun f2" and f12: "f12 = f1@f2"
    using le_join_right apply (cases v1) apply auto done
  let ?L12 = "map snd [(A2,B2)\<leftarrow>f12. A2 \<sqsubseteq> A1]"
  have "(A1,B1) \<in> set f12" using le_join_right f12 by auto
  then have "B1 \<in> set ?L12" by force       
  then show "B1 \<sqsubseteq> B2s" using join_list_sub le_join_right(5) by blast
next
  case (le_left_join v1 v3 v2 v12 f12 f3 A12 B12 B3s)
  obtain f1 where v1: "v1 = VFun f1" using le_left_join by (case_tac v1) auto 
  obtain f2 where v2: "v2 = VFun f2" using le_left_join by (case_tac v2) auto
  have v3: "v3 = VFun f3" using le_left_join.prems by blast
  have b3s: "\<Squnion> (map snd [(A3,B3)\<leftarrow>f3. A3 \<sqsubseteq> A12]) = Some B3s" 
    using le_left_join.prems(4) by auto   
  have "(A12, B12) \<in> set (f1@f2)" using v1 v2 le_left_join by force
  then show "B12 \<sqsubseteq> B3s" apply simp
  proof (erule disjE)
    assume ab12_f1: "(A12, B12) \<in> set f1"
    show ?thesis using le_left_join.IH(1)[of f1 f3 A12 B12 B3s] v1 v3 ab12_f1 b3s by blast
  next
    assume ab12_f2: "(A12, B12) \<in> set f2"
    show ?thesis using le_left_join.IH(2)[of f2 f3 A12 B12 B3s] v2 v3 ab12_f2 b3s by blast
  qed
*)
next
  case (le_arrow v2 v1 v1' v2')
  have f1: "f1 = [(v1, v1')]" using le_arrow by blast
  have f2: "f2 = [(v2, v2')]" using le_arrow by blast
  have a1b1_f1: "(A1, B1) \<in> set f1" using le_arrow by blast
  have a1: "A1 = v1" using f1 a1b1_f1 by auto 
  have b1: "B1 = v1'" using f1 a1b1_f1 by auto
  let ?L2 = "map snd [(A2,B2)\<leftarrow>f2 . A2 \<sqsubseteq> v1]" 
  have b2s: "\<Squnion> ?L2 = Some B2s" using le_arrow a1 by force
  have "v2' \<in> set ?L2" using le_arrow(1) f2 by auto
  then have "v2' \<sqsubseteq> B2s" using b2s join_list_sub[of v2' ?L2 B2s] by blast 
  then show "B1 \<sqsubseteq> B2s" using le_arrow(2) b1 le_trans by blast
next
  case (le_distr v1 v2 v12 v)
  have b2s_v12: "B2s = v12" using le_distr le_refl by auto
  have b1_v12: "B1 = v12" using le_distr by auto    
  show "B1 \<sqsubseteq> B2s" using b1_v12 b2s_v12 le_refl by simp
oops

lemma beta_sound_gen:
    "\<lbrakk> VFun f1 \<sqsubseteq> VFun f2;
       (A1,B1) \<in> set f1;
       \<Squnion> (map snd [(A2, B2)\<leftarrow>f2 . A2 \<sqsubseteq> A1]) = Some B2s \<rbrakk> \<Longrightarrow> B1 \<sqsubseteq> B2s"
(*    using beta_sound_aux2 *)
  oops

lemma beta_sound:
    "\<lbrakk> A1 \<mapsto> B1 \<sqsubseteq> VFun f2;
       \<Squnion> (map snd [(A2, B2)\<leftarrow>f2 . A2 \<sqsubseteq> A1]) = Some B2s \<rbrakk> \<Longrightarrow> B1 \<sqsubseteq> B2s"
  (*  using beta_sound_gen *)
  oops   

end