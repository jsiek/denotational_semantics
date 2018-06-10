theory Deterministic
  imports Values Denot Subsumption
begin

theorem deterministic:
  "\<lbrakk> v1 \<in> E e \<rho>1; v2 \<in> E e \<rho>2; val_env \<rho>1; val_env \<rho>2; consis_env \<rho>1 \<rho>2 \<rbrakk>
   \<Longrightarrow> v1 ~ v2 \<and> (\<exists> v12 \<rho>3. v1 \<squnion> v2 = Some v12 \<and> is_val v12 \<and> \<rho>1 \<squnion> \<rho>2 = Some \<rho>3 \<and> val_env \<rho>3 \<and> v12 \<in> \<lbrakk>e\<rbrakk>\<rho>3)"
proof (induction e arbitrary: v1 v2 \<rho>1 \<rho>2)
  case (EVar x)
  have xr1: "x < length \<rho>1" using EVar(1) by (case_tac "x < length \<rho>1") auto
  have xr2: "x < length \<rho>2" using EVar(2) by (case_tac "x < length \<rho>2") auto
  have v1_r1x: "v1 \<sqsubseteq> \<rho>1!x" using EVar(1) xr1 by auto
  have v2_r2x: "v2 \<sqsubseteq> \<rho>2!x" using EVar(2) EVar(5) xr2 by auto
  have v1_v2: "v1 ~ v2" using EVar lookup_consis apply auto
    apply (case_tac "x < length \<rho>1") apply auto apply (case_tac "x < length \<rho>2") apply auto
    apply (subgoal_tac "\<rho>1!x ~ \<rho>2!x") prefer 2 apply fastforce using consis_le by auto
  have v_v1: "is_val v1" using EVar.prems(1) EVar.prems(3) is_val_sem by blast
  have v_v2: "is_val v2" using EVar.prems(2) EVar.prems(4) is_val_sem by blast
  obtain v12 where v12: "v1 \<squnion> v2 = Some v12" and v_v12: "is_val v12"
    using v1_v2 v_v1 v_v2 consis_join_val by blast
  obtain \<rho>3 where r123: "\<rho>1 \<squnion> \<rho>2 = Some \<rho>3" and v_r3: "val_env \<rho>3" 
    using EVar consis_env_join by blast
  have r3x: "\<rho>1!x \<squnion> \<rho>2!x = Some (\<rho>3!x)" using r123 xr1 join_env_nth consis_env_length 
    using EVar.prems(5) by blast
  have v12_r3: "v12 \<sqsubseteq> \<rho>3!x" using v1_r1x r123 r3x using mon v12 v2_r2x by blast
  have xr3: "x < length \<rho>3" using join_env_length xr1 r123 consis_env_length EVar(5) by simp
  have v12_e: "v12 \<in> \<lbrakk>EVar x\<rbrakk>\<rho>3" using v12_r3 xr3 v_v12 by simp
  show ?case using v1_v2 v12 v_v12 r123 v12_e v_r3 by blast
next
  case (ENat x)
  obtain \<rho>3 where r123: "\<rho>1 \<squnion> \<rho>2 = Some \<rho>3" and v_r3: "val_env \<rho>3" 
    using ENat consis_env_join by blast
  show ?case using ENat r123 v_r3 by auto 
next
  case (ELam e)
  then show ?case sorry
next
  case (EApp e1 e2)
  obtain f1 v21 where v_v1: "is_val v1" and f1_e1: "VFun f1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and
    v21_e2: "v21 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" and v21v1_f1: "[(v21, v1)] \<sqsubseteq> f1" using EApp.prems(1) by auto
  obtain f2 v22 where v_v2: "is_val v2" and f2_e1: "VFun f2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and
    v22_e2: "v22 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and v22v2_f2: "[(v22, v2)] \<sqsubseteq> f2" using EApp.prems(2) by auto
  have f1_f2: "VFun f1 ~ VFun f2"
    using EApp.IH(1) EApp.prems(3) EApp.prems(4) EApp.prems(5) f1_e1 f2_e1 by blast
  have cf12: "VFun f1 ~ VFun f2" using EApp.IH(1)[of "VFun f1" \<rho>1 "VFun f2"] f1_f2 by blast
  obtain vf12 \<rho>3 where
    f12_vf12: "VFun f1 \<squnion> VFun f2 = Some vf12" and 
    v_vf12: "is_val vf12" and r12_r3: "\<rho>1 \<squnion> \<rho>2 = Some \<rho>3" and v_r3: "val_env \<rho>3" and
    vf12_e1: "vf12 \<in> \<lbrakk>e1\<rbrakk>\<rho>3" using EApp.IH(1)[of "VFun f1" \<rho>1 "VFun f2" \<rho>2] EApp.prems(3) 
      EApp.prems(4) EApp.prems(5) f1_e1 f2_e1 by blast 
  obtain v12 \<rho>3' where v21_v22: "v21 ~ v22" and
    v21_v22_v12: "v21 \<squnion> v22 = Some v12" and v_v12: "is_val v12" and
    r12_r3p: "\<rho>1 \<squnion> \<rho>2 = Some \<rho>3'" and v_r3p: "val_env \<rho>3'" and v12_e2: "v12 \<in> \<lbrakk>e2\<rbrakk>\<rho>3"
    using EApp.IH(2) v21_e2 v22_e2 EApp.prems(3) EApp.prems(4) EApp.prems(5)
    by (metis  option.inject r12_r3)
  obtain v21' v1' where v21p_f1: "(v21',v1') \<in> set f1" and 
    v21p_v21: "v21' \<sqsubseteq> v21" and v1_v1p: "v1 \<sqsubseteq> v1'"
    sorry
    (*using v21v1_f1
    by (meson le_fun_sub_pair list.set_intros(1))
      *)
  obtain v22' v2' where v22p_f2: "(v22',v2') \<in> set f2" and 
    v22p_v22: "v22' \<sqsubseteq> v22" and v2_v2p: "v2 \<sqsubseteq> v2'"
    sorry
    (*using v22v2_f2
    by (meson le_fun_sub_pair list.set_intros(1))*)
  from f1_f2 v21p_f1 v22p_f2 have 1: "(v21' ~ v22' \<and> v1' ~ v2') \<or> \<not> v21' ~ v22'" 
    using consis_inconsis_sym by blast
  have c_v1v2: "v1 ~ v2"
    using 1 consis_le_inconsis_le v1_v1p v21_v22 v21p_v21 v22p_v22 v2_v2p by blast
  obtain v3 where v1_v2_v3: "v1 \<squnion> v2 = Some v3" and v_v3: "is_val v3" 
    using c_v1v2 consis_join_val v_v1 v_v2 by auto
  have "[(v12, v3)] \<sqsubseteq> f1 @ f2" 
  proof -
    have 1: "[(v21',v1'),(v22',v2')] \<sqsubseteq> f1@f2" 
      apply (rule le_fun_subset) apply (rule subsetI) using v21p_f1 v22p_f2 apply force done
    have v21p_v22p: "v21' ~ v22'" using v21_v22 v21p_v21 v22p_v22 consis_le by blast
    obtain w2 where w2: "v21' \<squnion> v22' = Some w2" and v_w2: "is_val w2" 
      using v21p_v22p consis_join_val[of v21' v22'] EApp.prems(3) EApp.prems(4)
        f1_e1 f2_e1 is_val_sem v21p_f1 v22p_f2 by blast
    have 2: "[(v12,v3)] \<sqsubseteq> [(v21',v1'),(v22',v2')]"
    proof -
      have a: "[(v12,v3)] \<sqsubseteq> [(v12,v1),(v12,v2)]"
        using v1_v2_v3 by (rule le_distr)
      have b: "[(v12,v1),(v12,v2)] \<sqsubseteq> [(v21',v1'),(v22',v2')]"
        apply (rule le_cons_left) prefer 3 apply force
         apply (rule le_cons_right1) apply (rule le_arrow)
        using Values.le_trans le_join_left v21_v22_v12 v21p_v21 apply blast
        using v1_v1p apply blast
         apply blast
        apply (rule le_cons_right2)
        apply (rule le_arrow)
        using le_trans le_join_right v21_v22_v12 v22p_v22 apply blast
        using v2_v2p apply blast
        done
      show ?thesis using a b le_fun_trans by meson
    qed
    show ?thesis using 2 1 le_fun_trans by meson
  qed
  then have 2: "v3 \<in> \<lbrakk>EApp e1 e2\<rbrakk>\<rho>3" using v_v3 vf12_e1 vf12_e1 f12_vf12 v12_e2 apply simp
    apply (rule_tac x="f1@f2" in exI) apply simp
    apply (rule_tac x=v12 in exI) apply simp done
  show ?case using "2" \<open>v1 \<squnion> v2 = Some v3\<close> c_v1v2 r12_r3 v_r3 v_v3 by blast
next
  case (EPrim f e1 e2)
  then show ?case sorry
next
  case (EIf e1 e2 e3)
  then show ?case sorry
qed
  
end
