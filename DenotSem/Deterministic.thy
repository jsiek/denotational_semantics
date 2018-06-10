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
    vf12_e2: "vf12 \<in> \<lbrakk>e1\<rbrakk>\<rho>3" using EApp.IH(1)[of "VFun f1" \<rho>1 "VFun f2" \<rho>2] EApp.prems(3) 
      EApp.prems(4) EApp.prems(5) f1_e1 f2_e1 by blast 
  
    
  show ?case sorry
next
  case (EPrim f e1 e2)
  then show ?case sorry
next
  case (EIf e1 e2 e3)
  then show ?case sorry
qed
  
end
