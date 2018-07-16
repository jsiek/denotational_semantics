theory Deterministic
  imports Consistency Denot
begin

lemma merge_inter: "A ~ B \<Longrightarrow> merge A B \<approx> A \<sqinter> B"
  apply (case_tac A)
    apply (case_tac B)
      apply force
     apply simp
  apply simp
  apply (case_tac B)
     apply simp
    apply simp
   apply simp
    apply simp
  done
  
lemma consistent_app: "\<lbrakk> f1 ~ f2; v1 ~ v2; v1' \<in> f1 \<bullet> v1; v2' \<in> f2 \<bullet> v2 \<rbrakk> \<Longrightarrow> v1' ~ v2'"
  apply simp
  sorry
  
lemma merge_app: assumes f1_v1: "v1' \<in> f1 \<bullet> v1" and f2_v2: "v2' \<in> f2 \<bullet> v2" and 
  f1_f2: "f1 ~ f2" and v1_v2: "v1 ~ v2" and v1p_v2p: "v1' ~ v2'"
  shows "merge v1' v2' \<in> merge f1 f2 \<bullet> merge v1 v2"
proof -
  have f1_v1p: "f1 <: v1 \<rightarrow> v1'" using f1_v1 by simp
  have f2_v2p: "f2 <: v2 \<rightarrow> v2'" using f2_v2 by simp  
  have "merge f1 f2 <: f1 \<sqinter> f2" using merge_inter f1_f2 ty_equiv_def by auto
  also have "f1 \<sqinter> f2 <: (v1\<rightarrow>v1') \<sqinter> (v2\<rightarrow>v2')" using f1_v1p f2_v2p by (rule sub_mon)
  also have "(v1 \<rightarrow> v1') \<sqinter> (v2 \<rightarrow> v2') <: (v1 \<sqinter> v2) \<rightarrow> (v1' \<sqinter> v2')" by (rule sub_dist_union_fun)
  also have "... <: (merge v1 v2) \<rightarrow> (merge v1' v2')" apply (rule sub_arrow)
      using merge_inter v1_v2 v1p_v2p ty_equiv_def apply auto done
  finally  have "merge f1 f2 <: (merge v1 v2) \<rightarrow> (merge v1' v2')" using sub_trans by auto
  then show ?thesis by simp
qed
    
theorem deterministic:
  "\<lbrakk> v1 \<in> E e \<rho>1; v2 \<in> E e \<rho>2; wf_env \<rho>1; wf_env \<rho>2; consis_env \<rho>1 \<rho>2 \<rbrakk>
   \<Longrightarrow> v1 ~ v2 \<and> merge v1 v2 \<in> \<lbrakk>e\<rbrakk>(\<rho>1 \<sqinter> \<rho>2)"
proof (induction e arbitrary: v1 v2 \<rho>1 \<rho>2)
  case (EVar x)
  have xr1: "x < length \<rho>1" using EVar(1) by (case_tac "x < length \<rho>1") auto
  have xr2: "x < length \<rho>2" using EVar(2) by (case_tac "x < length \<rho>2") auto
  have v1: "v1 = \<rho>1!x" using xr1 EVar(1) by auto
  have v2: "v2 = \<rho>2!x" using xr2 EVar(2) by auto
  have v1_v2: "v1 ~ v2" using EVar xr1 xr2 by auto 
  have v_v1: "wf_ty v1" using EVar(1) EVar(3) xr1 by auto
  have v_v2: "wf_ty v2" using EVar(2) EVar(4) xr2 by auto
  have r3x: "merge v1 v2 = (\<rho>1 \<sqinter> \<rho>2)!x" 
    using v1 v2 consis_env_inter[of \<rho>1 \<rho>2 x] EVar(5) xr1 by simp
  have xr3: "x < length (\<rho>1 \<sqinter> \<rho>2)" using inter_env_length xr1 EVar(5) by simp
  have v12_e: "merge v1 v2 \<in> \<lbrakk>EVar x\<rbrakk>(\<rho>1 \<sqinter> \<rho>2)" using r3x xr3 by simp
  show ?case using v1_v2 v12_e by simp
next
  case (ENat n)
  have v1: "v1 = TNat n" using ENat(1) by simp
  have v2: "v2 = TNat n" using ENat(2) by simp
  have m: "merge v1 v2 = TNat n" using v1 v2 by simp
  show ?case using m v1 v2 by simp
next
  case (ELam e)
  then show ?case sorry
next
  case (EApp e1 e2 v1' v2')
  obtain f1 v1 where f1_e1: "f1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v1_e2: "v1 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" and v1p_f1_v1: "v1' \<in> f1 \<bullet> v1"
    using EApp(3) by auto
  obtain f2 v2 where f2_e1: "f2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v2_e2: "v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and v2p_f2_v2: "v2' \<in> f2 \<bullet> v2"
    using EApp(4) by auto
  have f1_f2: "f1 ~ f2" using EApp.IH(1) f1_e1 f2_e1 EApp(5) EApp(6) EApp(7) by blast
  have m_f1f2: "merge f1 f2 \<in> \<lbrakk>e1\<rbrakk>(\<rho>1\<sqinter>\<rho>2)" using EApp.IH(1) f1_e1 f2_e1 EApp(5) EApp(6) EApp(7) by blast
  have v1_v2: "v1 ~ v2" using EApp.IH(2) v1_e2 v2_e2 EApp(5) EApp(6) EApp(7) by blast
  have m_v12: "merge v1 v2 \<in> \<lbrakk>e2\<rbrakk>(\<rho>1\<sqinter>\<rho>2)" using EApp.IH(2) v1_e2 v2_e2 EApp(5) EApp(6) EApp(7) by blast
  have v1p_v2p: "v1' ~ v2'" using f1_f2 v1_v2 v1p_f1_v1 v2p_f2_v2 consistent_app by blast
  have m_v12p_f12_v12: "merge v1' v2' \<in> (merge f1 f2) \<bullet> (merge v1 v2)"
    using v1p_f1_v1 v2p_f2_v2 f1_f2 v1_v2 v1p_v2p merge_app by blast
  show ?case using v1p_v2p m_v12p_f12_v12 m_f1f2 m_v12 by auto
next
  case (EPrim f e1 e2)
  then show ?case apply simp apply clarify apply simp apply (rule conjI) 
      sorry
      
next
  case (EIf e1 e2 e3)
  then show ?case sorry
qed
  
end
