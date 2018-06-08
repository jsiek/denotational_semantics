theory Deterministic
  imports Values Denot Subsumption
begin

lemma lookup_consis[intro]: "\<lbrakk> consis_env \<rho> \<rho>'; x < length \<rho> \<rbrakk>
  \<Longrightarrow> (\<rho>!x) ~ (\<rho>'!x)"
  apply (induction arbitrary: x rule: consis_env.induct)
   apply force
  apply (case_tac x) apply force apply auto
  done
    
theorem deterministic:
  "\<lbrakk> v1 \<in> E e \<rho>1; v2 \<in> E e \<rho>2; val_env \<rho>1; val_env \<rho>2; consis_env \<rho>1 \<rho>2 \<rbrakk>
   \<Longrightarrow> v1 ~ v2 \<and> (\<exists> v12 \<rho>3. v1 \<squnion> v2 = Some v12 \<and> \<rho>1 \<squnion> \<rho>2 = Some \<rho>3 \<and> v12 \<in> \<lbrakk>e\<rbrakk>\<rho>3)"
proof (induction e arbitrary: v1 v2 \<rho>1 \<rho>2)
  case (EVar x)
  have "v1 ~ v2" using EVar(1) EVar(2) EVar(5) lookup_consis apply auto
      apply (case_tac "x < length \<rho>1") apply auto
      apply (case_tac "x < length \<rho>2") apply auto
    sorry
  then show ?case sorry
next
  case (ENat x)
  then show ?case sorry
next
  case (ELam e)
  then show ?case sorry
next
  case (EApp e1 e2)
  then show ?case sorry
next
  case (EPrim x1a e1 e2)
  then show ?case sorry
next
  case (EIf e1 e2 e3)
  then show ?case sorry
qed
  
end
