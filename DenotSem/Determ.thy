theory Determ
  imports Denot ValuesProps
begin

theorem deterministic:
  "\<lbrakk> v \<in> \<lbrakk>e\<rbrakk>\<rho>; v' \<in> \<lbrakk>e\<rbrakk>\<rho>'; val_env \<rho>; val_env \<rho>' \<rbrakk> \<Longrightarrow> v \<squnion> v' \<in> \<lbrakk>e\<rbrakk>(\<rho> \<squnion> \<rho>')"
proof (induction e arbitrary: v v' \<rho> \<rho>')
  case (EVar x)
  then show ?case apply simp apply (case_tac "x < length \<rho>")
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
