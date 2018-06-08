theory Subsumption
 imports Values Denot
begin

lemma is_val_sem: assumes v_e: "v \<in> \<lbrakk>e\<rbrakk>\<rho>" and v_r: "val_env \<rho>" shows "is_val v" 
  using v_e v_r 
proof (induction e arbitrary: v \<rho>)
  case (EVar x)
  then show ?case by (case_tac "x < length \<rho>") (auto simp: val_env_def)
qed auto
  


end