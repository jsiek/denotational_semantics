theory DenotAlt
  imports Denot Deterministic
begin

fun D :: "exp \<Rightarrow> ty list \<Rightarrow> ty set" where
  Enat: "D (ENat n) \<rho> = {TNat n}" |
  Evar: "D (EVar k) \<rho> = (if k < length \<rho> then {\<rho>!k} else {})" |
  Elam: "D (ELam e) \<rho> = { f. wf_ty f \<and> fun_pred f \<and> (\<forall> v v'. (v,v') \<in> entries f \<longrightarrow>
   (\<exists>v''. v'' \<in> D e (v#\<rho>) \<and> v'' <: v')) }" |
  Eapp: "D (EApp e1 e2) \<rho> = { v'. \<exists> f v. f \<in> D e1 \<rho> \<and> v \<in> D e2 \<rho> \<and> v' \<in> f \<bullet> v }" | 
  Eprim: "D (EPrim f e1 e2) \<rho> = { v. \<exists> v1 v2 n1 n2. v1 \<in> D e1 \<rho> 
          \<and> v2 \<in> D e2 \<rho> \<and> v1 <: TNat n1 \<and> v2 <: TNat n2 \<and> TNat (f n1 n2) <: v \<and> wf_ty v }" |
  Eif: "D (EIf e1 e2 e3) \<rho> = { v. \<exists> v1 n. v1 \<in> D e1 \<rho> \<and> v1 <: TNat n
         \<and> (n = 0 \<longrightarrow> v \<in> D e3 \<rho>) \<and> (n \<noteq> 0 \<longrightarrow> v \<in> D e2 \<rho>) }"

lemma f_lam: "fun_pred f \<Longrightarrow> F f e \<rho> = (\<forall> v v'. (v,v') \<in> entries f \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk> (v#\<rho>))"
  by (induction f) auto

lemma f_fun_pred: "F f e \<rho> \<Longrightarrow> fun_pred f"
  by (induction f) auto

lemma wf_entries: "\<lbrakk> wf_ty A; (v,v') \<in> entries A \<rbrakk> \<Longrightarrow> wf_ty v \<and> wf_ty v'"
  apply (induction A arbitrary: v v') apply force apply force apply force done

lemma extend_wf_env: "\<lbrakk> wf_env \<rho>; wf_ty v \<rbrakk> \<Longrightarrow> wf_env (v#\<rho>)"
  by (simp add: nth_Cons')

lemma wf_d: "\<lbrakk> wf_env \<rho>; A \<in> D e \<rho> \<rbrakk> \<Longrightarrow> wf_ty A"
  apply (induction e arbitrary: \<rho> A)
       apply simp apply (case_tac "x < length \<rho>") apply force apply force
      apply force
     apply force
  using D.simps(4) apply blast
   apply (smt D.simps(5) mem_Collect_eq)
  by (smt D.simps(6) mem_Collect_eq)
    
theorem d_e: "wf_env \<rho> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<rho> = {B. \<exists>A. A \<in> D e \<rho> \<and> A <: B \<and> wf_ty B }"  
  apply (induction e arbitrary: \<rho>)
       apply force
      apply force
    -- "lambda" 
     apply simp apply (rule Collect_cong) apply (rule iffI) 
      apply clarify
      apply (rule_tac x=f in exI) apply simp apply (rule conjI)
  using f_fun_pred apply blast
      apply clarify    
      apply (subgoal_tac "wf_ty v \<and> wf_ty v'") prefer 2 apply (rule wf_entries) apply blast apply blast
      apply (subgoal_tac "wf_env (v#\<rho>)") prefer 2 apply (rule extend_wf_env) apply blast apply blast
      apply (subgoal_tac "\<lbrakk>e\<rbrakk>(v#\<rho>) = {B. \<exists>A. A \<in> D e (v#\<rho>) \<and> A <: B \<and> wf_ty B}")
       prefer 2 apply blast
      apply (subgoal_tac "v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>)") prefer 2 using f_lam f_fun_pred apply meson 
      apply (subgoal_tac "\<exists>A. A \<in> D e (v # \<rho>) \<and> A <: v' \<and> wf_ty v'") prefer 2 apply blast
      apply clarify
      apply blast
     apply clarify 
     apply (subgoal_tac "F A e \<rho> = (\<forall> v v'. (v,v') \<in> entries A \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk> (v#\<rho>))") prefer 2
      apply (rule f_lam) apply blast
     apply (subgoal_tac "F A e \<rho>")       
      apply (rule subsumption_fun) apply assumption apply assumption apply assumption
        apply assumption apply assumption apply clarify apply (meson subsumption)
     apply (subgoal_tac "\<forall> v v'. (v,v') \<in> entries A \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk> (v#\<rho>)") apply blast
     apply (metis (no_types, lifting) extend_wf_env mem_Collect_eq wf_entries)
    -- "app"
    apply simp apply (rule Collect_cong) apply (rule iffI) 
     apply clarify apply (rule_tac x=v' in exI) apply (rule conjI)
      apply (rule_tac x=A in exI) apply (rule conjI) apply assumption
      apply (rule_tac x=Aa in exI) apply (rule conjI) apply assumption
      apply (rule conjI) apply (subgoal_tac "v \<rightarrow> v' <: Aa \<rightarrow> v'") prefer 2
        apply blast apply (meson sub_trans) apply assumption apply blast
    apply clarify apply (rule_tac x=f in exI) apply (rule conjI)
     apply (rule_tac x=f in exI) apply (rule conjI) apply assumption  
     apply (rule conjI) apply blast apply (rule wf_d) apply assumption apply assumption
    apply (rule_tac x=v in exI) apply (rule conjI) apply (rule_tac x=v in exI)
     apply (rule conjI) apply assumption apply (rule conjI) apply blast apply (rule wf_d)
      apply assumption apply assumption apply (rule conjI) 
     apply (subgoal_tac "v \<rightarrow> A <: v \<rightarrow> v'") prefer 2 apply blast
     apply (meson sub_trans) apply assumption 
    -- "prim"
   apply simp apply (rule Collect_cong) apply (rule iffI)
    apply (meson sub_refl sub_trans)
   apply (meson sub_refl sub_trans wf_d)
    -- "if"
  apply simp apply (rule Collect_cong) apply (rule iffI)
   apply clarify
   apply (case_tac n) apply simp apply clarify
    apply (meson less_numeral_extra(3) sub_trans)
   apply (meson Suc_neq_Zero sub_trans zero_less_Suc)
  by blast

         
end