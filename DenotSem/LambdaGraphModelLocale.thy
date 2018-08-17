theory LambdaGraphModelLocale
  imports Lambda Denot Deterministic DenotFSet
begin
  
locale model_base =
  fixes D :: "exp \<Rightarrow> 'a list \<Rightarrow> 'a set" and up :: "'a \<Rightarrow> 'a set" and
    inj_nat :: "nat \<Rightarrow> 'a set" and app :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" and wf:: "'a \<Rightarrow> bool" and
    is_fun :: "'a \<Rightarrow> bool" and entries :: "'a \<Rightarrow> ('a \<times> 'a) set"
begin
  
definition wf_env :: "'a list \<Rightarrow> bool" where
  "wf_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> wf (\<rho>!k)"

end  

locale lambda_graph_model = model_base +
  assumes d_var: "\<lbrakk> wf_env \<rho>; x < length \<rho> \<rbrakk> \<Longrightarrow> D (EVar x) \<rho> = up (\<rho>!x)" and
    d_nat: "wf_env \<rho> \<Longrightarrow> D (ENat n) \<rho> = inj_nat n" and
    d_lam: "wf_env \<rho> \<Longrightarrow> D (ELam e) \<rho> = { f. wf f \<and> is_fun f 
                                        \<and> (\<forall> v v'. (v,v') \<in> entries f \<longrightarrow> v' \<in> D e (v#\<rho>))}" and
    d_app: "wf_env \<rho> \<Longrightarrow> D (EApp e1 e2) \<rho> = {v'. \<exists> f v. f \<in> D e1 \<rho> \<and> v \<in> D e2 \<rho> \<and> v' \<in> app f v }" and
    d_prim: "wf_env \<rho> \<Longrightarrow> D (EPrim f e1 e2) \<rho> = {v. \<exists> n1 n2. inj_nat n1 \<subseteq> D e1 \<rho> \<and> inj_nat n2 \<subseteq> D e2 \<rho> 
            \<and> v \<in> inj_nat (f n1 n2)}" and
    d_if: "wf_env \<rho> \<Longrightarrow> D (EIf e1 e2 e3) \<rho> = {v. \<exists> n. inj_nat n \<subseteq> D e1 \<rho> \<and>
          (n = 0 \<longrightarrow> v \<in> D e3 \<rho>) \<and> (n \<noteq> 0 \<longrightarrow> v \<in> D e2 \<rho>) }"
    
abbreviation inj_nat_ty :: "nat \<Rightarrow> ty set" where
  "inj_nat_ty n \<equiv> \<up>(TNat n)"

lemma inj_nat_sub: "wf_env \<rho> \<Longrightarrow> 
  (inj_nat_ty n \<subseteq> Denot.E e \<rho>) = (\<exists> T. T \<in> Denot.E e \<rho> \<and> T <: TNat n)"
  apply auto using subsumption by (meson nat_wf_ty)
  
lemma f_lam: "fun_pred f \<Longrightarrow> F f e \<rho> = (\<forall> v v'. (v,v') \<in> entries f \<longrightarrow> v' \<in> Denot.E e (v#\<rho>))"
  by (induction f) auto

lemma f_fun_pred: "F f e \<rho> \<Longrightarrow> fun_pred f"
  by (induction f) auto
    
interpretation intersection_model: lambda_graph_model Denot.E up inj_nat_ty fun_app wf_ty fun_pred entries
  apply unfold_locales
       apply force
      apply force
     defer
     apply force
    apply simp apply (rule equalityI) apply (rule subsetI) apply simp apply clarify
     apply (subgoal_tac "TNat n1 \<in> \<lbrakk> e1 \<rbrakk>\<rho>") prefer 2
  using inj_nat_sub model_base.wf_env_def apply blast
     apply (subgoal_tac "TNat n2 \<in> \<lbrakk> e2 \<rbrakk>\<rho>") prefer 2
  using inj_nat_sub model_base.wf_env_def apply blast
     apply (rule_tac x=n1 in exI) 
  using inj_nat_sub model_base.wf_env_def apply blast
  apply (smt Collect_mono inj_nat_sub model_base.wf_env_def)
  apply simp apply (rule equalityI) apply clarify
    apply (rule_tac x=n in exI) 
  apply (metis (mono_tags, lifting) mem_Collect_eq model_base.wf_env_def nat_wf_ty subsetI subsumption)
   apply blast
  using f_lam f_fun_pred 
  by (smt Collect_cong Denot.Elam)

abbreviation inj_nat_val :: "nat \<Rightarrow> val set" where
  "inj_nat_val n \<equiv> { VNat n }"
  
abbreviation up_val :: "val \<Rightarrow> val set" where
  "up_val v \<equiv> {v'. v' \<sqsubseteq> v}" 
  
abbreviation simple_apply :: "val \<Rightarrow> val \<Rightarrow> val set" where
  "simple_apply v1 v2 \<equiv> { v3. \<exists> f v2' v3'. v1 = VFun f \<and> (v2', v3') \<in> fset f \<and> v2' \<sqsubseteq> v2 \<and> v3 \<sqsubseteq> v3' }"
  
fun is_fun_val :: "val \<Rightarrow> bool" where
  "is_fun_val (VNat n) = False" |
  "is_fun_val (VFun f) = True"
  
fun fun_entries :: "val \<Rightarrow> (val \<times> val) set" where
  "fun_entries (VNat n) = {}" |
  "fun_entries (VFun f) = fset f"
  
interpretation simple_model: lambda_graph_model DenotFSet.E up_val inj_nat_val simple_apply 
  "\<lambda>v. True" is_fun_val fun_entries
  apply unfold_locales
  apply force
  apply force
     defer
     defer
     apply force
    apply force
  apply (smt Collect_cong DenotFSet.Elam fun_entries.simps(2) is_fun_val.elims(2) is_fun_val.simps(2))
  apply simp apply blast
  done    
  
end