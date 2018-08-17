theory LambdaGraphModelLocale
  imports Lambda DenotAlt Deterministic DenotFSet
begin
  
locale model_base =
  fixes D :: "exp \<Rightarrow> 'a list \<Rightarrow> 'a set" and le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<lesssim>" 55) and
    inj_nat :: "nat \<Rightarrow> 'a" and app :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" and wf:: "'a \<Rightarrow> bool" and
    is_fun :: "'a \<Rightarrow> bool" and entries :: "'a \<Rightarrow> ('a \<times> 'a) set"
begin
  
definition wf_env :: "'a list \<Rightarrow> bool" where
  "wf_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> wf (\<rho>!k)"

end  

locale lambda_graph_model = model_base +
  assumes d_var: "\<lbrakk> wf_env \<rho> \<rbrakk> \<Longrightarrow> D (EVar x) \<rho> = (if x < length \<rho> then {\<rho>!x} else {})" and
    d_nat: "wf_env \<rho> \<Longrightarrow> D (ENat n) \<rho> = {inj_nat n}" and
    d_lam: "wf_env \<rho> \<Longrightarrow> D (ELam e) \<rho> = { f. wf f \<and> is_fun f 
              \<and> (\<forall> v v'. (v,v') \<in> entries f \<longrightarrow> (\<exists>v''. v'' \<in> D e (v#\<rho>) \<and> v' \<lesssim> v''))}" and
    d_app: "wf_env \<rho> \<Longrightarrow> D (EApp e1 e2) \<rho> = {v'. \<exists> f v. f \<in> D e1 \<rho> \<and> v \<in> D e2 \<rho> \<and> v' \<in> app f v }" and
    d_prim: "wf_env \<rho> \<Longrightarrow> D (EPrim f e1 e2) \<rho> = {v. wf v \<and> (\<exists> v1 v2 n1 n2. v1 \<in> D e1 \<rho> \<and> v2 \<in> D e2 \<rho> 
            \<and> inj_nat n1 \<lesssim> v1 \<and> inj_nat n2 \<lesssim> v2 \<and> v \<lesssim> inj_nat (f n1 n2))}" and
    d_if: "wf_env \<rho> \<Longrightarrow> D (EIf e1 e2 e3) \<rho> = {v. \<exists> v1 n1. v1 \<in> D e1 \<rho> \<and> inj_nat n1 \<lesssim> v1 \<and>
          (n1 = 0 \<longrightarrow> v \<in> D e3 \<rho>) \<and> (n1 \<noteq> 0 \<longrightarrow> v \<in> D e2 \<rho>) }"
    
interpretation intersection_model: lambda_graph_model DenotAlt.D "(\<lambda>a b. (b::ty) <: a)" TNat fun_app wf_ty fun_pred entries
  apply unfold_locales apply force+ done
    
  
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
  
interpretation simple_model: lambda_graph_model DenotFSet.E val_le VNat simple_apply 
  "\<lambda>v. True" is_fun_val fun_entries
  apply unfold_locales
       apply force
      apply force
     defer
     apply force
    apply simp apply (rule Collect_cong) apply (rule iffI) 
     apply blast using val_le.simps apply auto[1]
  using val_le.simps apply auto[1] 
  apply simp apply (rule Collect_cong) apply (rule iffI) 
  using fun_entries.simps(2) is_fun_val.simps(2) apply blast
  using fun_entries.simps(2) is_fun_val.elims(2) by force

    
  
end