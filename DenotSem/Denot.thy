(*<*)
theory Denot
  imports Lambda Consistency
begin
(*>*)
  
section "Denotational Semantics of Lambda Calculus"

abbreviation fun_app :: "ty \<Rightarrow> ty \<Rightarrow> ty set" (infix "\<bullet>" 80) where
  "f \<bullet> v \<equiv> {v'. f <: v \<rightarrow> v' \<and> wf_ty v' }"

abbreviation up :: "ty \<Rightarrow> ty set" ("\<up>" 1000) where
  "up A \<equiv> {B. A <: B \<and> wf_ty B}"

fun E :: "exp \<Rightarrow> ty list \<Rightarrow> ty set" ("\<lbrakk>_\<rbrakk>_" [999] 1000) and
    F :: "ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> bool" where
  Enat: "\<lbrakk>ENat n\<rbrakk> \<rho> = \<up> (TNat n)" |
  Evar: "\<lbrakk>EVar k\<rbrakk> \<rho> = (if k < length \<rho> then \<up>(\<rho>!k) else {})" |
  Elam: "\<lbrakk>ELam e\<rbrakk> \<rho> = { f. wf_ty f \<and> F f e \<rho> }" |
  Eapp: "\<lbrakk>EApp e1 e2\<rbrakk> \<rho> = { v'. \<exists> f v. f \<in> \<lbrakk>e1\<rbrakk>\<rho> \<and> v \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> v' \<in> f \<bullet> v }" | 
  Eprim: "\<lbrakk>EPrim f e1 e2\<rbrakk> \<rho> = { v. \<exists> v1 v2 n1 n2. v1 \<in> \<lbrakk>e1\<rbrakk>\<rho> 
          \<and> v2 \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> v1 <: TNat n1 \<and> v2 <: TNat n2 \<and> TNat (f n1 n2) <: v \<and> wf_ty v }" |
  Eif: "\<lbrakk>EIf e1 e2 e3\<rbrakk> \<rho> = { v. \<exists> v1 n. v1 \<in> \<lbrakk>e1\<rbrakk>\<rho> \<and> v1 <: TNat n
         \<and> (n = 0 \<longrightarrow> v \<in> \<lbrakk>e3\<rbrakk>\<rho>) \<and> (n \<noteq> 0 \<longrightarrow> v \<in> \<lbrakk>e2\<rbrakk>\<rho>) }" |
  Fnat: "F (TNat n) e \<rho> = False" |
  Ffun: "F (v \<rightarrow> v') e \<rho> = (v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>))" |
  Finter: "F (v1 \<sqinter> v2) e \<rho> = (F v1 e \<rho> \<and> F v2 e \<rho>)"

(*<*)
end
(*>*)
