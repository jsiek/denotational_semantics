theory Denot
  imports Values Lambda Consistency
begin

abbreviation fun_app :: "ty \<Rightarrow> ty \<Rightarrow> ty set" (infix "\<bullet>" 80) where
  "f \<bullet> v \<equiv> {v'. f <: v \<rightarrow> v' \<and> wf_ty v' }"

abbreviation up :: "ty \<Rightarrow> ty set" ("\<up>" 1000) where
  "up A \<equiv> {B. A <: B \<and> wf_ty B}"
  
fun E :: "exp \<Rightarrow> ty list \<Rightarrow> ty set" ("\<lbrakk>_\<rbrakk>_" [999] 1000) where
  Enat: "\<lbrakk>ENat n\<rbrakk> \<rho> = { TNat n }" |
  Evar: "\<lbrakk>EVar k\<rbrakk> \<rho> = (if k < length \<rho> then \<up>(\<rho>!k) else {})" |
  Elam: "\<lbrakk>ELam e\<rbrakk> \<rho> = { f. wf_fun f \<and> (\<forall>v v'. v\<rightarrow>v' \<in> atoms f \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>)) }" |
  Eapp: "\<lbrakk>EApp e1 e2\<rbrakk> \<rho> = { v'. \<exists> f v. f \<in> \<lbrakk>e1\<rbrakk>\<rho> \<and> v \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> v' \<in> f \<bullet> v }" | 
  Eprim: "\<lbrakk>EPrim f e1 e2\<rbrakk> \<rho> = { v. \<exists> n1 n2. TNat n1 \<in> \<lbrakk>e1\<rbrakk>\<rho> 
          \<and> TNat n2 \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> v = TNat (f n1 n2) }" |
  Eif: "\<lbrakk>EIf e1 e2 e3\<rbrakk> \<rho> = { v. \<exists> n. TNat n \<in> \<lbrakk>e1\<rbrakk>\<rho>
         \<and> (n = 0 \<longrightarrow> v \<in> \<lbrakk>e3\<rbrakk>\<rho>) \<and> (n \<noteq> 0 \<longrightarrow> v \<in> \<lbrakk>e2\<rbrakk>\<rho>) }"

end