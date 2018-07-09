theory Denot
  imports LaurentValues Lambda
begin

fun E :: "exp \<Rightarrow> val list \<Rightarrow> val set" ("\<lbrakk>_\<rbrakk>_" [999] 1000) and
    F :: "val \<Rightarrow> exp \<Rightarrow> val list \<Rightarrow> bool" where
  Enat: "\<lbrakk>ENat n\<rbrakk> \<rho> = { VNat n }" |
  Evar: "\<lbrakk>EVar k\<rbrakk> \<rho> = (if k < length \<rho> then {v. v \<sqsubseteq> \<rho>!k } else {})" |
  Elam: "\<lbrakk>ELam e\<rbrakk> \<rho> = { t. F t e \<rho> }" |
  Eapp: "\<lbrakk>EApp e1 e2\<rbrakk> \<rho> = { v'. (\<exists> f v. f \<in> \<lbrakk>e1\<rbrakk>\<rho> \<and> v \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> v\<mapsto>v' \<sqsubseteq> f) }" | 
  Eprim: "\<lbrakk>EPrim f e1 e2\<rbrakk> \<rho> = { v. \<exists> n1 n2. VNat n1 \<in> \<lbrakk>e1\<rbrakk>\<rho> 
          \<and> VNat n2 \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> v = VNat (f n1 n2) }" |
  Eif: "\<lbrakk>EIf e1 e2 e3\<rbrakk> \<rho> = { v. \<exists> n. VNat n \<in> \<lbrakk>e1\<rbrakk>\<rho>
         \<and> (n = 0 \<longrightarrow> v \<in> \<lbrakk>e3\<rbrakk>\<rho>) \<and> (n \<noteq> 0 \<longrightarrow> v \<in> \<lbrakk>e2\<rbrakk>\<rho>) }" |
  FNat : "F (VNat n) e \<rho> = False" | 
  FFun: "F (v \<mapsto> v') e \<rho> = (v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>))" |
  FUnion: "F (v1 \<squnion> v2) e \<rho> = (F v1 e \<rho> \<and> F v2 e \<rho>)"

end