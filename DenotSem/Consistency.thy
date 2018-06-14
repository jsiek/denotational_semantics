theory Consistency
  imports Values
begin
  
inductive is_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v';
                          \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f1 \<and> (v2,v2') \<in> set f2 \<longrightarrow>
                            ((\<exists> v3. v1 \<sqsubseteq> v3 \<and> v2 \<sqsubseteq> v3 \<and> is_val v3) 
                              \<and> (\<exists> v3'. v1' \<sqsubseteq> v3' \<and> v2' \<sqsubseteq> v3')) 
                            \<or> \<not>(\<exists> v3. v1 \<sqsubseteq> v3 \<and> v2 \<sqsubseteq> v3 \<and> is_val v3) \<rbrakk>
                        \<Longrightarrow> is_val (VFun f)"


end