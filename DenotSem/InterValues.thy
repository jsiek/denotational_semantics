theory InterValues
imports Main
begin

datatype val = VNat nat | VFun val val (infix "\<mapsto>" 70) | VJoin val val (infix "\<squnion>" 69)| VBot ("\<bottom>")
  
inductive funny :: "val \<Rightarrow> bool" where
  fun_funny[intro!]: "funny (v \<mapsto> v')" |
  join_funny[intro!]: "\<lbrakk> funny v1; funny v2 \<rbrakk> \<Longrightarrow> funny (v1 \<squnion> v2)"

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" |
  le_bot_bot[intro!]: "\<bottom> \<sqsubseteq> \<bottom>" |
  le_bot_fun[intro!]: "\<bottom> \<sqsubseteq> v\<mapsto>v'" |
  le_join_left[intro!]: "v1 \<sqsubseteq> v2 \<Longrightarrow> v1 \<sqsubseteq> v2 \<squnion> v3" |
  le_join_right[intro!]: "v1 \<sqsubseteq> v3 \<Longrightarrow> v1 \<sqsubseteq> v2 \<squnion> v3" |
  le_left_join[intro!]: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<squnion> v2 \<sqsubseteq> v3" |
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" |
  le_distr: "v \<mapsto> (v1\<squnion>v2) \<sqsubseteq> v\<mapsto>v1 \<squnion> v\<mapsto>v2"

inductive_cases
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_fun_fun_inv[elim!]: "v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> v \<mapsto> v'" and
  le_fun_nat_inv[elim!]: "v \<mapsto> v' \<sqsubseteq> VNat n" and
  le_fun_any_inv_aux: "v \<mapsto> v' \<sqsubseteq> v"
  
abbreviation equivalent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<approx>" 60) where
  "v \<approx> v' \<equiv> v \<sqsubseteq> v' \<and> v' \<sqsubseteq> v"
  
lemma le_bot_inv_aux: fixes v1::val 
  assumes v12: "v1 \<sqsubseteq> v2" and v2b: "v2 = \<bottom>"
  shows "v1 \<approx> \<bottom>"
  using v12 v2b by (induction rule: val_le.induct) auto

lemma le_bot_inv[elim!]: "\<lbrakk> v \<sqsubseteq> \<bottom>; v \<approx> \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_bot_inv_aux by auto      

lemma le_refl[intro!]: "v \<sqsubseteq> v"
  apply (induction v)
     apply blast+
  apply (simp add: le_join_left le_join_right le_left_join)
  apply blast
  done
 
lemma le_fun_any_inv[elim!]: "\<lbrakk> v12 \<sqsubseteq> v3; v12 = v1 \<mapsto> v2 \<rbrakk> \<Longrightarrow> funny v3"
  apply (induction v12 v3 arbitrary: v1 v2 rule: val_le.induct)
  apply force+
  sorry    
    
  
lemma le_trans: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  apply (induction v1 v2 arbitrary: v3 rule: val_le.induct)
         apply blast
        apply blast
    
    
    
end