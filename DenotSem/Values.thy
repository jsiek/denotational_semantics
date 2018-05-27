theory Values
imports Main
begin

datatype val = VNat nat | VFun "entry list" and
  entry = Entry val val (infix "\<mapsto>" 70)

inductive consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 52) and
    inconsistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "!~" 52) where
  vnat_consis[intro!]: "(VNat n) ~ (VNat n)" |
  vfun_consis[intro!]: "\<lbrakk> \<forall> v1 v1' v2 v2'. v1 \<mapsto>v1' \<in> set t1 \<and> v2\<mapsto>v2' \<in> set t2 \<longrightarrow>
                        (v1 ~ v2 \<and> v1' ~ v2') \<or> v1 !~ v2 \<rbrakk> \<Longrightarrow> (VFun t1) ~ (VFun t2)" |
  vnat_inconsis[intro!]: "n \<noteq> n' \<Longrightarrow> (VNat n) !~ (VNat n')" |
  vfun_inconsis[intro!]: "\<lbrakk> v1\<mapsto>v1' \<in> set t1; v2\<mapsto>v2' \<in> set t2; v1 ~ v2; v1' !~ v2' \<rbrakk> 
                         \<Longrightarrow> (VFun t1) !~ (VFun t2)" |
  vnat_vfun_inconsis[intro!]: "VNat n !~ VFun t" |
  vfun_vnat_inconsis[intro!]: "VFun t !~ VNat n"

definition is_fun :: "entry list \<Rightarrow> bool" where
  "is_fun t \<equiv> (\<forall> v1 v2 v1' v2'. v1\<mapsto>v1' \<in> set t \<and> v2\<mapsto>v2' \<in> set t \<and> v1 ~ v2 \<longrightarrow> v1' ~ v2')"
    
inductive is_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> is_fun t; \<forall> v v'. v\<mapsto>v' \<in> set t \<longrightarrow> is_val v \<and> is_val v' \<rbrakk>
                        \<Longrightarrow> is_val (VFun t)"
  
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then VNat n1 else undefined)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = (VFun (f1 @ f2))" |
  "v1 \<squnion> v2 = undefined"
  
fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> val list" (infix "\<squnion>" 56) where
  "env_join [] [] = []" |
  "env_join (v#\<rho>) (v'#\<rho>') = (v \<squnion> v')#(env_join \<rho> \<rho>')" |
  "env_join \<rho> \<rho>' = undefined" 

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) and
    entry_le :: "entry \<Rightarrow> entry \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) and
    fun_le :: "entry list \<Rightarrow> entry list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) and
    fun_in :: "entry \<Rightarrow> entry list \<Rightarrow> bool" ("_ in _" [56,56] 55)
    where
  vnat_le[intro!]: "(VNat n) \<sqsubseteq> (VNat n)" |
  vfun_le[intro!]: "t1 \<sqsubseteq> t2 \<Longrightarrow> (VFun t1) \<sqsubseteq> (VFun t2)" |
  entry_le[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2'\<rbrakk> \<Longrightarrow> (v1\<mapsto>v1') \<sqsubseteq> (v2\<mapsto>v2')" |
  empty_le[intro!]: "[] \<sqsubseteq> t2" |
  ins_le[intro!]: "\<lbrakk> p in t2; t1 \<sqsubseteq> t2 \<rbrakk> \<Longrightarrow>  p#t1 \<sqsubseteq> t2" |
  fun_in_ax[intro!]: "\<lbrakk> p \<in> set t \<rbrakk> \<Longrightarrow> p in t" |
  fun_in_sub: "\<lbrakk> p1 in t; p1 \<sqsubseteq> p2 \<rbrakk> \<Longrightarrow> p2 in t" 
(*
  fun_in_union: "\<lbrakk> (v1,v1') in t; (v2,v2') in t; v \<sqsubseteq> v1 \<squnion> v2; v1' \<squnion> v2' \<sqsubseteq> v' \<rbrakk>
                   \<Longrightarrow> (v,v') in t"
*)
  
inductive env_le :: "val list \<Rightarrow> val list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  empty_env_le[intro!]: "([]::val list) \<sqsubseteq> []" |
  cons_env_le[intro!]: "\<lbrakk> (v::val) \<sqsubseteq> v'; \<rho> \<sqsubseteq> \<rho>' \<rbrakk> \<Longrightarrow> (v#\<rho>) \<sqsubseteq> (v'#\<rho>')"

inductive_cases 
  le_fun_fun_inv[elim!]: "VFun t1 \<sqsubseteq> VFun t2" and
  le_fun_nat_inv[elim!]: "VFun t2 \<sqsubseteq> VNat x1" and
  le_any_nat_inv[elim!]: "v \<sqsubseteq> VNat n" and
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v" and
  le_fun_any_inv[elim!]: "VFun t \<sqsubseteq> v" and
  le_any_fun_inv[elim!]: "v \<sqsubseteq> VFun t" and
  le_cons_fun_inv[elim!]: "((p::entry)#t1) \<sqsubseteq> t2" and
  le_cons_env_inv[elim!]: "((v::val)#\<rho>) \<sqsubseteq> (v'#\<rho>')"
  
section "Joins and Meets"
  
abbreviation val_lub :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "val_lub v v1 v2 \<equiv> v1 \<sqsubseteq> v \<and> v2 \<sqsubseteq> v \<and> (\<forall> v'. v1 \<sqsubseteq> v' \<and> v2 \<sqsubseteq> v' \<longrightarrow> v \<sqsubseteq> v')"

abbreviation val_glb :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "val_glb v v1 v2 \<equiv> v \<sqsubseteq> v1 \<and> v \<sqsubseteq> v2 \<and> (\<forall> v'. v' \<sqsubseteq> v1 \<and> v' \<sqsubseteq> v2 \<longrightarrow> v' \<sqsubseteq> v)"
    
end