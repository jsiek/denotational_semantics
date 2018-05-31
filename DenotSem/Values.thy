theory Values
imports Main
begin

datatype val = VNat nat | VFun "(val \<times> val) list" 

abbreviation make_entry :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<mapsto>" 70) where
  "v \<mapsto> v' \<equiv> VFun [(v,v')]"
abbreviation bottom_fun :: "val" ("\<bottom>" 100) where
  "bottom_fun \<equiv> VFun []"
  
type_synonym entry = "val \<times> val" 
type_synonym func = "entry list"  
  
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 @ f2))" |
  "v1 \<squnion> v2 = None"

  (* Adapted from BCD subtyping (Lambda Calculus with Types 2013), but with nu instead of U *) 
inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  le_refl[intro!]: "(v::val) \<sqsubseteq> v" |
  le_trans[trans]: "\<lbrakk> (v1::val) \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3" |
  le_join_left: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v1 \<sqsubseteq> v12" | (* incl_L *)
  le_join_right[intro!]: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v2 \<sqsubseteq> v12" | (* incl_R *)
  le_left_join[intro!]: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12\<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" | (* glb *)
  le_bot[intro!]: "\<bottom> \<sqsubseteq> v \<mapsto> v'" (* nu *) |
  le_fun[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" | (* arrow *)
  le_distr: "\<lbrakk> v1 \<squnion> v2 = Some v12; (v\<mapsto>v1) \<squnion> (v \<mapsto>v2) = Some vv12 \<rbrakk>
     \<Longrightarrow> v \<mapsto> v12 \<sqsubseteq> vv12" (* arrow intersect *)

inductive consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 52) and
    inconsistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "!~" 52) where
  vnat_consis[intro!]: "(VNat n) ~ (VNat n)" |
  vfun_consis[intro!]: "\<lbrakk> \<forall> v1 v1' v2 v2'. v1\<mapsto>v1' \<sqsubseteq> VFun f1 \<and> v2\<mapsto>v2' \<sqsubseteq> VFun f2 \<longrightarrow>
                        (v1 ~ v2 \<and> v1' ~ v2') \<or> v1 !~ v2 \<rbrakk> \<Longrightarrow> (VFun f1) ~ (VFun f2)" |
  vnat_inconsis[intro!]: "n \<noteq> n' \<Longrightarrow> (VNat n) !~ (VNat n')" |
  vfun_inconsis[intro!]: "\<lbrakk> v1 \<mapsto> v1' \<sqsubseteq> VFun f1; v2 \<mapsto> v2' \<sqsubseteq> VFun f2; v1 ~ v2; v1' !~ v2' \<rbrakk> 
                         \<Longrightarrow> (VFun f1) !~ (VFun f2)" |
  vnat_vfun_inconsis[intro!]: "VNat n !~ VFun f" |
  vfun_vnat_inconsis[intro!]: "VFun f !~ VNat n"

inductive_cases 
  vnat_consis_inv[elim!]: "VNat n ~ VNat n'" and
  vfun_consis_inv[elim!]: "VFun f ~ VFun f'" and
  vnat_inconsis_inv[elim!]: "VNat n !~ VNat n'" and
  vfun_inconsis_inv[elim!]: "VFun f !~ VFun f'" and
  vnat_vfun_consis_inv[elim!]: "VNat n ~ VFun f" and
  vfun_vnat_consis_inv[elim!]: "VFun f ~ VNat n"
  
inductive consis_env :: "val list \<Rightarrow> val list \<Rightarrow> bool" where
  consis_env_nil[intro!]: "consis_env [] []" |
  consis_env_cons[intro!]: "\<lbrakk> v ~ v'; consis_env \<rho> \<rho>' \<rbrakk> \<Longrightarrow> consis_env (v#\<rho>) (v'#\<rho>')" 

definition is_fun :: "func \<Rightarrow> bool" where
  "is_fun f \<equiv> VFun f ~ VFun f"
    
inductive is_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> is_fun f; \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v' \<rbrakk>
                        \<Longrightarrow> is_val (VFun f)"
inductive_cases
  vfun_is_val_inv[elim!]: "is_val (VFun f)"

definition val_env :: "val list \<Rightarrow> bool" where
  "val_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> is_val (\<rho>!k)"

fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> (val list) option" (infix "\<squnion>" 56) where
  "env_join [] [] = Some []" |
  "env_join (v#\<rho>) (v'#\<rho>') =
     (case (v \<squnion> v') of
        None \<Rightarrow> None
      | Some v'' \<Rightarrow> 
        (case env_join \<rho> \<rho>' of
          None \<Rightarrow> None
        | Some \<rho>'' \<Rightarrow> Some (v''#\<rho>'')))" |
  "env_join \<rho> \<rho>' = None" 
 
definition env_le :: "val list \<Rightarrow> val list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "(\<rho>::val list) \<sqsubseteq> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k \<sqsubseteq> \<rho>'!k)" 

section "Size of Values (for induction)"
  
function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + fsize t" |
"fsize [] = 0" |
"fsize ((v,v')#t) = 1 + vsize v + vsize v' + fsize t"
  by pat_completeness auto
termination vsize by size_change
      
lemma "(v1 ~ v2 \<longrightarrow> (\<exists> v3. v1 \<squnion> v2 = Some v3))
      \<and> (v1 !~ v2 \<longrightarrow> True)"
  by (induction rule: consistent_inconsistent.induct) auto

    
  
end