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
  
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then (VNat n1) else undefined)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = (VFun (f1 @ f2))" |
  "v1 \<squnion> v2 = undefined"

  (* Adapted from BCD and EHR subtyping (Lambda Calculus with Types 2013) *) 
inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  le_refl[intro!]: "(v::val) \<sqsubseteq> v" |
  le_trans[trans]: "\<lbrakk> (v1::val) \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3" |
  le_join_left[intro!]: "v1 \<sqsubseteq> v1 \<squnion> v2 " | (* incl_L *)
  le_join_right[intro!]: "v2 \<sqsubseteq> v1 \<squnion> v2" | (* incl_R *)
  le_left_join[intro!]: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<squnion> v2 \<sqsubseteq> v3" | (* glb *)
  le_bot[intro!]: "\<bottom> \<sqsubseteq> v \<mapsto> v'" (* nu *) |
  le_fun[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" | (* arrow *)
  le_distr: "v \<mapsto> (v1 \<squnion> v2) \<sqsubseteq> (v\<mapsto>v1) \<squnion> (v \<mapsto>v2)" (* arrow intersect *)

inductive_cases fun_join_inv: "v1\<mapsto>v1' \<sqsubseteq> v2 \<squnion> v3" (* not useful *)

  
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

fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> val list" (infix "\<squnion>" 56) where
  "env_join [] [] = []" |
  "env_join (v#\<rho>) (v'#\<rho>') = (v \<squnion> v')#(\<rho>\<squnion>\<rho>')" 
 
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
    
lemma inconsis_not_consis[simp]: "(v1 !~ v2) = (\<not> (v1 ~ v2))"
  sorry

proposition mon: fixes v1::val and v2::val
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'"
  shows "v1 \<squnion> v2 \<sqsubseteq> v1' \<squnion> v2'"
proof -
  have 3: "v1' \<sqsubseteq> v1' \<squnion> v2'" by blast
  have 4: "v2' \<sqsubseteq> v1' \<squnion> v2'" by blast
  have 5: "v1 \<sqsubseteq> v1' \<squnion> v2'" using 1 3 le_trans by blast
  have 6: "v2 \<sqsubseteq> v1' \<squnion> v2'" using 2 4 le_trans by blast
  show "v1 \<squnion> v2 \<sqsubseteq> v1' \<squnion> v2'" using 5 6 by blast
qed
    
lemma consis_val_join_val_aux:
  "(v1 ~ v2 \<longrightarrow> is_val v1 \<longrightarrow> is_val v2 \<longrightarrow> is_val (v1 \<squnion> v2))
      \<and> (v1 !~ v2 \<longrightarrow> True)"
  apply (induction rule: consistent_inconsistent.induct)
  apply force
  defer
      apply force
     apply force
  apply force
   apply force
  apply (rule impI)+
proof -
  fix f1 f2 assume IH: "\<forall>v1 v1' v2 v2'. v1 \<mapsto> v1' \<sqsubseteq> VFun f1 \<and> v2 \<mapsto> v2' \<sqsubseteq> VFun f2 \<longrightarrow>
          (v1 ~ v2 \<and> (is_val v1 \<longrightarrow> is_val v2 \<longrightarrow> is_val (v1 \<squnion> v2))) \<and>
          v1' ~ v2' \<and> (is_val v1' \<longrightarrow> is_val v2' \<longrightarrow> is_val (v1' \<squnion> v2')) \<or>
          v1 !~ v2 \<and> True" and
    vf1: "is_val (VFun f1)" and vf2: "is_val (VFun f2)"
  let ?v3 = "VFun (f1@f2)"
  have "is_val ?v3"
  proof (rule vfun_is_val) 
    show "is_fun (f1@f2)" 
      apply (simp only: is_fun_def) apply (rule vfun_consis)
    proof clarify
      fix v1 v1' v2 v2'
      assume v11_f12: "v1 \<mapsto> v1' \<sqsubseteq> VFun (f1 @ f2)" and v22_f12: "v2 \<mapsto> v2' \<sqsubseteq> VFun (f1 @ f2)" 
        and nc_v12: "\<not> v1 !~ v2"
      have v1_v2: "v1 ~ v2" using nc_v12 by simp
      
          
      have v1p_v2p: "v1' ~ v2'" sorry
      show "v1 ~ v2 \<and> v1' ~ v2'" using v1_v2 v1p_v2p by blast
    qed
  next
    show "\<forall>v v'. (v, v') \<in> set (f1 @ f2) \<longrightarrow> is_val v \<and> is_val v'"
      using vf1 vf2 by auto        
  qed    
  then show "is_val (VFun f1 \<squnion> VFun f2)" by simp
qed
    
  
end