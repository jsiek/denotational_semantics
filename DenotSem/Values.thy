theory Values
imports Main
begin

datatype val = VNat nat | VFun "(val \<times> val) list" 
type_synonym entry = "val \<times> val" 
type_synonym func = "entry list"  

function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + fsize t" |
"fsize [] = 0" |
"fsize ((v,v')#t) = 1 + vsize v + vsize v' + fsize t"
  by pat_completeness auto
termination vsize by size_change

abbreviation make_entry :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<mapsto>" 70) where
  "v \<mapsto> v' \<equiv> VFun [(v,v')]"
abbreviation bottom_fun :: "val" ("\<bottom>" 100) where
  "bottom_fun \<equiv> VFun []"
  
  
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 @ f2))" |
  "v1 \<squnion> v2 = None"

  (* Adapted from BCD and EHR subtyping (Lambda Calculus with Types 2013) *) 
inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" | 
(*
  le_refl[intro!]: "(v::val) \<sqsubseteq> v" |
  le_trans[intro!]: "\<lbrakk> (v1::val) \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3" |
  le_join_left[intro!]: "v1 \<squnion> v2 = Some v3 \<Longrightarrow> v1 \<sqsubseteq> v3" | (* v1 \<sqsubseteq> v1 \<squnion> v2, incl_L *)
  le_join_right[intro!]: "v1 \<squnion> v2 = Some v3 \<Longrightarrow> v2 \<sqsubseteq> v3" | (* v2 \<sqsubseteq> v1 \<squnion> v2, incl_R *)
  le_left_join[intro!]: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" | (* glb *)
*)
(*
  le_bot[intro!]: "\<bottom> \<sqsubseteq> v \<mapsto> v'" (* nu *) |
*)
  le_bot[intro!]: "\<bottom> \<sqsubseteq> VFun f" |  
  le_cons_left[intro!]: "\<lbrakk> VFun [p] \<sqsubseteq> VFun f2; VFun f1 \<sqsubseteq> VFun f2 \<rbrakk> \<Longrightarrow> VFun (p#f1) \<sqsubseteq> VFun f2" |
  le_cons_right1[intro!]: "VFun [p] \<sqsubseteq> VFun (p#f2)" |
  le_cons_right2[intro!]: "VFun f1 \<sqsubseteq> VFun f2 \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (p#f2)" |
  le_fun[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1\<mapsto>v1' \<sqsubseteq> v2\<mapsto> v2'"  (* arrow *)
(* the following rule makes things much more complicated -Jeremy
  le_distr: "v \<mapsto> (v1 \<squnion> v2) \<sqsubseteq> (v\<mapsto>v1) \<squnion> (v \<mapsto>v2)" (* arrow intersect *)
*)
 
inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_cons_left_inv: "VFun (a # f2) \<sqsubseteq> VFun f3" and
  le_single_left_inv: "VFun [a] \<sqsubseteq> VFun f" and
  le_single_cons_right_inv: "VFun [a] \<sqsubseteq> VFun (b#f)" 

lemma le_fun_bot_inv_aux: "v1 \<sqsubseteq> v2 \<Longrightarrow> (\<forall> a f. v1 = VFun f \<longrightarrow> v2 = VFun [] \<longrightarrow> f = [])"
  apply (induction v1 v2 rule: val_le.induct)
  apply force
  apply (case_tac v2) apply force apply (rule allI)+ apply (rule impI)+
       apply (case_tac x2) apply force apply force
  apply (case_tac v1) apply force apply (case_tac v2) apply force apply force
  apply (case_tac v1) apply force apply (case_tac v2) apply force apply force
  apply (case_tac v1) apply force apply (case_tac v2) apply force 
    apply (rule allI)+ apply (rule impI)+
  apply (case_tac x2) apply force apply force 
  apply force
  done

lemma le_fun_bot_inv[elim!]: "\<lbrakk> VFun f \<sqsubseteq> \<bottom>; f = [] \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_fun_bot_inv_aux by simp      
  
lemma le_fun_refl_aux: "\<lbrakk> \<forall>m<Suc (fsize x2).
          \<forall>x. m = vsize x \<longrightarrow> x \<sqsubseteq> x \<rbrakk> \<Longrightarrow> VFun x2 \<sqsubseteq> VFun x2"
  apply (induction x2) 
  apply force
  apply (rule le_cons_left)
   apply (rule le_cons_right1)
  apply (rule le_cons_right2)
   apply (erule_tac x="vsize (VFun x2)" in allE)
  apply (erule impE) apply force
  apply force
  done
    
lemma le_refl_aux: fixes v::val shows "n = vsize v \<Longrightarrow> v \<sqsubseteq> v"
  apply (induction n arbitrary: v rule: nat_less_induct)
  apply (case_tac v)
  apply force
  apply simp using le_fun_refl_aux apply blast
  done
    
proposition le_refl[intro!]: fixes v::val shows "v \<sqsubseteq> v" using le_refl_aux by blast
    
lemma le_fun_cons_left_inv_aux: 
  "v1 \<sqsubseteq> v2 \<Longrightarrow> (\<forall> a f1 f2. v1 = VFun (a # f1) \<longrightarrow> v2 = VFun f2 \<longrightarrow>
      VFun [a] \<sqsubseteq> VFun f2 \<and> VFun f1 \<sqsubseteq> VFun f2)"
  apply (induction v1 v2 rule: val_le.induct)
  apply force
  apply force
  apply simp 
  apply simp apply blast
  apply clarify apply simp apply clarify apply blast
  apply simp apply (rule conjI) apply (simp add: le_fun)
  apply blast
  done

lemma le_fun_cons_left_inv[elim!]: 
  "\<lbrakk> VFun (a#f1) \<sqsubseteq> VFun f2; \<lbrakk> VFun [a] \<sqsubseteq> VFun f2; VFun f1 \<sqsubseteq> VFun f2 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_fun_cons_left_inv_aux[of "VFun (a#f1)" "VFun f2"] by simp

lemma le_fun_elt: "a \<in> set f \<Longrightarrow> VFun [a] \<sqsubseteq> VFun f"
  apply (induction f)
   apply force
  apply simp apply (erule disjE) apply force apply force
  done
    
lemma le_fun_subset: "\<lbrakk> set f1 \<subseteq> set f2 \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
  apply (induction f1 arbitrary: f2)
   apply force
  apply simp apply (erule conjE)
  apply (rule le_cons_left)
   apply (rule le_fun_elt) apply blast
  apply blast
  done

(*  VFun f1 \<sqsubseteq> VFun (a # f2)  *)
lemma le_factor_cons: "VFun f1 \<sqsubseteq> VFun (a # f2) \<Longrightarrow>
   \<exists> f3 f4. set f1 = set(f3@f4) \<and> VFun f3 \<sqsubseteq> VFun [a] \<and> VFun f4 \<sqsubseteq> VFun f2"
  apply (induction f1 arbitrary: a f2)
   apply force
  apply (erule le_fun_cons_left_inv)
(*    UNDER CONSTRUCTION
  *)
    
lemma le_fun_trans_aux:
   assumes IH: "\<forall>m<size (VFun f2).
          \<forall>v1 v2. m = size v2 \<longrightarrow> v1 \<sqsubseteq> v2 \<longrightarrow> (\<forall>v3. v2 \<sqsubseteq> v3 \<longrightarrow> v1 \<sqsubseteq> v3)"
    and f1_f2: "VFun f1 \<sqsubseteq> VFun f2" and f2_f3: "VFun f2 \<sqsubseteq> VFun f3"
  shows "VFun f1 \<sqsubseteq> VFun f3"
  using f1_f2 f2_f3 apply (induction f2 arbitrary: f1 f3)
  apply blast
  apply (erule le_fun_cons_left_inv)
  (* need assoc/comm *)
  sorry

       
lemma le_trans_aux: fixes v2::val shows "\<lbrakk> n = size v2; v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  apply (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  apply (case_tac v2)
  apply (case_tac v1)
  apply (case_tac v3)
     apply force
    apply force
  apply force
  apply (case_tac v1)
  apply (case_tac v3)
    apply force
  apply force
  apply (case_tac v3)
   apply force
  apply clarify
    sorry
    
lemma le_append_fun_left[intro!]: fixes v1::val shows "VFun f1 \<sqsubseteq> VFun (f1@f2)"
  by (subgoal_tac "set f1 \<subseteq> set (f1@f2)") auto

lemma le_append_fun_right[intro!]: fixes v1::val shows "VFun f2 \<sqsubseteq> VFun (f1@f2)"
  by (subgoal_tac "set f2 \<subseteq> set (f1@f2)") auto
    
lemma le_join_left[intro!]: fixes v1::val shows "v1 \<squnion> v2 = Some v3 \<Longrightarrow> v1 \<sqsubseteq> v3"
  apply (case_tac v1) apply (case_tac v2) apply (case_tac v3) apply simp
     apply (case_tac "x1 = x1a") apply force apply force 
    apply simp apply (case_tac "x1 = x1a") apply force apply force 
   apply force 
  apply simp apply (case_tac v2) apply force apply auto 
  done
    
lemma le_join_right[intro!]: fixes v1::val shows "v1 \<squnion> v2 = Some v3 \<Longrightarrow> v2 \<sqsubseteq> v3"
  apply (case_tac v1) apply (case_tac v2) apply (case_tac v3) apply simp
     apply (case_tac "x1 = x1a") apply simp apply force 
    apply simp apply (case_tac "x1 = x1a") apply force apply force 
   apply force 
  apply simp apply (case_tac v2) apply force apply auto 
  done

lemma le_append_left[intro!]: "\<lbrakk> VFun f1 \<sqsubseteq> VFun v3; VFun f2 \<sqsubseteq> VFun v3 \<rbrakk> \<Longrightarrow> VFun (f1@f2) \<sqsubseteq> VFun v3"
  apply (induction f1 arbitrary: f2 v3)
   apply simp
  apply simp
  apply (rule le_cons_left)
   sorry
    
lemma le_left_join[intro!]: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" (* glb *)
  sorry
  


    
  
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
  
    
lemma inconsis_not_consis[simp]: "(v1 !~ v2) = (\<not> (v1 ~ v2))"
  sorry

(*    
proposition mon: fixes v1::val and v2::val
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'"
  shows "v1 \<squnion> v2 \<sqsubseteq> v1' \<squnion> v2'"
proof -
  have 3: "v1' \<sqsubseteq> v1' \<squnion> v2'" using le_join_left by blast
  have 4: "v2' \<sqsubseteq> v1' \<squnion> v2'" using le_join_right by blast
  have 5: "v1 \<sqsubseteq> v1' \<squnion> v2'" using 1 3 le_trans by blast
  have 6: "v2 \<sqsubseteq> v1' \<squnion> v2'" using 2 4 le_trans by blast
  show "v1 \<squnion> v2 \<sqsubseteq> v1' \<squnion> v2'" using 5 6 le_left_join by blast
qed
*)    

lemma le_join_right:
  fixes v::val shows "\<lbrakk> v \<sqsubseteq> v12; v = VFun f; v1 \<squnion> v2 = Some v12 \<rbrakk> 
  \<Longrightarrow> VFun f \<sqsubseteq> v1 \<or> VFun f \<sqsubseteq> v2"   
proof (induction v v12 arbitrary: f v1 v2 rule: val_le.induct)
  case (le_refl v)
  then show ?case apply simp apply (case_tac v1) apply (case_tac v2) apply simp
      apply (case_tac "x1 = x1a") apply force apply force apply force 
    apply (case_tac v1) apply force apply simp apply (case_tac v2) apply force
      apply simp sorry (* false! *)
next
  case (le_trans v1 v2 v3)
  then show ?case sorry
next
  case (le_join_left v1 v2 v3)
  then show ?case sorry
next
  case (le_join_right v1 v2 v3)
  then show ?case sorry
next
  case (le_left_join v1 v3 v2 v12)
  then show ?case sorry
next
  case (le_bot v v')
  then show ?case sorry
next
  case (le_fun v2 v1 v1' v2')
  then show ?case sorry
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
    show "\<forall>v v'. (v, v') \<in> set (f1 @ f2) \<longrightarrow> is_val v \<and> is_val v'" using vf1 vf2 by auto        
  qed    
  then show "is_val (VFun f1 \<squnion> VFun f2)" by simp
qed
    
  
end