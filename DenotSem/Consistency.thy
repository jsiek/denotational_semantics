theory Consistency
  imports LaurentValues
begin

section "Consistency"

fun consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 52) where
  "(VNat n) ~ (VNat m) = (n = m)" |
  "(v1\<mapsto>v1') ~ (VNat m) = False" |
  "(VNat n) ~ (v2\<mapsto>v2') = False" | 
  "(v1\<mapsto>v1') ~ (v2\<mapsto>v2') = ((v1 ~ v2 \<and> v1' ~ v2') \<or> \<not> (v1 ~ v2))" |
  "(VNat n) ~ (v2 \<squnion> v2') = (VNat n ~ v2 \<and> VNat n ~ v2')" |
  "(v1\<mapsto>v1') ~ (v2 \<squnion> v2') = ((v1\<mapsto>v1') ~ v2 \<and> (v1\<mapsto>v1') ~ v2')" |
  "(v1\<squnion>v1') ~ v2 = (v1 ~ v2 \<and> v1' ~ v2)" 
  
fun consis_env :: "val list \<Rightarrow> val list \<Rightarrow> bool" where
  "consis_env [] [] = True" |
  "consis_env [] (v'#\<rho>') = False" | 
  "consis_env (v#\<rho>) [] = False" |
  "consis_env (v#\<rho>) (v'#\<rho>') = (v ~ v' \<and> consis_env \<rho> \<rho>')"

fun is_val :: "val \<Rightarrow> bool" where
  "is_val (VNat n) = True" |
  "is_val (v \<mapsto> v') = (is_val v \<and> is_val v')" |
  "is_val (v1 \<squnion> v2) = (is_val v1 \<and> is_val v2 \<and> v1 ~ v2)"

definition val_env :: "val list \<Rightarrow> bool" where
  "val_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> is_val (\<rho>!k)"

definition env_le :: "val list \<Rightarrow> val list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "(\<rho>::val list) \<sqsubseteq> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k \<sqsubseteq> \<rho>'!k)" 
 
lemma consis_join_R[intro!]: "\<lbrakk> v1 ~ v2; v1 ~ v3 \<rbrakk> \<Longrightarrow> v1 ~ v2 \<squnion> v3"
  by (induction v1) auto

lemma consis_join_L[intro!]: "\<lbrakk> v1 ~ v3; v2 ~ v3 \<rbrakk> \<Longrightarrow> v1 \<squnion> v2 ~ v3"
  by auto  
  
lemma consis_join_L_inv[elim!]: "\<lbrakk> v1\<squnion>v2 ~ v; \<lbrakk> v1 ~ v; v2 ~ v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto

lemma consis_join_R_inv[elim!]: "\<lbrakk> v ~ v1\<squnion>v2; \<lbrakk> v ~ v1; v ~ v2 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induction v arbitrary: v1 v2) auto
     
lemma consis_sym_aux: "(v ~ v' \<longrightarrow> v' ~ v) \<and> (\<not> v ~ v' \<longrightarrow> \<not> v' ~ v)"
  by (induction v v' rule: consistent.induct) auto
    
lemma consis_sym[sym]: "v ~ v' \<Longrightarrow> v' ~ v"
  using consis_sym_aux by blast
    
lemma consis_refl[intro!]: "is_val v \<Longrightarrow> v ~ v"
  apply (induction v rule: is_val.induct) 
    apply force
   apply force
  apply simp apply clarify apply (rule conjI) apply blast 
  using consis_sym by blast

(*    
corollary consis_upper_bound: fixes v1::val and v2::val 
  assumes v1_v2: "v1 ~ v2" and v_v1: "is_val v1" and v_v2: "is_val v2"
  shows "\<exists> v3. v1 \<sqsubseteq> v3 \<and> v2 \<sqsubseteq> v3 \<and> is_val v3"
proof -
  obtain v12 where v12: "v1 \<squnion> v2 = Some v12" and v_v12: "is_val v12" 
    using v1_v2 v_v1 v_v2 consis_join_val by blast
  have 1: "v1 \<sqsubseteq> v12" using v12 le_join_left by blast
  have 2: "v2 \<sqsubseteq> v12" using v12 le_join_right by blast
  show ?thesis using 1 2 v_v12 by blast
qed

lemma upper_bound_consis: fixes v1::val and v2::val and v3::val 
  assumes v1_v3: "v1 \<sqsubseteq> v3" and v2_v3: "v2 \<sqsubseteq> v3" and v_v3: "is_val v3"
  shows "v1 ~ v2"
  using v_v3 v1_v3 v2_v3 apply (induction arbitrary: v1 v2 rule: is_val.induct)
   apply (case_tac v1) apply (case_tac v2) apply force apply force
   apply (case_tac v2) apply force apply force
  apply (case_tac v1) apply (case_tac v2) apply force apply force
  apply (case_tac v2) apply force
  apply simp
  apply (rule vfun_consis) apply (rule allI)+ apply (rule impI) apply (erule conjE)
  oops      
*)
    

  
lemma d_consis_nat_L: "\<lbrakk> \<Gamma> \<turnstile> c : v; \<Gamma> = [VNat n] \<rbrakk> \<Longrightarrow> v ~ VNat n"
  apply (induction \<Gamma> c v arbitrary: n rule: deduce_le.induct)
       apply (case_tac \<Gamma>1) apply force apply force
      apply (case_tac \<Gamma>1) apply force apply force
     apply force+
    apply (case_tac \<Gamma>1) apply force apply force
   apply force+
  done

lemma le_any_nat_consis: "v \<sqsubseteq> VNat n \<Longrightarrow> v ~ VNat n"
  unfolding le_val_def using d_consis_nat_L by auto

lemma consis_nat_atoms: "\<lbrakk> v ~ VNat n \<rbrakk> \<Longrightarrow> atoms v \<subseteq> { VNat n }"
  by (induction v arbitrary: n) auto
  
(*
lemma le_any_nat_atom_consis: "\<lbrakk> v \<sqsubseteq> VNat n \<rbrakk> \<Longrightarrow> atoms v \<subseteq> {VNat n}"
  using le_any_nat_inv_atoms by blast
*)

definition consis :: "val set \<Rightarrow> bool" where
  "consis \<Gamma> \<equiv> (\<forall>v v'. v \<in> \<Gamma> \<longrightarrow> v' \<in> \<Gamma> \<longrightarrow> v ~ v')"
  
lemma consis_atoms: "\<lbrakk> v1 ~ v2; v1' \<in> atoms v1; v2' \<in> atoms v2 \<rbrakk> \<Longrightarrow> v1' ~ v2'"
  apply (induction v1 v2 arbitrary: v1' v2' rule: consistent.induct)  
        apply force
       apply force
      apply force
     apply (metis atoms.simps(2) singletonD)
    apply force
   apply force
  apply force
  done
    
lemma val_consis_atoms: "is_val v \<Longrightarrow> consis (atoms v)"
  apply (induction v) apply auto
    apply (simp add: consis_def)
   apply (simp add: consis_def) apply blast
  apply (simp add: consis_def) apply clarify
  apply (rule conjI) apply clarify apply (erule_tac x=v in allE) apply (erule impE)
    apply blast using consis_atoms apply blast 
  apply clarify using consis_sym consis_atoms apply blast
  done
  
lemma consis_nat_trans: "\<lbrakk> v1 ~ VNat n; VNat n ~ v2 \<rbrakk> \<Longrightarrow> v1 ~ v2"
  by (induction v1) auto   

lemma consis_nat_trans2: "\<lbrakk> v1 ~ v2; v2 ~ VNat n \<rbrakk> \<Longrightarrow> v1 ~ VNat n"
  by (induction v2 arbitrary: v1 n) auto

definition vals :: "val set \<Rightarrow> bool" where
  "vals \<Gamma> \<equiv> (\<forall>v. v \<in> \<Gamma> \<longrightarrow> is_val v)"
  
lemma nat_atom_consis_nat: "\<lbrakk>  VNat n \<in> atoms v; is_val v \<rbrakk> \<Longrightarrow> v ~ VNat n"
  apply (induction v arbitrary: n)
    apply force
   apply force
  apply simp apply clarify apply (erule disjE) 
   apply (rule conjI) apply force
    apply (subgoal_tac "v1 ~ VNat n") prefer 2 apply blast 
  using consis_nat_trans2 consis_sym apply blast
  apply (rule conjI) 
   apply (subgoal_tac "v2 ~ VNat n") prefer 2 apply blast
  using consis_nat_trans2 apply blast
  apply blast
  done    
  
lemma le_nat_any_consis[intro!]: assumes n_v: "VNat n \<sqsubseteq> v" and v_v: "is_val v" 
  shows "v ~ VNat n"
proof -
  obtain c where "[v] \<turnstile> c : VNat n" using n_v unfolding le_val_def by blast
  then obtain v' where
    vp_v: "v' \<in> (\<Union>v\<in>set [v]. atoms v)" and vp_n: "v' = VNat n"
    using d_nat_inv by presburger
  have "VNat n \<in> atoms v" using vp_v vp_n by simp
  with v_v show "v ~ VNat n" using nat_atom_consis_nat by blast
qed
  
    
    

lemma consis_le_inconsis_le:
  "(v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1 \<sqsubseteq> v1' \<and> v2 \<sqsubseteq> v2' \<longrightarrow> v1 ~ v2))
  \<and> (\<not> v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1' \<sqsubseteq> v1 \<and> v2' \<sqsubseteq> v2 \<longrightarrow> \<not> v1 ~ v2))"
proof (induction v1' v2' rule: consistent.induct)
  case (1 n m)
  then show ?case apply auto
    apply (subgoal_tac "v1 ~ VNat n") prefer 2 apply blast
    apply (subgoal_tac "v2 ~ VNat n") prefer 2 apply blast
    using consis_nat_trans consis_sym_aux apply blast
    apply (subgoal_tac "v1 ~ VNat n") prefer 2 apply blast
    apply (subgoal_tac "v2 ~ VNat n") prefer 2 apply blast
    done
next
  case (2 v1 v1' m)
  then show ?case sorry
next
  case (3 n v2 v2')
  then show ?case sorry
next
  case (4 v1 v1' v2 v2')
  then show ?case sorry
next
  case (5 n v2 v2')
  then show ?case sorry
next
  case (6 v1 v1' v2 v2')
  then show ?case sorry
next
  case (7 v1 v1' v2)
  then show ?case sorry
qed


    (*
  apply (induction rule: consistent_inconsistent.induct)
  apply blast
  defer
  apply blast
  defer
  apply blast
  apply blast

  apply (rule allI)+
  apply (rule impI) apply (erule conjE)
  apply (case_tac v1) apply force
  apply (case_tac v2) apply force
  apply simp apply (rule vfun_consis)
  apply (rule allI)+ apply (rule impI) apply (erule conjE)

  apply (erule le_fun_fun_inv)+
   apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f1 \<and> u \<sqsubseteq> v1a \<and> v1' \<sqsubseteq> u'")
   prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
   apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f2 \<and> u \<sqsubseteq> v2a \<and> v2' \<sqsubseteq> u'")
   prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption

   apply (erule exE)+
   apply (erule conjE)+
    
   apply (erule_tac x=u in allE)    
   apply (erule_tac x=u' in allE)    
   apply (erule_tac x=ua in allE)    
   apply (erule_tac x=u'a in allE)    

  apply (erule impE) apply force
  apply (erule disjE)
    apply force
  apply (rule disjI2)
    apply force 
    
  apply (rule allI)+
  apply (rule impI) apply (erule conjE)
  apply (case_tac v1a) apply force 
  apply (case_tac v2a) apply force
  apply clarify
  
  apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f2a \<and> u \<sqsubseteq> v1 \<and> v1' \<sqsubseteq> u'")
  prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
  apply (subgoal_tac "\<exists> v v'. (v,v') \<in> set f2b \<and> v \<sqsubseteq> v2 \<and> v2' \<sqsubseteq> v'")
  prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
  apply (erule exE)+ apply (erule conjE)+
  apply (rule vfun_inconsis) apply assumption apply assumption
  apply auto   
  done
*)

(*    
lemma consis_le: "\<lbrakk> v1 \<sqsubseteq> v1'; v2 \<sqsubseteq> v2'; v1' ~ v2' \<rbrakk> \<Longrightarrow> v1 ~ v2"
  using consis_le_inconsis_le by blast

lemma inconsis_le: "\<lbrakk> v1' \<sqsubseteq> v1; v2' \<sqsubseteq> v2; v1' !~ v2' \<rbrakk> \<Longrightarrow> v1 !~ v2"
  using consis_le_inconsis_le by blast
*)
    
lemma lookup_consis[intro]: "\<lbrakk> consis_env \<rho> \<rho>'; x < length \<rho> \<rbrakk>
  \<Longrightarrow> (\<rho>!x) ~ (\<rho>'!x)"
  apply (induction arbitrary: x rule: consis_env.induct)
   apply force
  apply (case_tac x) apply force apply auto
  done

lemma cons_val_env_inv[elim!]:
  "\<lbrakk> val_env (v#\<rho>); \<lbrakk> is_val v; val_env \<rho> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    unfolding val_env_def by fastforce

lemma ext_val_env[intro!]: "\<lbrakk> is_val v; val_env \<rho> \<rbrakk> \<Longrightarrow> val_env (v#\<rho>)"
  unfolding val_env_def apply auto apply (case_tac k) apply auto done
      
lemma consis_env_join: fixes \<rho>1::"val list" assumes r1_r2: "consis_env \<rho>1 \<rho>2" 
  and v_r1: "val_env \<rho>1" and v_r2: "val_env \<rho>2"
  shows "\<exists> \<rho>3. \<rho>1 \<squnion> \<rho>2 = Some \<rho>3 \<and> val_env \<rho>3"
  using r1_r2 v_r1 v_r2 apply (induction rule: consis_env.induct)
   apply (rule_tac x="[]" in exI) apply force
   apply (erule cons_val_env_inv)
  apply (erule cons_val_env_inv)
   apply (subgoal_tac "\<exists>\<rho>3. \<rho> \<squnion> \<rho>' = Some \<rho>3 \<and> val_env \<rho>3") prefer 2 apply blast
  apply (subgoal_tac "\<exists> v3. v \<squnion> v' = Some v3 \<and> is_val v3")
    prefer 2 using consis_join_val apply blast
  apply (erule exE)+ apply (erule conjE)+
  apply (rule_tac x="v3#\<rho>3" in exI) 
  apply (rule conjI) apply fastforce
  apply blast
  done
    
lemma consis_env_length: "consis_env \<rho> \<rho>' \<Longrightarrow> length \<rho> = length \<rho>'"
  apply (induction rule: consis_env.induct) apply auto done

lemma join_env_length: "\<lbrakk> consis_env \<rho>1 \<rho>2; \<rho>1 \<squnion> \<rho>2 = Some \<rho>3  \<rbrakk> \<Longrightarrow> length \<rho>3 = length \<rho>1"
  apply (induction arbitrary: \<rho>3 rule: consis_env.induct)
   apply fastforce
  apply simp
  apply (case_tac "v \<squnion> v'") apply auto
  apply (case_tac "\<rho> \<squnion> \<rho>'") apply auto
  done
*)
     
end
