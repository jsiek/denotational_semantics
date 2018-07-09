theory Consistency
  imports LaurentValues
begin

section "Consistency"

inductive consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 52) and
    inconsistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "!~" 52) where
  vnat_consis[intro!]: "(VNat n) ~ (VNat n)" |
  vfun_consis[intro!]: "\<lbrakk> (v1 ~ v2 \<and> v1' ~ v2') \<or> v1 !~ v2 \<rbrakk> \<Longrightarrow> (v1 ) ~ (VFun f2)" |
  vnat_inconsis[intro!]: "n \<noteq> n' \<Longrightarrow> (VNat n) !~ (VNat n')" |
  vfun_inconsis[intro!]: "\<lbrakk> (v1, v1') \<in> set f1; (v2, v2') \<in> set f2; v1 ~ v2; v1' !~ v2' \<rbrakk> 
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

definition env_le :: "val list \<Rightarrow> val list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "(\<rho>::val list) \<sqsubseteq> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k \<sqsubseteq> \<rho>'!k)" 
    
lemma consis_and_not_consis: "(v ~ v' \<longrightarrow> \<not> (v !~ v')) \<and> (v !~ v' \<longrightarrow> \<not>(v ~ v'))"
  by (induction rule: consistent_inconsistent.induct) blast+ 
        
lemma consis_or_not_aux: "\<forall> v v'. n = vsize v \<longrightarrow> v ~ v' \<or> v !~ v'"
 apply (induction n rule: nat_less_induct)
 apply (rule allI)+ apply (rule impI)
 apply (case_tac v)    
  apply (case_tac v')
    apply force
   apply force
  apply (case_tac v')
   apply force
  apply simp
  apply auto
    apply (metis add_lessD1 less_SucI size_fun_mem)
    apply (metis add_lessD1 less_SucI size_fun_mem)
    apply (metis add_lessD1 less_SucI size_fun_mem)
  by (metis add.commute add_lessD1 less_SucI size_fun_mem)    
    
lemma consis_or_not: "v ~ v' \<or> v !~ v'"
  using consis_or_not_aux by blast
  
lemma inconsis_not_consis[simp]: "(v1 !~ v2) = (\<not> (v1 ~ v2))"
  using consis_and_not_consis consis_or_not by blast
  
lemma consis_refl[intro!]: "is_val v \<Longrightarrow> v ~ v"
  apply (induction rule: is_val.induct)
  apply blast
  apply (simp only: is_fun_def)
  done

lemma consis_inconsis_sym: "(v ~ v' \<longrightarrow> v' ~ v) \<and> (v !~ v' \<longrightarrow> \<not>(v' ~ v))"
  apply (induction rule: consistent_inconsistent.induct) 
  apply blast
  using consis_or_not apply blast
  apply blast    
  using consis_and_not_consis apply blast
  apply blast    
  apply blast    
  done
    
lemma consis_sym[sym]: "v ~ v' \<Longrightarrow> v' ~ v"
  using consis_inconsis_sym by blast

lemma consis_join_val:
  assumes v1_v2: "v1 ~ v2" and v_v1: "is_val v1" and v_v2: "is_val v2"
  shows "\<exists> v12. (v1 \<squnion> v2) = Some v12 \<and> is_val v12"
proof (cases v1)
  case (VNat n1) then have v1: "v1 = VNat n1" .
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    show ?thesis using v1 VNat v1_v2 by auto
  next
    case (VFun f2)
    have "False" using v1_v2 v1 VFun by auto 
    then show ?thesis ..
  qed
next
  case (VFun f1) then have v1: "v1 = VFun f1" .
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    show ?thesis using v1 VNat v1_v2 by auto
  next
    case (VFun f2)
    let ?v12 = "VFun (f1@f2)"
    have j12: "v1 \<squnion> v2 = Some ?v12" using v1 VFun by simp
    have v_v12: "is_val ?v12"
      apply (rule vfun_is_val)
       apply (simp only: is_fun_def)
       apply (rule vfun_consis) 
       apply (metis (mono_tags, lifting) Un_iff VFun consis_refl consis_sym set_append v1 v1_v2 v_v1 v_v2 vfun_consis_inv)
      using v_v1 v_v2 using VFun v1 apply auto
      done
    show ?thesis using j12 v_v12 by blast
  qed
qed

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

lemma consis_le_inconsis_le:
  "(v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1 \<sqsubseteq> v1' \<and> v2 \<sqsubseteq> v2' \<longrightarrow> v1 ~ v2))
  \<and> (v1' !~ v2' \<longrightarrow> (\<forall> v1 v2. v1' \<sqsubseteq> v1 \<and> v2' \<sqsubseteq> v2 \<longrightarrow> v1 !~ v2))"
proof (induction rule: consistent_inconsistent.induct)
  case (vnat_consis n)
  then show ?case by blast
next
  case (vfun_consis f1 f2)
  show ?case 
  proof clarify
    fix v1 v2 assume v1_f1: "v1 \<sqsubseteq> VFun f1" and v2_f2: "v2 \<sqsubseteq> VFun f2"
    show "v1 ~ v2" sorry
  qed
next
  case (vnat_inconsis n n')
  then show ?case by blast
next
  case (vfun_inconsis v1 v1' f1 v2 v2' f2)
  then show ?case sorry
next
  case (vnat_vfun_inconsis n f)
  then show ?case apply clarify apply (erule le_fun_any_inv) apply blast done
next
  case (vfun_vnat_inconsis f n)
  then show ?case apply clarify apply (erule le_fun_any_inv) apply blast done
oops

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

end
