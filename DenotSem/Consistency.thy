theory Consistency
  imports Values
begin
  
inductive is_val :: "val \<Rightarrow> bool" and not_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v';
                          \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f \<and> (v2,v2') \<in> set f \<longrightarrow>
                            ((\<exists> v3. v1 \<sqsubseteq> v3 \<and> v2 \<sqsubseteq> v3 \<and> is_val v3) 
                                \<and> (\<exists> v3'. v1' \<sqsubseteq> v3' \<and> v2' \<sqsubseteq> v3' \<and> is_val v3')) 
                            \<or> (\<forall> v3. \<not>(v1 \<sqsubseteq> v3) \<or> \<not>(v2 \<sqsubseteq> v3) \<or> not_val v3) \<rbrakk>
                        \<Longrightarrow> is_val (VFun f)" |
  vfun_not_val1: "\<lbrakk> (v,v') \<in> set f; not_val v \<rbrakk> \<Longrightarrow> not_val (VFun f)" |
  vfun_not_val2: "\<lbrakk> (v,v') \<in> set f; not_val v' \<rbrakk> \<Longrightarrow> not_val (VFun f)" |
  vfun_not_val3: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f;
                    v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; is_val v3;
                    (\<forall> v3'. \<not>(v1' \<sqsubseteq> v3') \<or> \<not>(v2' \<sqsubseteq> v3') \<or> not_val v3') \<rbrakk> \<Longrightarrow> not_val (VFun f)"

inductive_cases
  v_fun_inv: "is_val (VFun f)" and
  nv_nat_inv[elim!]: "not_val (VNat n)" and
  nv_fun_inv: "not_val (VFun f)"

lemma is_val_and_not_val: "(is_val v \<longrightarrow> \<not> (not_val v)) \<and> (not_val v \<longrightarrow> \<not> is_val v)"
  apply (induction rule: is_val_not_val.induct)
  apply blast
  apply (rule notI) apply (erule nv_fun_inv) apply force apply force apply blast
  using v_fun_inv apply blast
  using v_fun_inv apply blast
  using v_fun_inv apply blast 
  done

lemma is_val_or_not: "is_val v \<or> not_val v" sorry

lemma not_val_is_val[simp]: "not_val v = (\<not> is_val v)"
  using is_val_and_not_val is_val_or_not by blast
    
abbreviation consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 53) where
  "v1 ~ v2 \<equiv> (\<exists> v3. v1 \<sqsubseteq> v3 \<and> v2 \<sqsubseteq> v3 \<and> is_val v3)"

abbreviation is_fun :: "func \<Rightarrow> bool" where
  "is_fun f \<equiv>  \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f \<and> (v2,v2') \<in> set f \<and> v1 ~ v2 \<longrightarrow> v1' ~ v2'"
    
abbreviation has_vals :: "func \<Rightarrow> bool" where
  "has_vals f \<equiv> \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v'"
  
lemma is_fun_intro[intro!]: "\<lbrakk> is_fun f; \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v' \<rbrakk>
       \<Longrightarrow> is_val (VFun f)" 
  apply auto apply blast done
  
lemma is_val_fun: "is_val (VFun f) \<Longrightarrow> is_fun f"
  apply (erule v_fun_inv)
  apply clarify
  apply simp 
  apply blast
  done
    
lemma is_val_fun_elim[elim!]: "\<lbrakk> is_val (VFun f); \<lbrakk> is_fun f; has_vals f\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (smt is_val_fun v_fun_inv)
    
lemma consis_le: assumes v1p_v2p: "v1' ~ v2'" and v1_v1p: "v1 \<sqsubseteq> v1'" and v2_v2p: "v2 \<sqsubseteq> v2'"
  shows "v1 ~ v2"
  using v1_v1p v1p_v2p v2_v2p val_le.le_trans by blast

lemma inconsis_le: assumes v1p_v2p: "\<not>(v1' ~ v2')" and v1_v1p: "v1' \<sqsubseteq> v1" and v2_v2p: "v2' \<sqsubseteq> v2"
  shows "\<not>(v1 ~ v2)"
  using v1_v1p v1p_v2p v2_v2p val_le.le_trans by blast

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
      using v_v1 v_v2 
      apply (metis Un_iff VFun is_val.simps set_append v1 val.inject(2) val.simps(4))
      apply (rule allI)+ apply (rule impI) apply (erule conjE)+
      apply simp apply (erule disjE) apply (erule disjE)
      using v1 v_v1 apply blast
      using v1_v2 v1 VFun apply simp apply (erule exE) apply (erule conjE)+
       apply (case_tac v3) apply force apply simp
       apply (case_tac "v1a ~ v2a")
        apply (rule disjI1) apply simp
        apply (erule exE) apply (erule conjE)+
        apply (subgoal_tac "\<exists> Bs. \<Squnion> (map snd [(A2, B2)\<leftarrow>x2 . A2 \<sqsubseteq> v3a]) = Some Bs")        
          apply (erule exE)+
       apply (subgoal_tac "v3a \<mapsto> v1' \<sqsubseteq> VFun x2") prefer 2
              apply (subgoal_tac "v1a \<mapsto> v1' \<sqsubseteq> VFun x2") prefer 2 
          using le_fun_elt val_le.le_trans apply blast
          using le_trans apply blast
       apply (subgoal_tac "v3a \<mapsto> v2' \<sqsubseteq> VFun x2") prefer 2
                  apply (subgoal_tac "v2a \<mapsto> v2' \<sqsubseteq> VFun x2") prefer 2 
          using le_fun_elt val_le.le_trans apply blast
          using le_trans apply blast                
        apply (subgoal_tac "v1' \<sqsubseteq> Bs") prefer 2 apply (rule beta_sound) apply blast
              apply blast
        apply (subgoal_tac "v2' \<sqsubseteq> Bs") prefer 2 apply (rule beta_sound) apply blast apply blast
         apply (rule_tac x=Bs in exI) apply simp
             defer
          defer
             apply force
         apply (erule disjE)
          using v1 VFun v1_v2 apply simp 
             apply (erule exE) apply (erule conjE)+
            apply (case_tac v3) apply force
       apply (case_tac "v1a ~ v2a")
        apply (rule disjI1) apply simp
              apply (erule exE) apply (erule conjE)+          
        apply (subgoal_tac "\<exists> Bs. \<Squnion> (map snd [(A2, B2)\<leftarrow>x2 . A2 \<sqsubseteq> v3a]) = Some Bs")        
          apply (erule exE)+
       apply (subgoal_tac "v3a \<mapsto> v1' \<sqsubseteq> VFun x2") prefer 2
              apply (subgoal_tac "v1a \<mapsto> v1' \<sqsubseteq> VFun x2") prefer 2 
          using le_fun_elt val_le.le_trans apply blast
          using le_trans apply blast
       apply (subgoal_tac "v3a \<mapsto> v2' \<sqsubseteq> VFun x2") prefer 2
                  apply (subgoal_tac "v2a \<mapsto> v2' \<sqsubseteq> VFun x2") prefer 2 
          using le_fun_elt val_le.le_trans apply blast
          using le_trans apply blast                
        apply (subgoal_tac "v1' \<sqsubseteq> Bs") prefer 2 apply (rule beta_sound) apply blast
              apply blast
        apply (subgoal_tac "v2' \<sqsubseteq> Bs") prefer 2 apply (rule beta_sound) apply blast apply blast
         apply (rule_tac x=Bs in exI) apply simp
               defer defer
               apply force
         using v1 v_v1 
         apply (smt VFun is_val_fun v_v2)
         sorry
    show ?thesis using j12 v_v12 by blast
  qed
qed    
    
end