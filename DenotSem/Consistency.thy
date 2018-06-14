theory Consistency
  imports Values
begin
  
inductive is_val :: "val \<Rightarrow> bool" and not_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v';
                          \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f \<and> (v2,v2') \<in> set f \<longrightarrow>
                            ((\<exists> v3. v1 \<squnion> v2 = Some v3 \<and> is_val v3) 
                                \<and> (\<exists> v3'. v1' \<squnion> v2' = Some v3' \<and> is_val v3')) 
                            \<or> (\<forall> v3. \<not>(v1 \<squnion> v2 = Some v3) \<or> not_val v3) \<rbrakk>
                        \<Longrightarrow> is_val (VFun f)" |
  vfun_not_val1: "\<lbrakk> (v,v') \<in> set f; not_val v \<rbrakk> \<Longrightarrow> not_val (VFun f)" |
  vfun_not_val2: "\<lbrakk> (v,v') \<in> set f; not_val v' \<rbrakk> \<Longrightarrow> not_val (VFun f)" |
  vfun_not_val3: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f;
                    v1 \<squnion> v2 = Some v3; is_val v3;
                    (\<forall> v3'. \<not>(v1' \<squnion> v2' = Some v3') \<or> not_val v3') \<rbrakk> \<Longrightarrow> not_val (VFun f)"

inductive_cases
  v_fun_inv: "is_val (VFun f)" and
  nv_nat_inv[elim!]: "not_val (VNat n)" and
  nv_fun_inv: "not_val (VFun f)"

abbreviation consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 53) where
  "v1 ~ v2 \<equiv> (\<exists> v3. v1 \<squnion> v2 = Some v3 \<and> is_val v3)"
abbreviation is_fun :: "func \<Rightarrow> bool" where
  "is_fun f \<equiv>  \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f \<and> (v2,v2') \<in> set f \<and> v1 ~ v2 \<longrightarrow> v1' ~ v2'"
abbreviation has_vals :: "func \<Rightarrow> bool" where
  "has_vals f \<equiv> \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v'"

lemma is_val_and_not_val: "(is_val v \<longrightarrow> \<not> (not_val v)) \<and> (not_val v \<longrightarrow> \<not> is_val v)"
  apply (induction rule: is_val_not_val.induct)
  apply blast
  apply (rule notI) apply (erule nv_fun_inv) apply force apply force apply blast
  using v_fun_inv apply blast
  using v_fun_inv apply blast
  using v_fun_inv apply blast 
  done

lemma consis_join_val:
  assumes v1_v2: "v1 ~ v2" and v_v1: "is_val v1" and v_v2: "is_val v2"
  shows "\<exists> v12. (v1 \<squnion> v2) = Some v12 \<and> is_val v12"
  using v1_v2 v_v1 v_v2 by auto

lemma vsize_join: "v1 \<squnion> v2 = Some v3 \<Longrightarrow> vsize v3 \<le> vsize v1 + vsize v2"
  apply (case_tac v1)
   apply (case_tac v2)
  apply auto apply (case_tac "x1 = x1a") apply auto
  apply (case_tac v2) apply auto
  apply (case_tac "x2 = x2a") apply auto
  done
    
lemma is_val_or_not_aux: "\<forall> v. n = vsize v \<longrightarrow> is_val v \<or> not_val v"
  apply (induction n rule: nat_less_induct)
  apply (rule allI) apply (rule impI)
  apply (case_tac v)
   apply fastforce
  apply simp apply clarify
  apply (rule vfun_is_val)
   apply (rule allI)+ apply (rule impI)
   apply (subgoal_tac "is_val va \<or> not_val va") prefer 2 
    apply (metis add_lessD1 less_SucI size_fun_mem)
   apply (subgoal_tac "is_val v' \<or> not_val v'") prefer 2 
    apply (subgoal_tac "vsize v' < Suc (fsize x2)") prefer 2 
     apply (meson dual_order.strict_trans not_add_less2 not_less_eq size_fun_mem)      
    apply blast
  using vfun_not_val1 vfun_not_val2 apply auto[1]
  apply (rule allI)+ apply (rule impI)+ apply (erule conjE)+
  apply (case_tac "v1 ~ v2") apply (rule disjI1)
   apply simp
   apply (rule classical)
   apply (subgoal_tac "not_val (VFun x2)") apply blast
   apply (erule exE) apply (erule conjE)+        
   apply (rule vfun_not_val3)
       prefer 3 apply assumption
      apply assumption apply assumption apply assumption
   apply clarify
   apply (subgoal_tac "vsize v3' < Suc (fsize x2)")
    apply (subgoal_tac "is_val v3' \<or> not_val v3'")
     apply (erule disjE) apply blast apply blast
    apply blast
   apply (simp add: size_fun_mem_join)
  apply (rule disjI2)
  apply (rule allI)
  apply clarify
  apply (subgoal_tac "vsize v3 < Suc (fsize x2)")
   apply (subgoal_tac "is_val v3 \<or> not_val v3")
    apply (erule disjE) apply blast apply blast
   apply blast
  apply (rule size_fun_mem_join_fst) prefer 3 apply assumption
   apply auto
  done

lemma is_val_or_not: "is_val v \<or> not_val v" 
  using is_val_or_not_aux by blast

lemma not_val_is_val[simp]: "not_val v = (\<not> is_val v)"
  using is_val_and_not_val is_val_or_not by blast    
  
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
    
lemma consis_refl[intro!]: "is_val v \<Longrightarrow> v ~ v"
  by (cases v) auto

lemma consis_sym[sym]: "v1 ~ v2 \<Longrightarrow> v2 ~ v1"
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1=x1a") apply auto
  apply (case_tac v2) apply force apply simp
  apply (case_tac "x2=x2a") apply force
  apply simp
  apply clarify
  apply (rule is_fun_intro)
  apply (subgoal_tac "set (x2@x2a) = set (x2a @ x2)") prefer 2 apply force apply blast
  apply (subgoal_tac "set (x2@x2a) = set (x2a @ x2)") prefer 2 apply force apply blast
  done     
    
lemma is_val_le_aux2:
  "\<forall> v. n = vsize v \<longrightarrow> (is_val v \<longrightarrow> (\<forall> v'. v' \<sqsubseteq> v \<longrightarrow> is_val v'))
    \<and> (not_val v \<longrightarrow>  (\<forall> v'. v \<sqsubseteq> v' \<longrightarrow> not_val v'))"
  apply (induction n rule: nat_less_induct)
  apply clarify apply (rule conjI) apply clarify
   apply (case_tac v)
  apply force
   apply simp
   apply clarify
   apply (case_tac v') apply force apply simp
   apply (rule is_fun_intro)
    apply clarify
    sorry
  

lemma is_val_le_aux: "(is_val v \<longrightarrow> (\<forall> v'. v' \<sqsubseteq> v \<longrightarrow> is_val v'))
                    \<and> (not_val v \<longrightarrow>  (\<forall> v'. v \<sqsubseteq> v' \<longrightarrow> not_val v'))"
  apply (induction v rule: is_val_not_val.induct)
  apply force
  defer
     apply clarify apply (case_tac v'a) apply force apply clarify 
    apply (rule vfun_not_val1) apply simp
  sorry (* need beta sound *)    

lemma is_val_le: "\<lbrakk> is_val v; v' \<sqsubseteq> v \<rbrakk> \<Longrightarrow> is_val v'" 
  using is_val_le_aux by blast

lemma upper_bound_consis: fixes v1::val and v2::val and v3::val 
  assumes v1_v3: "v1 \<sqsubseteq> v3" and v2_v3: "v2 \<sqsubseteq> v3" and 
    v_v1: "is_val v1" and v_v2: "is_val v2" and v_v3: "is_val v3"
  shows "v1 ~ v2"
proof -
  obtain v12 where v12: "v1 \<squnion> v2 = Some v12"
    using v1_v3 v2_v3 apply (case_tac v1) apply auto apply (case_tac v2) apply auto
      apply (case_tac v3) apply auto apply (case_tac "x2=x2a") apply auto done
  have v12_v3: "v12 \<sqsubseteq> v3" using v12 v1_v3 v2_v3 using le_left_join by blast
  then have v_v12: "is_val v12" using is_val_le v_v3 by blast
  show ?thesis using v12 v_v12 by blast
qed
    
lemma consis_le: assumes v1p_v2p: "v1' ~ v2'" and v1_v1p: "v1 \<sqsubseteq> v1'" and v2_v2p: "v2 \<sqsubseteq> v2'"
  shows "v1 ~ v2"
  oops
    
lemma inconsis_le: assumes v1p_v2p: "\<not>(v1' ~ v2')" and v1_v1p: "v1' \<sqsubseteq> v1" and v2_v2p: "v2' \<sqsubseteq> v2"
  shows "\<not>(v1 ~ v2)"
  oops
    
lemma le_consis: "\<lbrakk> v1 \<sqsubseteq> v2; is_val v1; is_val v2 \<rbrakk> \<Longrightarrow> v1 ~ v2"
  apply (induction rule: val_le.induct)
  apply (rule consis_refl) apply blast
  oops    
    
end