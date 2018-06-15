theory Consistency
  imports Values
begin
  
abbreviation consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 53) where
  "v1 ~ v2 \<equiv> (\<exists> v3. v1 \<squnion> v2 = Some v3)"
abbreviation is_fun :: "func \<Rightarrow> bool" where
  "is_fun f \<equiv>  \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f \<and> (v2,v2') \<in> set f \<and> v1 ~ v2 \<longrightarrow> v1' ~ v2'"

inductive is_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v';
                          is_fun f \<rbrakk>
                        \<Longrightarrow> is_val (VFun f)"
inductive_cases
  v_fun_inv[elim!]: "is_val (VFun f)"

abbreviation has_vals :: "func \<Rightarrow> bool" where
  "has_vals f \<equiv> \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v'"

abbreviation consis_list :: "val list \<Rightarrow> bool" where
  "consis_list L \<equiv> \<forall> v1 v2. v1 \<in> set L \<longrightarrow> v2 \<in> set L \<longrightarrow> v1 ~ v2"

lemma consis_upper_bound: fixes v1::val and v2::val and v3::val
  assumes v12: "v1 ~ v2" and v13: "v1 ~ v3" and v23: "v2 \<squnion> v3 = Some v23"
  shows "v1 ~ v23"
  using v12 v13 v23
  apply (case_tac v1) apply (case_tac v2) apply (case_tac v3) apply simp apply clarify
     apply (case_tac "x1a = x1b") apply force apply force apply force apply force
  apply (case_tac v2) apply force apply (case_tac v3) apply force apply simp
  apply (erule exE)+ apply (case_tac "x2a = x2b") apply simp
   apply (case_tac "x2 = x2b") apply force apply force
  apply simp apply (case_tac "x2= x2b") apply force apply force
  done

lemma consis_join_list: assumes cl: "consis_list L" and vl: "\<forall> v'. v' \<in> set L \<longrightarrow> v ~ v'" 
   and ls: "\<Squnion>L = Some Ls"
  shows "v ~ Ls"  
  using cl vl ls apply (induction L arbitrary: Ls)
   apply force
  apply simp apply (case_tac "L") apply force
  apply simp apply (case_tac "\<Squnion> (aa # list)") apply force apply simp
  apply (rule consis_upper_bound) prefer 3 apply assumption
  apply auto
  done   
 
lemma upper_bound_consis_list:
  assumes cl: "consis_list L" and ll: "0 < length L" shows "\<exists> Ls. \<Squnion>L = Some Ls"
  using cl ll apply (induction L)
   apply force
  apply simp
  apply (case_tac L)
  apply force
  apply simp
  apply (erule exE)
  apply simp
  apply (rule consis_join_list) prefer 3 apply assumption
   apply auto
  done
  
lemma le_consis: "v1 \<sqsubseteq> v2 \<Longrightarrow> v1 ~ v2"
  using le_join by blast

lemma vsize_join: "v1 \<squnion> v2 = Some v3 \<Longrightarrow> vsize v3 \<le> vsize v1 + vsize v2"
  apply (case_tac v1)
   apply (case_tac v2)
  apply auto apply (case_tac "x1 = x1a") apply auto
  apply (case_tac v2) apply auto
  apply (case_tac "x2 = x2a") apply auto
  done
        
lemma consis_refl[intro!]: "is_val v \<Longrightarrow> v ~ v"
  by (cases v) auto

lemma consis_sym[sym]: "v1 ~ v2 \<Longrightarrow> v2 ~ v1"
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1=x1a") apply auto
  apply (case_tac v2) apply force apply simp
  done     
    
lemma is_val_le_aux2:
  "\<forall> v. n = vsize v \<longrightarrow> (is_val v \<longrightarrow> (\<forall> v'. v' \<sqsubseteq> v \<longrightarrow> is_val v'))"
  apply (induction n rule: nat_less_induct)
  apply clarify 
   apply (case_tac v)
  apply force
   apply simp
   apply clarify
   apply (case_tac v') apply force apply simp
  apply clarify    
    oops
  

lemma is_val_le_aux: "(is_val v \<longrightarrow> (\<forall> v'. v' \<sqsubseteq> v \<longrightarrow> is_val v'))
                    \<and> (not_val v \<longrightarrow>  (\<forall> v'. v \<sqsubseteq> v' \<longrightarrow> not_val v'))"
(*
  apply (induction v rule: is_val_not_val.induct)
  apply force
  defer
     apply clarify apply (case_tac v'a) apply force apply clarify 
    apply (rule vfun_not_val1) apply simp
*)
  oops (* need beta sound *)    

lemma is_val_le: "\<lbrakk> is_val v; v' \<sqsubseteq> v \<rbrakk> \<Longrightarrow> is_val v'" 
  (*using is_val_le_aux by blast*)
  oops

lemma upper_bound_consis: fixes v1::val and v2::val and v3::val 
  assumes v1_v3: "v1 \<sqsubseteq> v3" and v2_v3: "v2 \<sqsubseteq> v3" and 
    v_v1: "is_val v1" and v_v2: "is_val v2" and v_v3: "is_val v3"
  shows "v1 ~ v2"
    oops
(*
proof -
  obtain v12 where v12: "v1 \<squnion> v2 = Some v12"
    using v1_v3 v2_v3 apply (case_tac v1) apply auto apply (case_tac v2) apply auto
      apply (case_tac v3) apply auto apply (case_tac "x2=x2a") apply auto done
  have v12_v3: "v12 \<sqsubseteq> v3" using v12 v1_v3 v2_v3 using le_left_join by blast
  then have v_v12: "is_val v12" using is_val_le v_v3 by blast
  show ?thesis using v12 v_v12 by blast
qed
*)
      
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