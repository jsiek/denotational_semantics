theory DenotAlt
  imports Denot Deterministic
begin

definition lamD :: "(ty \<Rightarrow> ty set) \<Rightarrow> ty set" where
  "lamD G = { f. wf_ty f \<and> fun_pred f \<and> (\<forall> v v'. (v,v') |\<in>| entries f \<longrightarrow>
                                           (\<exists>v''. v'' \<in> G v \<and> v'' <: v')) }"
  
fun D :: "exp \<Rightarrow> ty list \<Rightarrow> ty set" where
  Enat: "D (ENat n) \<rho> = {TNat n}" |
  Evar: "D (EVar k) \<rho> = (if k < length \<rho> then {\<rho>!k} else {})" |
  Elam: "D (ELam e) \<rho> = { f. wf_ty f \<and> fun_pred f \<and> (\<forall> v v'. (v,v') |\<in>| entries f \<longrightarrow>
   (\<exists>v''. v'' \<in> D e (v#\<rho>) \<and> v'' <: v')) }" |
  Eapp: "D (EApp e1 e2) \<rho> = { v'. \<exists> f v. f \<in> D e1 \<rho> \<and> v \<in> D e2 \<rho> \<and> v' \<in> f \<bullet> v }" | 
  Eprim: "D (EPrim f e1 e2) \<rho> = { v. \<exists> v1 v2 n1 n2. v1 \<in> D e1 \<rho> 
          \<and> v2 \<in> D e2 \<rho> \<and> v1 <: TNat n1 \<and> v2 <: TNat n2 \<and> TNat (f n1 n2) <: v \<and> wf_ty v }" |
  Eif: "D (EIf e1 e2 e3) \<rho> = { v. \<exists> v1 n. v1 \<in> D e1 \<rho> \<and> v1 <: TNat n
         \<and> (n = 0 \<longrightarrow> v \<in> D e3 \<rho>) \<and> (n \<noteq> 0 \<longrightarrow> v \<in> D e2 \<rho>) }"
declare Elam[simp del]
  
lemma lambda_lamD[simp]: "D (ELam e) \<rho> = lamD (\<lambda>v. D e (v # \<rho>))"
  unfolding lamD_def using Elam by blast
    
lemma f_lam: "fun_pred f \<Longrightarrow> F f e \<rho> = (\<forall> v v'. (v,v') |\<in>| entries f \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk> (v#\<rho>))"
  by (induction f) auto

lemma f_fun_pred: "F f e \<rho> \<Longrightarrow> fun_pred f"
  by (induction f) auto

lemma wf_entries: "\<lbrakk> wf_ty A; (v,v') |\<in>| entries A \<rbrakk> \<Longrightarrow> wf_ty v \<and> wf_ty v'"
  apply (induction A arbitrary: v v') apply force apply force apply force done

lemma extend_wf_env: "\<lbrakk> wf_env \<rho>; wf_ty v \<rbrakk> \<Longrightarrow> wf_env (v#\<rho>)"
  by (simp add: nth_Cons')

lemma wf_d: "\<lbrakk> wf_env \<rho>; A \<in> D e \<rho> \<rbrakk> \<Longrightarrow> wf_ty A"
  apply (induction e arbitrary: \<rho> A)
       apply simp apply (case_tac "x < length \<rho>") apply force apply force
      apply force
     using lamD_def apply force
  using D.simps(4) apply blast
   apply (smt D.simps(5) mem_Collect_eq)
  by (smt D.simps(6) mem_Collect_eq)
    
theorem d_e: "wf_env \<rho> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<rho> = {B. \<exists>A. A \<in> D e \<rho> \<and> A <: B \<and> wf_ty B }"  
proof (induction e arbitrary: \<rho>)
  case (EVar x)
  then show ?case by auto
next
  case (ENat x)
  then show ?case by auto
next
  case (ELam e)
  { fix f assume wf_f: "wf_ty f" and f_f: "F f e \<rho>"
    have fun_f: "fun_pred f" using f_f f_fun_pred by blast
    have "f \<in> lamD (\<lambda>v. D e (v # \<rho>))" using wf_f fun_f apply (simp add: lamD_def) apply clarify
    proof -
      fix v v' assume vv_f: "(v, v') |\<in>| entries f"
      have 1: "v' \<in> \<lbrakk>e\<rbrakk> (v#\<rho>)" using f_f fun_f f_lam[of f] vv_f by blast
      have wf_vr: "wf_env (v#\<rho>)"
        using vv_f wf_entries[of f v v'] extend_wf_env[of \<rho> v] wf_f ELam.prems by blast
      have "\<lbrakk>e\<rbrakk>v # \<rho> = {B. \<exists>A. A \<in> D e (v # \<rho>) \<and> A <: B \<and> wf_ty B}" 
        using ELam.IH[of "v#\<rho>"] wf_vr by blast
      then show "\<exists>v''. v'' \<in> D e (v # \<rho>) \<and> v'' <: v' " using 1 by auto
    qed        
    then have "\<exists>A. A \<in> lamD (\<lambda>v. D e (v # \<rho>)) \<and> A <: f \<and> wf_ty f" using wf_f by auto
  } moreover { fix f assume "\<exists>A. A \<in> lamD (\<lambda>v. D e (v # \<rho>)) \<and> A <: f \<and> wf_ty f"
    then obtain A where A_D: "A \<in> lamD (\<lambda>v. D e (v # \<rho>))" and A_f: "A <: f" and wf_f: "wf_ty f"
      by blast
    have fun_A: "fun_pred A" using A_D by (simp add: lamD_def) 
    have wf_A: "wf_ty A" using A_D by (simp add: lamD_def) 
    have "\<forall> v v'. (v,v') |\<in>| entries A \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk> (v#\<rho>)"
    proof clarify
      fix v v' assume vv_A: "(v,v') |\<in>| entries A"
      have wf_vr: "wf_env (v#\<rho>)"
        using vv_A wf_entries[of A v v'] extend_wf_env[of \<rho> v] wf_A ELam.prems by blast
      have "\<lbrakk>e\<rbrakk>v # \<rho> = {B. \<exists>A. A \<in> D e (v # \<rho>) \<and> A <: B \<and> wf_ty B}" 
        using ELam.IH[of "v#\<rho>"] wf_vr by blast
      
      then 
      show "v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>)" 
        by (smt A_D lamD_def mem_Collect_eq vv_A wf_entries)
    qed      
    then have F_A: "F A e \<rho>" using f_lam fun_A by blast
    then have F_f: "F f e \<rho>" using subsumption_fun[of A e \<rho> f] A_f
        subsumption A_D ELam.prems lamD_def wf_f by blast      
    then have "wf_ty f \<and> F f e \<rho>" using wf_f by blast }
  ultimately show ?case apply simp
    apply (rule Collect_cong) apply (rule iffI) apply blast apply blast done
next
  case (EApp e1 e2)
  then show ?case 
      apply simp apply (rule Collect_cong) apply (rule iffI) 
     apply clarify apply (rule_tac x=v' in exI) apply (rule conjI)
      apply (rule_tac x=A in exI) apply (rule conjI) apply assumption
      apply (rule_tac x=Aa in exI) apply (rule conjI) apply assumption
      apply (rule conjI) apply (subgoal_tac "v \<rightarrow> v' <: Aa \<rightarrow> v'") prefer 2
        apply blast apply (meson sub_trans) apply assumption apply blast
    apply clarify apply (rule_tac x=f in exI) apply (rule conjI)
     apply (rule_tac x=f in exI) apply (rule conjI) apply assumption  
     apply (rule conjI) apply blast apply (rule wf_d) apply assumption apply assumption
    apply (rule_tac x=v in exI) apply (rule conjI) apply (rule_tac x=v in exI)
     apply (rule conjI) apply assumption apply (rule conjI) apply blast apply (rule wf_d)
      apply assumption apply assumption apply (rule conjI) 
     apply (subgoal_tac "v \<rightarrow> A <: v \<rightarrow> v'") prefer 2 apply blast
     apply (meson sub_trans) apply assumption 
      done
next
  case (EPrim x1a e1 e2)
  then show ?case 
    apply simp apply (rule Collect_cong) apply (rule iffI)
    apply (meson sub_refl sub_trans)
   apply (meson sub_refl sub_trans wf_d) done
next
  case (EIf e1 e2 e3)
  then show ?case 
    apply simp apply (rule Collect_cong) apply (rule iffI)
   apply clarify
   apply (case_tac n) apply simp apply clarify
    apply (meson less_numeral_extra(3) sub_trans)
   apply (meson Suc_neq_Zero sub_trans zero_less_Suc)
  by blast
qed

end