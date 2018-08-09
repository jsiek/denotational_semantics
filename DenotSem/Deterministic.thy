(*<*)
theory Deterministic
  imports Lambda Denot Consistency
begin
(*>*)

section "Environment Weakening" 
  
lemma weaken_env_fun_aux: 
  "\<lbrakk> F v e \<rho>1; \<rho>2 <: \<rho>1; (\<forall> v \<rho>1 \<rho>2. v \<in> \<lbrakk>e\<rbrakk>\<rho>1 \<longrightarrow> \<rho>2 <: \<rho>1 \<longrightarrow> v \<in> \<lbrakk>e\<rbrakk>\<rho>2) \<rbrakk>
   \<Longrightarrow> F v e \<rho>2"
proof (induction v arbitrary: e \<rho>1 \<rho>2)
  case (TNat n)
  then have "False" by auto
  then show ?case ..
next
  case (TArrow v1 v2)
  have "v1#\<rho>2 <: v1#\<rho>1" using TArrow.prems(2) apply auto apply (case_tac k) apply auto done
  then show ?case using TArrow by simp
next
  case (TInter v1 v2)
  then show ?case by auto    
qed    
  
lemma weaken_env: "\<lbrakk> v \<in> \<lbrakk>e\<rbrakk>\<rho>1; \<rho>2 <: \<rho>1 \<rbrakk> \<Longrightarrow> v \<in> \<lbrakk>e\<rbrakk>\<rho>2"
proof  (induction e arbitrary: v \<rho>1 \<rho>2)
  case (EVar x)
  then show ?case 
    apply (case_tac "x < length \<rho>1") using sub_trans apply force apply force done
next
  case (ENat n)
  then show ?case by auto
next
  case (ELam e)
  then show ?case using weaken_env_fun_aux[of v e \<rho>1 \<rho>2] by auto
next
  case (EApp e1 e2)
  then show ?case apply simp apply blast done      
next
  case (EPrim x1a e1 e2)
  then show ?case apply simp apply blast done
next
  case (EIf e1 e2 e3)
  then show ?case apply simp apply blast done
qed

lemma weaken_env_fun: "\<lbrakk> F v e \<rho>1; \<rho>2 <: \<rho>1 \<rbrakk> \<Longrightarrow> F v e \<rho>2"
  using weaken_env_fun_aux weaken_env by blast


section "Determinism and Admissability of Intersection Intro"
  
lemma wf_eval: "\<lbrakk> v \<in> \<lbrakk>e\<rbrakk>\<rho>; wf_env \<rho> \<rbrakk> \<Longrightarrow> wf_ty v"
  apply (induction e) apply (case_tac "x < length \<rho>") apply force+ done
    
lemma consis_codomain:
  fixes a b c d
  assumes ab_g1: "a\<rightarrow>b \<in> set \<Gamma>1" and cd_g2: "c\<rightarrow>d \<in> set \<Gamma>2" and
    v1_g1: "\<forall>v v'. v\<rightarrow>v' \<in> set \<Gamma>1 \<longrightarrow> v1 <: v" and
    v2_g2: "\<forall>v v'. v\<rightarrow>v' \<in> set \<Gamma>2 \<longrightarrow> v2 <: v" and
    v1_v2: "v1 ~ v2" and f1_f2: "f1 ~ f2" and
    g1_f1: "set \<Gamma>1 \<subseteq> atoms f1" and g2_f2: "set \<Gamma>2 \<subseteq> atoms f2"
  shows "b ~ d"
proof -    
    have v1_a: "v1 <: a" using v1_g1 ab_g1 by blast 
    have v2_c: "v2 <: c" using v2_g2 cd_g2 by blast
    have a_c: "a ~ c" using v1_a v2_c v1_v2 consis_le by blast        
    have ab_cd: "a\<rightarrow>b ~ c\<rightarrow>d"
      using ab_g1 cd_g2 g1_f1 g2_f2 f1_f2 consis_atoms by blast
    show "b ~ d" using ab_cd a_c by simp 
qed
    
lemma all_fun_ex: "\<lbrakk> all_funs (set \<Gamma>); x \<in> set \<Gamma>; \<And> a b. \<lbrakk> x = a \<rightarrow> b \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (cases x) apply auto done

lemma all_fun_ex_dom: "\<lbrakk> all_funs (set \<Gamma>); y \<in> set (map cod \<Gamma>) \<rbrakk> \<Longrightarrow> \<exists>x. x\<rightarrow>y \<in> set \<Gamma>"
  apply (induction \<Gamma> arbitrary: y)
  apply force
  apply simp apply (erule disjE) 
   apply simp apply (case_tac a) apply force apply force apply force
  apply blast
  done
    
lemma consistent_app: assumes f1_f2: "f1 ~ f2" and v1_v2: "v1 ~ v2" and 
  f1_v1: "v1' \<in> f1 \<bullet> v1"  and f2_v2: "v2' \<in> f2 \<bullet> v2" and
  wf_f1: "wf_ty f1" and wf_f2: "wf_ty f2" and wf_v1: "wf_ty v1" and wf_v2: "wf_ty v2"
shows "v1' ~ v2'"
proof -
  have f1_v11: "f1 <: v1 \<rightarrow> v1'" using f1_v1 by simp
  have f2_v22: "f2 <: v2 \<rightarrow> v2'" using f2_v2 by simp
      
  obtain \<Gamma>1 where g1_ne: "\<Gamma>1 \<noteq> []" and af_g1: "all_funs (set \<Gamma>1)" and 
    g1_f1: "set \<Gamma>1 \<subseteq> atoms f1" and
    v1_g1: "\<forall>v v'. v\<rightarrow>v' \<in> set \<Gamma>1 \<longrightarrow> v1 <: v" and 
    g1_v1p: "\<Sqinter>(map cod \<Gamma>1) <: v1'"
    using f1_v11 sub_fun_any_inv_atoms[of f1 v1 v1'] by blast
  let ?C1 = "map cod \<Gamma>1"     
  obtain \<Gamma>2 where g2_ne: "\<Gamma>2 \<noteq> []" and af_g2: "all_funs (set \<Gamma>2)" and 
    g2_f2: "set \<Gamma>2 \<subseteq> atoms f2" and
    v2_g2: "\<forall>v v'. v\<rightarrow>v' \<in> set \<Gamma>2 \<longrightarrow> v2 <: v" and 
    g2_v2p: "\<Sqinter>(map cod \<Gamma>2) <: v2'"
    using f2_v22 sub_fun_any_inv_atoms[of f2 v2 v2'] by blast
  let ?C2 = "map cod \<Gamma>2"

  have wf_c1: "\<forall>v. v \<in> set ?C1 \<longrightarrow> wf_ty v"
    using g1_f1 wf_f1 af_g1 apply auto
    apply (erule all_fun_ex) apply blast apply simp using wf_atoms apply auto done
  have wf_c2: "\<forall>v. v \<in> set ?C2 \<longrightarrow> wf_ty v"
    using g2_f2 wf_f2 af_g2 apply auto
    apply (erule all_fun_ex) apply blast apply simp using wf_atoms apply auto done
  have c_c1: "\<forall>v1' v2'. {v1',v2'} \<subseteq> set ?C1 \<longrightarrow> v1' ~ v2'"
  proof clarify
    fix v1' v2' assume 1: "{v1',v2'} \<subseteq> set ?C1"        
    have v1_c1: "v1' \<in> set ?C1" using 1 by blast 
    have v2_c1: "v2' \<in> set ?C1" using 1 by blast
    obtain d1 where v11_g1: "d1\<rightarrow>v1' \<in> set \<Gamma>1" 
      using v1_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v1'] by blast
    obtain d2 where v22_g1: "d2\<rightarrow>v2' \<in> set \<Gamma>1" 
      using v2_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v2'] by blast        
    show "v1' ~ v2'"
      apply (rule consis_codomain[of d1 v1' \<Gamma>1 d2 v2' \<Gamma>1 v1 v1 f1 f1])
      using v11_g1 v22_g1 v1_g1 consis_refl wf_v1 wf_f1 g1_f1 by auto   
  qed
  have c_c2: "\<forall>v1' v2'. {v1',v2'} \<subseteq> set ?C2 \<longrightarrow> v1' ~ v2'"
  proof clarify
    fix v1' v2' assume 1: "{v1',v2'} \<subseteq> set ?C2"        
    have v1_c1: "v1' \<in> set ?C2" using 1 by blast 
    have v2_c1: "v2' \<in> set ?C2" using 1 by blast
    obtain d1 where v11_g2: "d1\<rightarrow>v1' \<in> set \<Gamma>2" 
      using v1_c1 af_g2 all_fun_ex_dom[of \<Gamma>2 v1'] by blast
    obtain d2 where v22_g2: "d2\<rightarrow>v2' \<in> set \<Gamma>2" 
      using v2_c1 af_g2 all_fun_ex_dom[of \<Gamma>2 v2'] by blast        
    show "v1' ~ v2'"
      apply (rule consis_codomain[of d1 v1' \<Gamma>2 d2 v2' \<Gamma>2 v2 v2 f2 f2])
      using v11_g2 v22_g2 v2_g2 consis_refl wf_v2 wf_f2 g2_f2 by auto   
  qed
  have c1_c2: "\<Sqinter>?C1 ~ \<Sqinter>?C2" 
  proof (rule meet_list_consis)
    show "map cod \<Gamma>1 \<noteq> []" using g1_ne by auto
  next
    show "map cod \<Gamma>2 \<noteq> []" using g2_ne by auto
  next
    show "\<forall>v1 v2. {v1, v2} \<subseteq> set ?C1 \<union> set ?C2 \<longrightarrow> v1 ~ v2"
    proof clarify
      fix v1' v2' assume 1: "{v1',v2'} \<subseteq> set ?C1 \<union> set ?C2"        
      { assume v1_c1: "v1' \<in> set ?C1" and v2_c1: "v2' \<in> set ?C1"
        have "v1' ~ v2'" using v1_c1 v2_c1 c_c1 by blast
      } moreover {
        assume v1_c1: "v1' \<in> set ?C1" and v2_c2: "v2' \<in> set ?C2"
        obtain d1 where v11_g1: "d1\<rightarrow>v1' \<in> set \<Gamma>1" 
          using v1_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v1'] by blast
        obtain d2 where v22_g2: "d2\<rightarrow>v2' \<in> set \<Gamma>2" 
          using v2_c2 af_g2 all_fun_ex_dom[of \<Gamma>2 v2'] by blast        
        have "v1' ~ v2'" 
          apply (rule consis_codomain)
          using v11_g1 apply blast using v22_g2 apply blast using v1_g1 apply blast
          using v2_g2 apply blast using v1_v2 apply blast using f1_f2 apply blast
          using g1_f1 apply blast using g2_f2 apply blast done          
      } moreover {
        assume v1_c2: "v1' \<in> set ?C2" and v2_c1: "v2' \<in> set ?C1"
        obtain d1 where v11_g2: "d1\<rightarrow>v1' \<in> set \<Gamma>2" 
          using v1_c2 af_g2 all_fun_ex_dom[of \<Gamma>2 v1'] by blast
        obtain d2 where v22_g1: "d2\<rightarrow>v2' \<in> set \<Gamma>1" 
          using v2_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v2'] by blast        
        have "v1' ~ v2'" 
          apply (rule consis_codomain)
          using v11_g2 apply blast using v22_g1 apply blast using v2_g2 apply blast
          using v1_g1 apply blast using v1_v2 consis_sym apply blast
          apply (rule consis_sym) using f1_f2 apply blast using g2_f2 apply blast           
          using g1_f1 apply blast done        
      } moreover {
        assume v1_c2: "v1' \<in> set ?C2" and v2_c2: "v2' \<in> set ?C2"
        have "v1' ~ v2'" using v1_c2 v2_c2 c_c2 g2_ne by auto 
      } ultimately show "v1' ~ v2'" using 1 by blast
    qed      
  qed  
  then show ?thesis using g1_v1p g2_v2p consis_le by blast
qed

lemma inter_app: assumes f1_v1: "v1' \<in> f1 \<bullet> v1" and f2_v2: "v2' \<in> f2 \<bullet> v2" and 
  f1_f2: "f1 ~ f2" and v1_v2: "v1 ~ v2" and v1p_v2p: "v1' ~ v2'"
  shows "v1' \<sqinter> v2' \<in> (f1 \<sqinter> f2) \<bullet> (v1 \<sqinter> v2)"
proof -
  have wf_v12: "wf_ty (v1' \<sqinter> v2')" using f1_v1 f2_v2 v1p_v2p by auto 
  have f1_v1p: "f1 <: v1 \<rightarrow> v1'" using f1_v1 by simp
  have f2_v2p: "f2 <: v2 \<rightarrow> v2'" using f2_v2 by simp  
  have "f1 \<sqinter> f2 <: (v1\<rightarrow>v1') \<sqinter> (v2\<rightarrow>v2')" using f1_v1p f2_v2p by (rule sub_mon)
  also have "(v1 \<rightarrow> v1') \<sqinter> (v2 \<rightarrow> v2') <: (v1 \<sqinter> v2) \<rightarrow> (v1' \<sqinter> v2')" by (rule sub_dist_union_fun)
  finally have "f1 \<sqinter> f2 <: (v1 \<sqinter> v2) \<rightarrow> (v1' \<sqinter> v2')" using sub_trans by auto
  then show ?thesis using wf_v12 by simp
qed

lemma denot_fun_atoms: 
  "\<lbrakk> all_funs (atoms v); \<forall>v1 v2. v1\<rightarrow>v2 \<in> atoms v \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>v1#\<rho> \<rbrakk> \<Longrightarrow> F v e \<rho>"
  by (induction v) auto    

lemma denot_fun_inv_atoms: "F v e \<rho> \<Longrightarrow> all_funs (atoms v) 
   \<and> (\<forall>v1 v2. v1\<rightarrow>v2 \<in> atoms v \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>v1#\<rho>)"
  apply (induction v) apply auto done
    
lemma eval_fun_all_funs: "F v e \<rho> \<Longrightarrow> all_funs (atoms v)"
  apply (induction v) apply auto done

lemma denot_fold_meet_inv_init: "F (fold op \<sqinter> L A) e \<rho> \<Longrightarrow> F A e \<rho>"
  apply (induction L arbitrary: A)
   apply force
  apply simp
  apply (subgoal_tac "F (a \<sqinter> A) e \<rho>") prefer 2 apply blast
  apply simp
  done    

lemma denot_fold_meet_swap_init: "\<lbrakk> F (fold op \<sqinter> L A) e \<rho>; F B e \<rho> \<rbrakk> 
   \<Longrightarrow>  F (fold op \<sqinter> L B) e \<rho>"
  apply (induction L arbitrary: A B) apply force
  apply simp 
  apply (subgoal_tac "F (a \<sqinter> A) e \<rho>") prefer 2 using denot_fold_meet_inv_init apply blast
  apply (subgoal_tac "F (a \<sqinter> B) e \<rho>") prefer 2 apply force
  apply blast  
  done    

abbreviation consis_funs :: "ty list \<Rightarrow> bool" where
  "consis_funs L \<equiv> \<forall>v1 v1' v2 v2'. {v1\<rightarrow>v1',v2\<rightarrow>v2'} \<subseteq> (set L) \<longrightarrow> v1 ~ v2 \<and> v1' ~ v2'"  

abbreviation wf_list :: "ty list \<Rightarrow> bool" where
  "wf_list L \<equiv> \<forall>v. v \<in> set L \<longrightarrow> wf_ty v"

abbreviation determ :: "ty \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "determ v1 v2 e \<rho>1 \<rho>2 \<equiv> v1 \<in> \<lbrakk>e\<rbrakk>\<rho>1 \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>\<rho>2
     \<longrightarrow> wf_env \<rho>1 \<longrightarrow> wf_env \<rho>2 \<longrightarrow> consis_env \<rho>1 \<rho>2
     \<longrightarrow> v1 \<sqinter> v2 \<in> \<lbrakk>e\<rbrakk>(\<rho>1\<sqinter>\<rho>2) \<and> wf_ty (v1 \<sqinter> v2)" 
 
lemma deterministic: "\<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2"
proof (induction e)
  case (EVar x)
  show ?case
    apply clarify apply (case_tac "x < length \<rho>1") defer apply force
    apply simp apply clarify apply (rule conjI)
  proof -
    fix v1::ty and v2::ty and \<rho>1 \<rho>2
    assume "\<rho>1 ! x <: v1" and "\<rho>2 ! x <: v2"    
    then show "\<rho>1 ! x \<sqinter> \<rho>2 ! x <: v1 \<sqinter> v2" by (rule sub_mon)
  next
    fix v1::ty and v2::ty and \<rho>1 \<rho>2
    assume wv1: "wf_ty v1" and wv2: "wf_ty v2" and c_r1_r2: "\<forall>k<length \<rho>2. \<rho>1 ! k ~ \<rho>2 ! k" and
      r1x_v1: "\<rho>1 ! x <: v1" and r2x_v2: "\<rho>2 ! x <: v2" and
      l_r1r2: "length \<rho>1 = length \<rho>2" and x_r2: "x < length \<rho>2"
    have "\<rho>1!x ~ \<rho>2!x" using c_r1_r2 l_r1r2 x_r2 by blast
    then have "v1 ~ v2" using consis_le r1x_v1 r2x_v2 by blast
    then show "wf_ty (v1 \<sqinter> v2)" using wv1 wv2 by blast
 qed
next
  case (ENat n)
  show ?case apply simp apply clarify apply (rule conjI)
  proof -
    fix v1 v2 \<rho>1 \<rho>2
    assume "TNat n <: v1" and "TNat n <: v2"
    then show "TNat n <: v1 \<sqinter> v2" by blast
  next
    fix v1 v2 \<rho>1 \<rho>2
    assume n_v1: "TNat n <: v1" and n_v2: "TNat n <: v2" and wf_v1: "wf_ty v1" and wf_v2: "wf_ty v2"
    have "v1 ~ v2" using n_v1 n_v2 consis_le by auto
    then show "wf_ty (v1 \<sqinter> v2)" using wf_v1 wf_v2 by blast
  qed    
next
  case (ELam e)
  show ?case
    apply (rule allI)+ apply (rule impI)+
  proof -
    fix v1 v2 \<rho>1 \<rho>2 assume v1_le: "v1 \<in> \<lbrakk>\<lambda> e\<rbrakk>\<rho>1" and v2_le: "v2 \<in> \<lbrakk>\<lambda> e\<rbrakk>\<rho>2" and
      wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and c_r1_r2: "consis_env \<rho>1 \<rho>2" 
    have wf_v1: "wf_ty v1" using v1_le by simp
    have wf_v2: "wf_ty v2" using v2_le by simp
    have f_v1_e_r1: "F v1 e \<rho>1" using v1_le by simp      
    have f_v2_e_r2: "F v2 e \<rho>2" using v2_le by simp      
    have r12_r1: "\<rho>1\<sqinter>\<rho>2 <: \<rho>1" using c_r1_r2 by auto
    have r12_r2: "\<rho>1\<sqinter>\<rho>2 <: \<rho>2" using c_r1_r2 by auto
    have "v1 ~ v2" apply (rule atoms_consis) apply clarify
    proof -
      fix A1 A2 assume a1_v1: "A1 \<in> atoms v1" and a2_v2: "A2 \<in> atoms v2"
      obtain A11 A12 where a1: "A1=A11\<rightarrow>A12" and a12_e: "A12 \<in> \<lbrakk>e\<rbrakk>A11#\<rho>1" using f_v1_e_r1 
        by (metis a1_v1 atoms_not_inter denot_fun_inv_atoms ty.simps(10)
            wf_atoms wf_ty.simps wf_v1)
      obtain A21 A22 where a2: "A2=A21\<rightarrow>A22" and a22_e: "A22 \<in> \<lbrakk>e\<rbrakk>A21#\<rho>2" using f_v2_e_r2 
        by (metis a2_v2 atoms_not_inter denot_fun_inv_atoms ty.simps(10) 
            wf_atoms wf_ty.simps wf_v2)
      show "A1 ~ A2"
      proof (cases "A11 ~ A21")
        case True
        have c_ar1_ar2: "consis_env (A11#\<rho>1) (A21#\<rho>2)" using True c_r1_r2 apply auto
          apply (case_tac k) apply auto done
        have wf_ar1: "wf_env (A11#\<rho>1)" using wf_r1 a1 a1_v1 wf_v1 apply auto
          apply (case_tac k) apply auto using wf_ty_arrow_inv by blast
        have wf_ar2: "wf_env (A21#\<rho>2)" using wf_r2 a2 a2_v2 wf_v2 apply auto
          apply (case_tac k) apply auto using wf_ty_arrow_inv by blast
        have "determ A12 A22 e (A11#\<rho>1) (A21#\<rho>2)" using ELam by blast
        then show ?thesis using c_ar1_ar2 a12_e a22_e wf_ar1 wf_ar2 True a1 a2 by auto
      next
        case False
        then show ?thesis using a1 a2 by simp
      qed
    qed        
    then have wf_v12: "wf_ty (v1 \<sqinter> v2)" using wf_v1 wf_v2 by auto
    have f_v1_e: "F v1 e (\<rho>1 \<sqinter> \<rho>2)" using f_v1_e_r1 r12_r1 weaken_env_fun by blast
    have f_v2_e: "F v2 e (\<rho>1 \<sqinter> \<rho>2)" using f_v2_e_r2 r12_r2 weaken_env_fun by blast
    show "v1 \<sqinter> v2 \<in> \<lbrakk>\<lambda> e\<rbrakk>\<rho>1 \<sqinter> \<rho>2 \<and> wf_ty (v1 \<sqinter> v2)" using wf_v12 f_v1_e f_v2_e by simp
  qed
next
  case (EApp e1 e2)
  show ?case
    apply (rule allI)+ apply (rule impI)+
  proof -
    fix v1 v2 \<rho>1 \<rho>2 assume v1_e1e2: "v1 \<in> \<lbrakk>EApp e1 e2\<rbrakk>\<rho>1" and v2_e1e2: "v2 \<in> \<lbrakk>EApp e1 e2\<rbrakk>\<rho>2" and
      wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and c_r1_r2: "consis_env \<rho>1 \<rho>2"
    obtain f1 v21 where f1_e1: "f1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v21_e2: "v21\<in> \<lbrakk>e2\<rbrakk>\<rho>1" and 
      f1_v21: "v1 \<in> f1 \<bullet> v21" using v1_e1e2 by auto
    obtain f2 v22 where f2_e1: "f2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v22_e2: "v22\<in> \<lbrakk>e2\<rbrakk>\<rho>2" and 
      f2_v22: "v2 \<in> f2 \<bullet> v22" using v2_e1e2 by auto
    have "determ f1 f2 e1 \<rho>1 \<rho>2" using EApp(1) by blast
    then have f12_e1: "f1 \<sqinter> f2 \<in> \<lbrakk>e1\<rbrakk>\<rho>1\<sqinter>\<rho>2" and wf_f12: "wf_ty (f1 \<sqinter> f2)"         
      using f1_e1 f2_e1 wf_r1 wf_r2 c_r1_r2 by auto
    have "determ v21 v22 e2 \<rho>1 \<rho>2" using EApp(2) by blast
    then have v22_e2: "v21 \<sqinter> v22 \<in> \<lbrakk>e2\<rbrakk>\<rho>1\<sqinter>\<rho>2" and wf_v21_v22: "wf_ty (v21 \<sqinter> v22)"
      using v21_e2 v22_e2 wf_r1 wf_r2 c_r1_r2 by auto
    have v1_v2: "v1 ~ v2"
      using consistent_app[of f1 f2 v21 v22 v1 v2] wf_f12 wf_v21_v22 f1_v21 f2_v22 by blast        
    have f12_v21_v22: "v1 \<sqinter> v2 \<in> (f1 \<sqinter> f2) \<bullet> (v21 \<sqinter> v22)"
      using inter_app[of v1 f1 v21 v2 f2 v22] f1_v21 f2_v22 wf_f12 wf_v21_v22 v1_v2 wf_ty_inter_inv
      by metis
    have wf_v1: "wf_ty v1" using f1_v21 by blast
    have wf_v2: "wf_ty v2" using f2_v22 by blast
    show "v1 \<sqinter> v2 \<in> \<lbrakk>EApp e1 e2\<rbrakk>\<rho>1 \<sqinter> \<rho>2 \<and> wf_ty (v1 \<sqinter> v2)"
      using f12_e1 v22_e2 v1_v2 wf_v1 wf_v2 v1_v2 f12_v21_v22 by auto
  qed      
next
  case (EPrim f e1 e2)
  show ?case 
    apply (rule allI)+ apply (rule impI)+
  proof -
    fix v1 v2 \<rho>1 \<rho>2
    assume v1_p: "v1 \<in> \<lbrakk>EPrim f e1 e2\<rbrakk>\<rho>1" and v2_p: "v2 \<in> \<lbrakk>EPrim f e1 e2\<rbrakk>\<rho>2" and 
      wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and c_r1_r2: "consis_env \<rho>1 \<rho>2"
    obtain v11 v21 n1 n2 where v11_e1_r1: "v11 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v21_e2_r1: "v21 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" and
      v11_n1: "v11 <: TNat n1" and v21_n2: "v21 <: TNat n2" and
      fn12_v1: "TNat (f n1 n2) <: v1" and wf_v1: "wf_ty v1" using v1_p by auto
    obtain v12 v22 n3 n4 where v12_e1_r2: "v12 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v22_e2_r2: "v22 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and
      v12_n3: "v12 <: TNat n3" and v22_n4: "v22 <: TNat n4" and
      fn34_v2: "TNat (f n3 n4) <: v2" and wf_v2: "wf_ty v2" using v2_p by auto
        
    have IH1: "determ v11 v12 e1 \<rho>1 \<rho>2" using EPrim(1) by simp
    have "wf_ty (v11 \<sqinter> v12)" using IH1 v11_e1_r1 v12_e1_r2 c_r1_r2 wf_r1 wf_r2 by blast
    then have "TNat n1 ~ TNat n3" using v11_n1 v12_n3 consis_le by blast
    then have n1_n3: "n1 = n3" by simp
        
    have IH2: "determ v21 v22 e2 \<rho>1 \<rho>2" using EPrim(2) by simp
    have "wf_ty (v21 \<sqinter> v22)" using IH2 v21_e2_r1 v22_e2_r2 c_r1_r2 wf_r1 wf_r2 by blast
    then have "TNat n2 ~ TNat n4" using v21_n2 v22_n4 consis_le by blast
    then have n2_n4: "n2 = n4" by simp
        
    have v1_v2: "v1 ~ v2" using n1_n3 n2_n4 fn12_v1 fn34_v2 consis_le by blast
    have r12_r1: "\<rho>1\<sqinter>\<rho>2 <: \<rho>1" using c_r1_r2 apply auto done
        
    have v11_r12: "v11 \<in> \<lbrakk>e1\<rbrakk>\<rho>1\<sqinter>\<rho>2" using r12_r1 v11_e1_r1 weaken_env by blast
    have v21_r12: "v21 \<in> \<lbrakk>e2\<rbrakk>\<rho>1\<sqinter>\<rho>2" using r12_r1 v21_e2_r1 weaken_env by blast
        
    show "v1 \<sqinter> v2 \<in> \<lbrakk>EPrim f e1 e2\<rbrakk>\<rho>1 \<sqinter> \<rho>2 \<and> wf_ty (v1 \<sqinter> v2)"
      using v11_r12 v21_r12 v1_v2 wf_v1 wf_v2
      apply simp using fn12_v1 fn34_v2 n1_n3 n2_n4 v11_n1 v21_n2 by blast
  qed
next
  case (EIf e1 e2 e3)
  show ?case
    apply (rule allI)+ apply (rule impI)+
  proof -
    fix v1 v2 \<rho>1 \<rho>2
    assume v1_p: "v1 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>1" and v2_p: "v2 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>2" and 
      wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and c_r1_r2: "consis_env \<rho>1 \<rho>2"
    obtain v11 n1 where v11_e1: "v11 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v11_n1: "v11 <: TNat n1" and
      v1_e3: "n1 = 0 \<longrightarrow> v1 \<in> \<lbrakk>e3\<rbrakk>\<rho>1" and v1_e2: "n1 \<noteq> 0 \<longrightarrow> v1 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" using v1_p by auto
    obtain v12 n2 where v12_e1: "v12 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v12_n2: "v12 <: TNat n2" and
      v2_e3: "n2 = 0 \<longrightarrow> v2 \<in> \<lbrakk>e3\<rbrakk>\<rho>2" and v2_e2: "n2 \<noteq> 0 \<longrightarrow> v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" using v2_p by auto
        
    have IH1: "determ v11 v12 e1 \<rho>1 \<rho>2" using EIf(1) by simp
    have "wf_ty (v11 \<sqinter> v12)" using IH1 v11_e1 v12_e1 c_r1_r2 wf_r1 wf_r2 by blast
    then have "TNat n1 ~ TNat n2" using v11_n1 v12_n2 consis_le by blast
    then have n1_n2: "n1 = n2" by simp
        
    have IH2: "determ v1 v2 e2 \<rho>1 \<rho>2" using EIf(2) by simp
    have IH3: "determ v1 v2 e3 \<rho>1 \<rho>2" using EIf(3) by simp
        
    { assume n1: "n1 = 0"
      have "v1 \<sqinter> v2 \<in> \<lbrakk>e3\<rbrakk>\<rho>1\<sqinter>\<rho>2" and "wf_ty (v1 \<sqinter> v2)"
        using IH3 v1_e3 v2_e3 wf_r1 wf_r2 c_r1_r2 wf_r1 wf_r2 n1 n1_n2 by auto
    } moreover { assume n1: "n1 \<noteq> 0"
      have "v1 \<sqinter> v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>1\<sqinter>\<rho>2" and "wf_ty (v1 \<sqinter> v2)"
        using IH2 v1_e2 v2_e2 wf_r1 wf_r2 c_r1_r2 wf_r1 wf_r2 n1 n1_n2 by auto        
    } ultimately
    show "v1 \<sqinter> v2 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>1 \<sqinter> \<rho>2 \<and> wf_ty (v1 \<sqinter> v2)"
      by (smt E.simps(6) c_r1_r2 case_prod_conv length_map length_zip mem_Collect_eq
          min.idem n1_n2 nth_map nth_zip sub_inter_right2 sub_refl v12_e1 v12_n2 weaken_env)          
  qed
qed    

section "Subsumption is Admissible"  

lemma fun_eval_distr:
  "\<lbrakk> F (A \<rightarrow> B \<sqinter> C \<rightarrow> D) e \<rho>; wf_env \<rho>; wf_ty A; wf_ty C; A ~ C \<rbrakk>
    \<Longrightarrow> F ((A \<sqinter> C) \<rightarrow> (B \<sqinter> D)) e \<rho>"
  apply simp apply clarify
  apply (subgoal_tac "(A\<sqinter>C)#\<rho> <: A # \<rho>") prefer 2 apply simp 
   apply clarify apply (case_tac k) apply force apply force
  apply (subgoal_tac "(A\<sqinter>C)#\<rho> <: C # \<rho>") prefer 2 apply simp 
   apply clarify apply (case_tac k) apply force apply force
  apply (subgoal_tac "B \<in> \<lbrakk>e\<rbrakk>(A\<sqinter>C)#\<rho>") prefer 2 using weaken_env apply blast
  apply (subgoal_tac "D \<in> \<lbrakk>e\<rbrakk>(A\<sqinter>C)#\<rho>") prefer 2 using weaken_env apply blast
  apply (subgoal_tac "wf_env ((A\<sqinter>C)#\<rho>)") prefer 2 apply simp apply clarify
    apply (case_tac k) apply simp apply blast apply force
  apply (subgoal_tac "B \<sqinter> D \<in> \<lbrakk>e\<rbrakk>((A \<sqinter> C) # \<rho>) \<sqinter> ((A \<sqinter> C) # \<rho>)") prefer 2 
    using deterministic consis_refl apply presburger
  apply (subgoal_tac "(A \<sqinter> C) # \<rho> <: ((A \<sqinter> C) # \<rho>) \<sqinter> ((A \<sqinter> C) # \<rho>)") prefer 2
   apply simp apply clarify apply (case_tac k) prefer 2 apply force
    apply simp 
  apply blast
  apply (rule weaken_env)    
   apply blast
    apply blast
  done

lemma denot_fun_fold_meet:
  "\<lbrakk> F (fold op \<sqinter> L (A\<rightarrow>B)) e \<rho>; all_funs (set L); wf_env \<rho>; wf_ty A; wf_ty B;
     wf_list L; consis_funs ((A\<rightarrow>B)#L) \<rbrakk> \<Longrightarrow> 
    F ((fold op \<sqinter> (map dom L) A) \<rightarrow> (fold op \<sqinter> (map cod L) B)) e \<rho>"
  apply (induction L arbitrary: A B)
   apply force
   apply (case_tac a) apply force defer apply force
  apply (rename_tac A' B') apply clarify    
  apply (subgoal_tac "F (fold op \<sqinter> L ((A'\<sqinter>A) \<rightarrow> (B' \<sqinter> B))) e \<rho>") prefer 2
   apply (rule denot_fold_meet_swap_init)
    apply force
   apply (rule fun_eval_distr)
   apply (subgoal_tac "F (A' \<rightarrow> B' \<sqinter> A \<rightarrow> B) e \<rho>") prefer 2
         apply (rule denot_fold_meet_inv_init)
         apply force
   apply assumption apply assumption 
   apply force
    apply assumption
  apply (metis bot_least consis_sym insert_mono list.set(2))
  apply (subgoal_tac "wf_ty (A'\<sqinter>A)") 
   apply (subgoal_tac "wf_ty (B'\<sqinter>B)")
    apply (subgoal_tac "\<forall>v1 v1' v2 v2'. {v1\<rightarrow>v1',v2\<rightarrow>v2'} \<subseteq> insert ((A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B)) (set L)
                         \<longrightarrow> v1 ~ v2 \<and> v1' ~ v2'")
     apply simp
    defer
      
    apply (subgoal_tac "B ~ B'") prefer 2 
     apply (metis bot_least insert_mono list.set(2))
    apply (subgoal_tac "wf_ty B'") prefer 2 apply auto[1]
    apply (subgoal_tac "B' ~ B") prefer 2 apply (rule consis_sym) apply blast
    apply blast
    
    apply (subgoal_tac "A ~ A'") prefer 2 
      apply (metis bot_least insert_mono list.set(2))
    apply (subgoal_tac "wf_ty A'") prefer 2 apply auto[1]
    apply (subgoal_tac "A' ~ A") prefer 2 apply (rule consis_sym) apply blast
   apply blast
    apply clarify
proof -
  fix a L A B A' B' v1 v1' v2 v2'
  assume 1: "consis_funs ((A \<rightarrow> B) # (A' \<rightarrow> B') # L)"
    and 2: "{v1 \<rightarrow> v1', v2 \<rightarrow> v2'} \<subseteq> insert ((A' \<sqinter> A) \<rightarrow> (B' \<sqinter> B)) (set L)"
    and "wf_ty A'" and "wf_ty A" and "wf_ty B" and "wf_ty B'" and "A' ~ A" and "B'~B"    
  have "v1 \<rightarrow> v1' = (A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B) \<or> v1\<rightarrow>v1' \<in> set L" using 2 apply auto done
  then show "v1 ~ v2 \<and> v1' ~ v2' "
  proof 
    assume v11: "v1 \<rightarrow> v1' = (A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B)"
    have "v2 \<rightarrow> v2' = (A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B) \<or> v2\<rightarrow>v2' \<in> set L" using 2 apply auto done
    then show "v1 ~ v2 \<and> v1' ~ v2' "
    proof
      assume v22: "v2 \<rightarrow> v2' = (A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B)"
      show ?thesis using v22 v11 apply simp 
        by (simp add: \<open>A' ~ A\<close> \<open>B' ~ B\<close> \<open>wf_ty A'\<close> \<open>wf_ty A\<close> \<open>wf_ty B'\<close> \<open>wf_ty B\<close> 
            consis_refl consis_sym)
    next
      assume v22: "v2 \<rightarrow> v2' \<in> set L"
      have ap_v2: "A' ~ v2" using 1 v22 apply auto done
      have a_v2: "A ~ v2" using 1 v22 apply auto done
      have aa_v2: "A'\<sqinter>A ~ v2" using ap_v2 a_v2 apply blast done
      have bp_v2p: "B' ~ v2'" using 1 v22 apply auto done
      have b_v2: "B ~ v2'" using 1 v22 apply auto done
      have bb_v2: "B'\<sqinter>B ~ v2'" using bp_v2p b_v2 apply blast done          
      show ?thesis using v11 v22 aa_v2 bb_v2 apply simp done
    qed
  next
    assume v11: "v1 \<rightarrow> v1' \<in> set L"
    have "v2 \<rightarrow> v2' = (A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B) \<or> v2\<rightarrow>v2' \<in> set L" using 2 apply auto done
    then show "v1 ~ v2 \<and> v1' ~ v2' "
    proof
      assume v22: "v2 \<rightarrow> v2' = (A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B)"
      have ap_v1: "A' ~ v1" using 1 v22 v11 apply auto done
      have a_v1: "A ~ v1" using 1 v22 v11 apply auto done
      have aa_v1: "A'\<sqinter>A ~ v1" using ap_v1 a_v1 apply blast done
          
      have bp_v2p: "B' ~ v1'" using 1 v22 v11 apply auto done
      have b_v2: "B ~ v1'" using 1 v22 v11 apply auto done
      have bb_v2: "B'\<sqinter>B ~ v1'" using bp_v2p b_v2 apply blast done          

      show ?thesis using v11 v22 aa_v1 bb_v2 consis_sym apply simp done
    next
      assume v22: "v2 \<rightarrow> v2' \<in> set L"
      show ?thesis using v11 v22 1 apply auto done
    qed 
  qed    
qed    
  
lemma denot_fun_meet_list: "\<lbrakk> F (\<Sqinter>L) e \<rho>; L \<noteq> []; all_funs (set L); wf_env \<rho>;
   consis_funs L; wf_list L \<rbrakk> 
  \<Longrightarrow> F (\<Sqinter>(map dom L) \<rightarrow> \<Sqinter>(map cod L)) e \<rho>"
  apply (cases L) apply force
  unfolding meet_list_def apply clarify
  apply (case_tac a) apply force defer apply force apply simp
  apply (subgoal_tac "wf_ty x21") prefer 2 apply blast
  apply (subgoal_tac "wf_ty x22") prefer 2 apply blast    
    using denot_fun_fold_meet apply simp 
  done

abbreviation subsump :: "ty \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> bool" where
  "subsump v1 v2 e \<rho> \<equiv> v1 \<in> \<lbrakk>e\<rbrakk>\<rho> \<longrightarrow> v1 <: v2 \<longrightarrow> wf_ty v2 \<longrightarrow> wf_env \<rho> \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>\<rho>" 
    
lemma subsumption_fun: fixes v1::ty and v2::ty
  assumes v1_e: "F v1 e \<rho>" and v1_v2: "v1 <: v2" and
    wf_v1: "wf_ty v1"  and wf_v2: "wf_ty v2" and wf_r: "wf_env \<rho>" and
    IH: "\<forall>v1 v2 \<rho>. subsump v1 v2 e \<rho>"
  shows "F v2 e \<rho>"
proof (rule denot_fun_atoms)
  have "all_funs (atoms v1)" using v1_e eval_fun_all_funs by simp
  then show "all_funs (atoms v2)" using v1_v2 
    using d_fun_atoms_L_inv sub_ty_def by auto 
next
  show "\<forall>v1 v2a. v1 \<rightarrow> v2a \<in> atoms v2 \<longrightarrow> v2a \<in> \<lbrakk>e\<rbrakk>v1 # \<rho>"
  proof clarify
    fix A B assume ab_v2: "A \<rightarrow> B \<in> atoms v2"
    have v1_ab: "v1 <: A \<rightarrow> B" using v1_v2 ab_v2 sub_atom_sub by blast
    then show "B \<in> \<lbrakk>e\<rbrakk>A#\<rho>"
    proof (rule sub_any_fun_elim)
      fix \<Gamma>1 assume g_ne: "\<Gamma>1 \<noteq> []" and af_g: "all_funs (set \<Gamma>1)" and 
        gp_v1: "set \<Gamma>1 \<subseteq> atoms v1" and
        a_g1: "\<forall>v v'. v \<rightarrow> v' \<in> set \<Gamma>1 \<longrightarrow> A <: v" and
        cg_b: "\<Sqinter> (map cod \<Gamma>1) <: B"
      have a_dg: "A <: \<Sqinter> (map dom \<Gamma>1)" using a_g1 meet_list_ub af_g g_ne by blast
      have wf_B: "wf_ty B" using wf_v2 ab_v2 wf_ty_arrow_inv by blast
      have af_v1: "all_funs (atoms v1)" and 
        v1_e_atoms: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>v#\<rho>"
        using v1_e denot_fun_inv_atoms[of v1 e \<rho>] by auto
      have c_g1: "consis_funs \<Gamma>1"
        apply clarify apply (rename_tac W X Y Z)
        apply (subgoal_tac "W\<rightarrow>X \<in> atoms v1") prefer 2 using gp_v1 af_g apply auto[1] 
        apply (subgoal_tac "Y\<rightarrow>Z \<in> atoms v1") prefer 2 using gp_v1 af_g apply auto[1] 
        by (metis wf_v1 a_g1 ab_v2 consis_le consis_refl consistent.simps(4) insert_subset 
            wf_atoms wf_consis_atoms wf_ty_arrow_inv wf_v2)        
      have wf_g1: "wf_list \<Gamma>1" using gp_v1 wf_v1 by blast
      have ag1: "atoms (\<Sqinter>\<Gamma>1) = ctx_atoms \<Gamma>1" 
        by (simp add: g_ne)
      have af_mg1: "all_funs (atoms (\<Sqinter>\<Gamma>1))" using af_g ag1 apply auto
          apply (case_tac x) apply auto done
      have "atoms (\<Sqinter>\<Gamma>1) \<subseteq> atoms v1" using ag1 gp_v1 af_g apply simp
        apply (rule subsetI) apply simp apply clarify 
        apply (case_tac xa) apply auto done
      then have "F (\<Sqinter>\<Gamma>1) e \<rho>" using v1_e_atoms af_mg1 denot_fun_atoms by blast
      then have "F (\<Sqinter>(map dom \<Gamma>1) \<rightarrow> \<Sqinter>(map cod \<Gamma>1)) e \<rho>"
        using denot_fun_meet_list af_g g_ne wf_r c_g1 wf_g1 by blast
      then have cg1_e: "\<Sqinter> (map cod \<Gamma>1) \<in> \<lbrakk>e\<rbrakk>(\<Sqinter> (map dom \<Gamma>1))#\<rho>" by simp
      have "A#\<rho> <: (\<Sqinter> (map dom \<Gamma>1))#\<rho>" using a_dg apply auto apply (case_tac k) apply auto done
      then have cg1_e: "\<Sqinter> (map cod \<Gamma>1) \<in> \<lbrakk>e\<rbrakk>A#\<rho>" using cg1_e weaken_env by blast
      have "wf_ty A" using wf_v2 ab_v2 wf_ty_arrow_inv by blast
      then have "wf_env (A#\<rho>)" using wf_r apply auto apply (case_tac k) apply auto done
      then show ?thesis using cg1_e IH cg_b wf_B by blast
    qed
  qed
qed
  
lemma subsumption: "\<forall> v1 v2 \<rho>. subsump v1 v2 e \<rho>"
proof (induction e)
  case (EVar x)
  show ?case
    apply clarify
    apply (case_tac "x < length \<rho>") defer apply force
    apply simp apply (rule sub_trans) apply auto done
next
  case (ENat n)
  then show ?case apply auto
    using sub_trans apply blast done
next
  case (ELam e)
  show ?case
      apply clarify apply simp
       apply (rule subsumption_fun) apply blast apply blast apply blast 
         apply blast apply blast using ELam.IH deterministic apply auto done
next
  case (EApp e1 e2)
  show ?case
    apply clarify apply simp apply clarify
  proof -
    fix v1::ty and v2 \<rho> f v assume v1_v2: "v1 <: v2" and 
      wf_v1: "wf_ty v1" and wf_v2: "wf_ty v2" and wf_r: "wf_env \<rho>" and
      f_e1: "f \<in> \<lbrakk>e1\<rbrakk>\<rho>" and v_e2: "v \<in> \<lbrakk>e2\<rbrakk>\<rho>" and f_vv1: "f <: v \<rightarrow> v1" 
    have "v \<rightarrow> v1 <: v \<rightarrow> v2" using v1_v2 by blast
    then have "f <: v \<rightarrow> v2" using f_vv1 sub_trans by blast
    then show "\<exists>f. f \<in> \<lbrakk>e1\<rbrakk>\<rho> \<and> (\<exists>v. v \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> f <: v \<rightarrow> v2)" 
      using f_e1 v_e2 by blast
  qed
next
  case (EPrim f e1 e2)
  show ?case apply simp by (meson sub_trans)
next
  case (EIf e1 e2 e3)
  show ?case apply simp by (meson EIf.IH(2) EIf.IH(3))
qed  

(*<*)
end
(*>*)
