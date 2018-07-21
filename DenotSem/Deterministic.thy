theory Deterministic
  imports Consistency Denot
begin

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
      
  obtain \<Gamma>1 where g1_ne: "\<Gamma>1 \<noteq> []" and af_g1: "all_funs (set \<Gamma>1)" and g1_f1: "set \<Gamma>1 \<subseteq> atoms f1" and
    v1_g1: "\<forall>v v'. v\<rightarrow>v' \<in> set \<Gamma>1 \<longrightarrow> v1 <: v" and g1_v1p: "\<Sqinter>(map cod \<Gamma>1) <: v1'"
    using f1_v11 sub_fun_any_inv_atoms[of f1 v1 v1'] by blast
  let ?C1 = "map cod \<Gamma>1"     
  obtain \<Gamma>2 where g2_ne: "\<Gamma>2 \<noteq> []" and af_g2: "all_funs (set \<Gamma>2)" and g2_f2: "set \<Gamma>2 \<subseteq> atoms f2" and
    v2_g2: "\<forall>v v'. v\<rightarrow>v' \<in> set \<Gamma>2 \<longrightarrow> v2 <: v" and g2_v2p: "\<Sqinter>(map cod \<Gamma>2) <: v2'"
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
    obtain d1 where v11_g1: "d1\<rightarrow>v1' \<in> set \<Gamma>1" using v1_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v1'] by blast
    obtain d2 where v22_g1: "d2\<rightarrow>v2' \<in> set \<Gamma>1" using v2_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v2'] by blast        
    show "v1' ~ v2'"
      apply (rule consis_codomain[of d1 v1' \<Gamma>1 d2 v2' \<Gamma>1 v1 v1 f1 f1])
      using v11_g1 v22_g1 v1_g1 consis_refl wf_v1 wf_f1 g1_f1 by auto   
  qed
  have c_c2: "\<forall>v1' v2'. {v1',v2'} \<subseteq> set ?C2 \<longrightarrow> v1' ~ v2'"
  proof clarify
    fix v1' v2' assume 1: "{v1',v2'} \<subseteq> set ?C2"        
    have v1_c1: "v1' \<in> set ?C2" using 1 by blast 
    have v2_c1: "v2' \<in> set ?C2" using 1 by blast
    obtain d1 where v11_g2: "d1\<rightarrow>v1' \<in> set \<Gamma>2" using v1_c1 af_g2 all_fun_ex_dom[of \<Gamma>2 v1'] by blast
    obtain d2 where v22_g2: "d2\<rightarrow>v2' \<in> set \<Gamma>2" using v2_c1 af_g2 all_fun_ex_dom[of \<Gamma>2 v2'] by blast        
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
        obtain d1 where v11_g1: "d1\<rightarrow>v1' \<in> set \<Gamma>1" using v1_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v1'] by blast
        obtain d2 where v22_g2: "d2\<rightarrow>v2' \<in> set \<Gamma>2" using v2_c2 af_g2 all_fun_ex_dom[of \<Gamma>2 v2'] by blast        
        have "v1' ~ v2'" 
          apply (rule consis_codomain)
          using v11_g1 apply blast using v22_g2 apply blast using v1_g1 apply blast
          using v2_g2 apply blast using v1_v2 apply blast using f1_f2 apply blast
          using g1_f1 apply blast using g2_f2 apply blast done          
      } moreover {
        assume v1_c2: "v1' \<in> set ?C2" and v2_c1: "v2' \<in> set ?C1"
        obtain d1 where v11_g2: "d1\<rightarrow>v1' \<in> set \<Gamma>2" using v1_c2 af_g2 all_fun_ex_dom[of \<Gamma>2 v1'] by blast
        obtain d2 where v22_g1: "d2\<rightarrow>v2' \<in> set \<Gamma>1" using v2_c1 af_g1 all_fun_ex_dom[of \<Gamma>1 v2'] by blast        
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

lemma weaken_env_fun_aux: "\<lbrakk> F v e \<rho>1; \<rho>2 <: \<rho>1; (\<forall> v \<rho>1 \<rho>2. v \<in> \<lbrakk>e\<rbrakk>\<rho>1 \<longrightarrow> \<rho>2 <: \<rho>1 \<longrightarrow> v \<in> \<lbrakk>e\<rbrakk>\<rho>2) \<rbrakk>
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

lemma denot_fun_atoms: "\<lbrakk> all_funs (atoms v); \<forall>v1 v2. v1\<rightarrow>v2 \<in> atoms v \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>v1#\<rho> \<rbrakk>
   \<Longrightarrow> F v e \<rho>"
  by (induction v) auto    

lemma denot_fun_inv_atoms: "F v e \<rho> \<Longrightarrow> all_funs (atoms v) 
   \<and> (\<forall>v1 v2. v1\<rightarrow>v2 \<in> atoms v \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>v1#\<rho>)"
  apply (induction v) apply auto done
    
lemma eval_fun_all_funs: "F v e \<rho> \<Longrightarrow> all_funs (atoms v)"
  apply (induction v) apply auto done

abbreviation subsump :: "ty \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> bool" where
  "subsump v1 v2 e \<rho> \<equiv> v1 \<in> \<lbrakk>e\<rbrakk>\<rho> \<longrightarrow> v1 <: v2 \<longrightarrow> wf_ty v2 \<longrightarrow> wf_env \<rho> \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>\<rho>" 

abbreviation determ :: "ty \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "determ v1 v2 e \<rho>1 \<rho>2 \<equiv> v1\<in> \<lbrakk>e\<rbrakk>\<rho>1 \<longrightarrow> v2\<in> \<lbrakk>e\<rbrakk>\<rho>2 \<longrightarrow> wf_env \<rho>1 \<longrightarrow> wf_env \<rho>2 \<longrightarrow> consis_env \<rho>1 \<rho>2
    \<longrightarrow> v1 \<sqinter> v2 \<in> \<lbrakk>e\<rbrakk>(\<rho>1\<sqinter>\<rho>2) \<and> wf_ty (v1 \<sqinter> v2)"

lemma fun_eval_distr_determ:
  "\<lbrakk> F (A \<rightarrow> B \<sqinter> C \<rightarrow> D) e \<rho>; \<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2; wf_env \<rho>; wf_ty A; wf_ty C; A ~ C \<rbrakk>
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
  apply (subgoal_tac "B \<sqinter> D \<in> \<lbrakk>e\<rbrakk>((A \<sqinter> C) # \<rho>) \<sqinter> ((A \<sqinter> C) # \<rho>)") prefer 2 apply blast
  apply (subgoal_tac "(A \<sqinter> C) # \<rho> <: ((A \<sqinter> C) # \<rho>) \<sqinter> ((A \<sqinter> C) # \<rho>)") prefer 2
   apply simp apply clarify apply (case_tac k) prefer 2 apply force
    apply simp 
  apply blast
  apply (rule weaken_env)    
   apply blast
    apply blast
  done
 
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
 
lemma denot_fun_fold_meet:
  "\<lbrakk> F (fold op \<sqinter> L (A\<rightarrow>B)) e \<rho>; all_funs (set L); wf_env \<rho>; wf_ty A; wf_ty B;
     wf_list L; consis_funs ((A\<rightarrow>B)#L);
     \<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2 \<rbrakk> \<Longrightarrow> 
    F ((fold op \<sqinter> (map dom L) A) \<rightarrow> (fold op \<sqinter> (map cod L) B)) e \<rho>"
  apply (induction L arbitrary: A B)
   apply force
   apply (case_tac a) apply force defer apply force
  apply (rename_tac A' B') apply clarify    
  apply (subgoal_tac "F (fold op \<sqinter> L ((A'\<sqinter>A) \<rightarrow> (B' \<sqinter> B))) e \<rho>") prefer 2
   apply (rule denot_fold_meet_swap_init)
    apply force
   apply (rule fun_eval_distr_determ)
   apply (subgoal_tac "F (A' \<rightarrow> B' \<sqinter> A \<rightarrow> B) e \<rho>") prefer 2
         apply (rule denot_fold_meet_inv_init)
         apply force
   apply assumption apply assumption apply assumption 
   apply force
    apply assumption
  apply (metis bot_least consis_sym insert_mono list.set(2))
  apply (subgoal_tac "wf_ty (A'\<sqinter>A)") 
   apply (subgoal_tac "wf_ty (B'\<sqinter>B)")
   apply (subgoal_tac "\<forall>v1 v1' v2 v2'. {v1\<rightarrow>v1',v2\<rightarrow>v2'} \<subseteq> insert ((A'\<sqinter>A)\<rightarrow>(B'\<sqinter>B)) (set L) \<longrightarrow> v1 ~ v2 \<and> v1' ~ v2'")
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
   consis_funs L; wf_list L;
   \<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2 \<rbrakk> 
  \<Longrightarrow> F (\<Sqinter>(map dom L) \<rightarrow> \<Sqinter>(map cod L)) e \<rho>"
  apply (cases L) apply force
  unfolding meet_list_def apply clarify
  apply (case_tac a) apply force defer apply force apply simp
  apply (subgoal_tac "wf_ty x21") prefer 2 apply blast
  apply (subgoal_tac "wf_ty x22") prefer 2 apply blast    
    using denot_fun_fold_meet apply simp 
  done
    
lemma subsumption_fun: fixes v1::ty and v2::ty
  assumes v1_e: "F v1 e \<rho>" and v1_v2: "v1 <: v2" and
    wf_v1: "wf_ty v1"  and wf_v2: "wf_ty v2" and wf_r: "wf_env \<rho>" and
    IH: "\<forall>v1 v2 \<rho>. subsump v1 v2 e \<rho>" and
    D: "\<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2"
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
        using denot_fun_meet_list D af_g g_ne wf_r c_g1 wf_g1 by blast
      then have cg1_e: "\<Sqinter> (map cod \<Gamma>1) \<in> \<lbrakk>e\<rbrakk>(\<Sqinter> (map dom \<Gamma>1))#\<rho>" by simp
      have "A#\<rho> <: (\<Sqinter> (map dom \<Gamma>1))#\<rho>" using a_dg apply auto apply (case_tac k) apply auto done
      then have cg1_e: "\<Sqinter> (map cod \<Gamma>1) \<in> \<lbrakk>e\<rbrakk>A#\<rho>" using cg1_e weaken_env by blast
      have "wf_ty A" using wf_v2 ab_v2 wf_ty_arrow_inv by blast
      then have "wf_env (A#\<rho>)" using wf_r apply auto apply (case_tac k) apply auto done
      then show ?thesis using cg1_e IH cg_b wf_B by blast
    qed
  qed
qed
  
lemma subsumption_deterministic:
  "(\<forall> v1 v2 \<rho>. subsump v1 v2 e \<rho>) \<and> (\<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2)"
proof (induction)
  case (EVar x)
  show ?case
  proof
    show "\<forall>v1 v2 \<rho>. subsump v1 v2 (EVar x) \<rho>" apply clarify
      apply (case_tac "x < length \<rho>") defer apply force
      apply simp apply (rule sub_trans) apply auto done
  next
    show "\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 (EVar x) \<rho>1 \<rho>2" apply clarify
      apply (case_tac "x < length \<rho>1") defer apply force
      using consis_le inter_func by auto
  qed
next
  case (ENat n)
  then show ?case apply auto
    using sub_trans apply blast
    by (simp add: consis_le inter_func)      
next
  case (ELam e)
  show ?case
  proof
    show "\<forall>v1 v2 \<rho>. subsump v1 v2 (\<lambda> e) \<rho>" 
      apply clarify apply simp
       apply (rule subsumption_fun) apply blast apply blast apply blast 
         apply blast apply blast using ELam.IH apply auto done
  next
    show "\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 (\<lambda> e) \<rho>1 \<rho>2 " apply (rule allI)+ apply (rule impI)+
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
          by (metis a1_v1 atoms_not_inter denot_fun_inv_atoms ty.simps(10) wf_atoms wf_ty.simps wf_v1)
        obtain A21 A22 where a2: "A2=A21\<rightarrow>A22" and a22_e: "A22 \<in> \<lbrakk>e\<rbrakk>A21#\<rho>2" using f_v2_e_r2 
          by (metis a2_v2 atoms_not_inter denot_fun_inv_atoms ty.simps(10) wf_atoms wf_ty.simps wf_v2)
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
  qed
next
  case (EApp e1 e2)
  show ?case
  proof
    show "\<forall>v1 v2 \<rho>. subsump v1 v2 (EApp e1 e2) \<rho>"
      apply clarify apply simp apply clarify
    proof -
      fix v1::ty and v2 \<rho> f v assume v1_v2: "v1 <: v2" and wf_v2: "wf_ty v2" and wf_r: "wf_env \<rho>" and
        f_e1: "f \<in> \<lbrakk>e1\<rbrakk>\<rho>" and v_e2: "v \<in> \<lbrakk>e2\<rbrakk>\<rho>" and f_vv1: "f <: v \<rightarrow> v1" and wf_v1: "wf_ty v1"
      have "v \<rightarrow> v1 <: v \<rightarrow> v2" using v1_v2 by blast
      then have "f <: v \<rightarrow> v2" using f_vv1 sub_trans by blast
      then show "\<exists>f. f \<in> \<lbrakk>e1\<rbrakk>\<rho> \<and> (\<exists>v. v \<in> \<lbrakk>e2\<rbrakk>\<rho> \<and> f <: v \<rightarrow> v2)" 
        using f_e1 v_e2 by blast
    qed
  next
    show "\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 (EApp e1 e2) \<rho>1 \<rho>2 "
      apply (rule allI)+ apply (rule impI)+
    proof -
      fix v1 v2 \<rho>1 \<rho>2 assume v1_e1e2: "v1 \<in> \<lbrakk>EApp e1 e2\<rbrakk>\<rho>1" and v2_e1e2: "v2 \<in> \<lbrakk>EApp e1 e2\<rbrakk>\<rho>2" and
        wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and c_r1_r2: "consis_env \<rho>1 \<rho>2"
      obtain f1 v21 where f1_e1: "f1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v21_e2: "v21\<in> \<lbrakk>e2\<rbrakk>\<rho>1" and f1_v21: "v1 \<in> f1 \<bullet> v21" 
        using v1_e1e2 by auto
      obtain f2 v22 where f2_e1: "f2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v22_e2: "v22\<in> \<lbrakk>e2\<rbrakk>\<rho>2" and f2_v22: "v2 \<in> f2 \<bullet> v22" 
        using v2_e1e2 by auto
      have "determ f1 f2 e1 \<rho>1 \<rho>2" using EApp(1) by blast
      then have f12_e1: "f1 \<sqinter> f2 \<in> \<lbrakk>e1\<rbrakk>\<rho>1\<sqinter>\<rho>2" and wf_f12: "wf_ty (f1 \<sqinter> f2)"         
        using f1_e1 f2_e1 wf_r1 wf_r2 c_r1_r2 by auto
      have "determ v21 v22 e2 \<rho>1 \<rho>2" using EApp(2) by blast
      then have v22_e2: "v21 \<sqinter> v22 \<in> \<lbrakk>e2\<rbrakk>\<rho>1\<sqinter>\<rho>2" and wf_v21_v22: "wf_ty (v21 \<sqinter> v22)"
        using v21_e2 v22_e2 wf_r1 wf_r2 c_r1_r2 by auto
      have f12_v21_v22: "v1 \<sqinter> v2 \<in> (f1 \<sqinter> f2) \<bullet> (v21 \<sqinter> v22)"
        using inter_app[of v1 f1 v21 v2 f2 v22] f1_v21 f2_v22 wf_f12 wf_v21_v22 
        by (metis CollectD consis_le consistent.simps(4) wf_ty_inter_inv)
      have v1_v2: "v1 ~ v2"
        using consistent_app[of f1 f2 v21 v22 v1 v2] wf_f12 wf_v21_v22 f1_v21 f2_v22 by blast
      have wf_v1: "wf_ty v1" using f1_v21 by blast
      have wf_v2: "wf_ty v2" using f2_v22 by blast
      show "v1 \<sqinter> v2 \<in> \<lbrakk>EApp e1 e2\<rbrakk>\<rho>1 \<sqinter> \<rho>2 \<and> wf_ty (v1 \<sqinter> v2)"
        using f12_e1 v22_e2 v1_v2 wf_v1 wf_v2 v1_v2 f12_v21_v22 by auto
    qed      
  qed    
next
  case (EPrim f e1 e2)
  show ?case 
  proof
    show "\<forall>v1 v2 \<rho>. subsump v1 v2 (EPrim f e1 e2) \<rho>" apply simp by (meson sub_trans)
  next
    show "\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 (EPrim f e1 e2) \<rho>1 \<rho>2" 
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
  qed
next
  case (EIf e1 e2 e3)
  then show ?case sorry
qed  

(*
lemma strengthen_env: "\<lbrakk> v1 \<in> \<lbrakk>e\<rbrakk>\<rho>1; \<rho>2 <: \<rho>1; wf_env \<rho>1; wf_env \<rho>2 \<rbrakk> \<Longrightarrow>
    \<exists>v2. v2 \<in> \<lbrakk>e\<rbrakk>\<rho>2 \<and> v2 <: v1 \<and> wf_ty v2"
proof (induction e arbitrary: v1 \<rho>1 \<rho>2)
  case (EVar x)
  then show ?case by (cases "x < length \<rho>1") auto
next
  case (ENat x)
  then show ?case by auto
next
  case (ELam e)
  have wf_v1: "wf_fun v1" and v1_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)"
    using ELam.prems(1) by auto    
  
  { fix v v' assume vv_v1: "v\<rightarrow>v' \<in> atoms v1"
    have vp_e: "v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)" using vv_v1 v1_e by blast
    have vr2_vr1: "v#\<rho>2 <: v#\<rho>1" using ELam.prems(2) apply auto apply (case_tac k) by auto
    have wf_v: "wf_ty v" using vv_v1 wf_v1 using wf_atoms by blast
    have wf_vr1: "wf_env (v#\<rho>1)" using wf_v ELam.prems(3) apply auto apply (case_tac k) by auto
    have wf_vr2: "wf_env (v#\<rho>2)" using wf_v ELam.prems(4) apply auto apply (case_tac k) by auto
    obtain v2 where v2_e: "v2 \<in> \<lbrakk>e\<rbrakk>(v#\<rho>2)" and v2_vp: "v2 <: v'" and wf_v2: "wf_ty v2"
      using ELam.IH[of v' "v#\<rho>1" "v#\<rho>2"] vp_e vr2_vr1 wf_vr1 wf_vr2 by blast
    have "True" ..
  }  
  
    
  show ?case sorry
next
  case (EApp e1 e2)
  obtain f v where f_e1: "f \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v_e2: "v \<in> \<lbrakk>e2\<rbrakk>\<rho>1" and f_v: "v1 \<in> f \<bullet> v"
    using EApp.prems(1) by auto
  obtain f' where fp_e1: "f' \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and fp_f: "f' <: f" and wf_fp: "wf_ty f'"
    using EApp.IH(1)[of f \<rho>1 \<rho>2] f_e1 EApp.prems by blast
  obtain v2 where v2_e2: "v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and v2_v: "v2 <: v" and wf_v2: "wf_ty v2"
    using EApp.IH(2)[of v \<rho>1 \<rho>2] v_e2 EApp.prems by blast
  note fp_f
  also have "f <: v \<rightarrow> v1" using f_v by simp
  also have "v \<rightarrow> v1 <: v2 \<rightarrow> v1" using v2_v by (simp add: sub_arrow)
  finally have fp_v2v1: "f' <: v2 \<rightarrow> v1" by blast
  have wf_v1: "wf_ty v1" using EApp.prems(1) wf_eval EApp.prems(3) by blast  
  show ?case using fp_e1 v2_e2 fp_v2v1 wf_v1 by auto
next
  case (EPrim f e1 e2)
  obtain n1 n2 where n1_e1_r1: "TNat n1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and n2_e2_r1: "TNat n2 \<in> \<lbrakk>e2\<rbrakk>\<rho>1"
    and v1: "v1 = TNat (f n1 n2)" using EPrim(3) by auto
  obtain v2 where v2_n1: "v2 <: TNat n1" and wf_v2: "wf_ty v2" and v2_e1_r2: "v2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2"
    using EPrim.IH(1)[of "TNat n1" \<rho>1 \<rho>2] EPrim.prems n1_e1_r1 by blast
  obtain v3 where v3_n2: "v3 <: TNat n2" and wf_v3: "wf_ty v3" and v3_e2_r2: "v3 \<in> \<lbrakk>e2\<rbrakk>\<rho>2"
    using EPrim.IH(2)[of "TNat n2" \<rho>1 \<rho>2] EPrim.prems n2_e2_r1 by blast
  have v2: "v2 = TNat n1" using v2_n1 wf_v2 
    by (metis consis_le consis_refl consistent.simps(7) merge.simps(1) merge_inter sub_refl ty_equiv_def)
  have v3: "v3 = TNat n2" using v3_n2 wf_v3
    by (metis consis_le consis_refl consistent.simps(7) merge.simps(1) merge_inter sub_refl ty_equiv_def)           
  show ?case using v2 v3 v2 v2_e1_r2 v3_e2_r2 v1 v2 by auto
next
  case (EIf e1 e2 e3)
  obtain n where n_e1: "TNat n \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v1_e3: "n=0\<longrightarrow> v1 \<in> \<lbrakk>e3\<rbrakk>\<rho>1" and 
    v1_e2: "n\<noteq>0 \<longrightarrow> v1 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" using EIf.prems(1) by auto
  obtain v2 where v2_n: "v2 <: TNat n" and wf_v2: "wf_ty v2" and v2_e1_r2: "v2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2"
    using EIf.IH(1)[of "TNat n" \<rho>1 \<rho>2] EIf.prems n_e1 by blast
  have v2: "v2 = TNat n" using v2_n wf_v2
    by (metis consis_le consis_refl consistent.simps(7) merge.simps(1) merge_inter sub_refl ty_equiv_def) 
  show ?case
  proof (cases "n = 0")
    case True
    from EIf.IH(3)[of v1 \<rho>1 \<rho>2] EIf.prems v1_e3 True
    obtain v3 where v3_e3: "v3 \<in> \<lbrakk>e3\<rbrakk>\<rho>2" and v3_v1: "v3 <: v1" and wf_v3: "wf_ty v3" by blast        
    then show ?thesis using True v2_e1_r2 v2 by auto
  next
    case False
    from EIf.IH(2)[of v1 \<rho>1 \<rho>2] EIf.prems v1_e2 False
    obtain v3 where v3_e2: "v3 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and v3_v1: "v3 <: v1" and wf_v3: "wf_ty v3" by blast        
    then show ?thesis using False v2_e1_r2 v2 by auto
  qed
qed
*)

(*  
theorem deterministic:
  "\<lbrakk> v1 \<in> E e \<rho>1; v2 \<in> E e \<rho>2; wf_env \<rho>1; wf_env \<rho>2; consis_env \<rho>1 \<rho>2 \<rbrakk>
   \<Longrightarrow> v1 ~ v2 \<and> merge v1 v2 \<in> \<lbrakk>e\<rbrakk>(\<rho>1 \<sqinter> \<rho>2)"
proof (induction e arbitrary: v1 v2 \<rho>1 \<rho>2)    
  case (EVar x)
  have xr1: "x < length \<rho>1" using EVar(1) by (case_tac "x < length \<rho>1") auto
  have xr2: "x < length \<rho>2" using EVar(2) by (case_tac "x < length \<rho>2") auto
  have v1: "v1 = \<rho>1!x" using xr1 EVar(1) by auto
  have v2: "v2 = \<rho>2!x" using xr2 EVar(2) by auto
  have v1_v2: "v1 ~ v2" using EVar xr1 xr2 by auto 
  have v_v1: "wf_ty v1" using EVar(1) EVar(3) xr1 by auto
  have v_v2: "wf_ty v2" using EVar(2) EVar(4) xr2 by auto
  have r3x: "merge v1 v2 = (\<rho>1 \<sqinter> \<rho>2)!x" 
    using v1 v2 consis_env_inter[of \<rho>1 \<rho>2 x] EVar(5) xr1 by simp
  have xr3: "x < length (\<rho>1 \<sqinter> \<rho>2)" using inter_env_length xr1 EVar(5) by simp
  have v12_e: "merge v1 v2 \<in> \<lbrakk>EVar x\<rbrakk>(\<rho>1 \<sqinter> \<rho>2)" using r3x xr3 by simp
  show ?case using v1_v2 v12_e by simp
next
  case (ENat n)
  have v1: "v1 = TNat n" using ENat(1) by simp
  have v2: "v2 = TNat n" using ENat(2) by simp
  have m: "merge v1 v2 = TNat n" using v1 v2 by simp
  show ?case using m v1 v2 by simp
next
  case (ELam e)
  have wf_v1: "wf_fun v1" and v1_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)" using ELam(2) by auto
  have wf_v2: "wf_fun v2" and v2_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v2 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>2)" using ELam(3) by auto
  
  have v12: "merge v1 v2 = v1 \<sqinter> v2"
    using wf_v1 wf_v2 by (metis merge.simps(4) merge.simps(5) wf_fun_inv)

  have v1_v2: "v1 ~ v2" apply (rule atoms_consis) using wf_v1 wf_v2 apply auto
  proof -
    fix a1 a2
    assume a1_v1: "a1 \<in> atoms v1" and a2_v2: "a2 \<in> atoms v2"
    obtain a11 a12 where a1: "a1=a11\<rightarrow>a12" using a1_v1 wf_v1 atoms_wf_fun by blast
    obtain a21 a22 where a2: "a2=a21\<rightarrow>a22" using a2_v2 wf_v2 atoms_wf_fun by blast
    show "a1 ~ a2"
    proof (cases "a11 ~ a21")
      case True
      have a12_e: "a12 \<in> \<lbrakk>e\<rbrakk>(a11#\<rho>1)" using v1_e a1_v1 a1 by simp
      have a22_e: "a22 \<in> \<lbrakk>e\<rbrakk>(a21#\<rho>2)" using v2_e a2_v2 a2 by simp
      have wf_r1: "wf_env (a11 # \<rho>1)"
        using ELam(4) wf_v1 a1_v1 apply simp apply clarify apply (case_tac k)
          apply simp 
         apply (metis a1 fun_wf_ty wf_arrow_inv wf_atoms wf_ty_arrow_inv)
          apply simp done
      have wf_r2: "wf_env (a21 # \<rho>2)" 
        using ELam(5) wf_v2 a2_v2 apply simp apply clarify apply (case_tac k)
          apply simp 
         apply (metis a2 fun_wf_ty wf_arrow_inv wf_atoms wf_ty_arrow_inv)
          apply simp done
      have c_r12: "consis_env (a11 # \<rho>1) (a21 # \<rho>2)" 
        using ELam(6) True apply simp apply clarify apply (case_tac k)
          apply simp apply simp done
      have "a12 ~ a22"
        using ELam.IH[of a12 "a11#\<rho>1" a22 "a21#\<rho>2"] a12_e a22_e wf_r1 wf_r2 c_r12 by blast
      then show ?thesis using True a1 a2 by simp
    next
      case False
      then show ?thesis using a1 a2 by simp
    qed
  qed
  have v12_l: "merge v1 v2 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>1 \<sqinter> \<rho>2" apply simp
  proof
    show "wf_fun (merge v1 v2)"
      using wf_v1 wf_v2 v1_v2 by (simp add: inter_func v12)
  next
    show " \<forall>v v'. v \<rightarrow> v' \<in> atoms (merge v1 v2) \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>v # (\<rho>1 \<sqinter> \<rho>2)"
    proof clarify
      fix v v' assume vv_v12: "v \<rightarrow> v' \<in> atoms (merge v1 v2)"
      have "v\<rightarrow>v' \<in> atoms v1 \<or> v\<rightarrow>v' \<in> atoms v2" using v12 vv_v12 by simp        
      then show "v' \<in> \<lbrakk>e\<rbrakk>v # (\<rho>1 \<sqinter> \<rho>2)"
      proof
        assume vv_v1: "v\<rightarrow>v' \<in> atoms v1"
        have vp_e_r1: "v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)" using vv_v1 v1_e by blast
            
        show ?thesis sorry
      next
        assume vv_v2: "v\<rightarrow>v' \<in> atoms v2"
        have vp_e_r2: "v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>2)" using vv_v2 v2_e by blast
          
        show ?thesis sorry
      qed
    qed
  qed
  show ?case using v1_v2 v12_l by simp
next
  case (EApp e1 e2 v1' v2')
  obtain f1 v1 where f1_e1: "f1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v1_e2: "v1 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" and v1p_f1_v1: "v1' \<in> f1 \<bullet> v1"
    using EApp(3) by auto
  obtain f2 v2 where f2_e1: "f2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v2_e2: "v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and v2p_f2_v2: "v2' \<in> f2 \<bullet> v2"
    using EApp(4) by auto
  have f1_f2: "f1 ~ f2" using EApp.IH(1) f1_e1 f2_e1 EApp(5) EApp(6) EApp(7) by blast
  have m_f1f2: "merge f1 f2 \<in> \<lbrakk>e1\<rbrakk>(\<rho>1\<sqinter>\<rho>2)" using EApp.IH(1) f1_e1 f2_e1 EApp(5) EApp(6) EApp(7) by blast
  have v1_v2: "v1 ~ v2" using EApp.IH(2) v1_e2 v2_e2 EApp(5) EApp(6) EApp(7) by blast
  have m_v12: "merge v1 v2 \<in> \<lbrakk>e2\<rbrakk>(\<rho>1\<sqinter>\<rho>2)" using EApp.IH(2) v1_e2 v2_e2 EApp(5) EApp(6) EApp(7) by blast
  have wf_f1: "wf_ty f1" using f1_e1 wf_eval EApp(5) by blast
  have wf_f2: "wf_ty f2" using f2_e1 wf_eval EApp(6) by blast
  have wf_v1: "wf_ty v1" using v1_e2 wf_eval EApp(5) by blast
  have wf_v2: "wf_ty v2" using v2_e2 wf_eval EApp(6) by blast
  have v1p_v2p: "v1' ~ v2'"
    using f1_f2 v1_v2 v1p_f1_v1 v2p_f2_v2 wf_f1 wf_f2 wf_v1 wf_v2 consistent_app by blast
  have m_v12p_f12_v12: "merge v1' v2' \<in> (merge f1 f2) \<bullet> (merge v1 v2)"
    using v1p_f1_v1 v2p_f2_v2 f1_f2 v1_v2 v1p_v2p inter_app by blast
  show ?case using v1p_v2p m_v12p_f12_v12 m_f1f2 m_v12 by auto
next
  case (EPrim f e1 e2)
  obtain n1 n2 where n1_e1: "TNat n1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and n2_e2: "TNat n2 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" and 
    v1: "v1 = TNat (f n1 n2)" using EPrim(3) by auto
  obtain n3 n4 where n3_e1: "TNat n3 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and n4_e2: "TNat n4 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and
    v2: "v2 = TNat (f n3 n4)" using EPrim(4) by auto
  have n1_n3: "n1 = n3" 
    using EPrim.IH(1)[of "TNat n1" \<rho>1 "TNat n3" \<rho>2] n1_e1 n3_e1 EPrim.prems by auto
  have n13_e1: "merge (TNat n1) (TNat n3) \<in> \<lbrakk>e1\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
    using EPrim.IH(1)[of "TNat n1" \<rho>1 "TNat n3" \<rho>2] n1_e1 n3_e1 EPrim.prems by auto
  have n2_n4: "n2 = n4" 
    using EPrim.IH(2)[of "TNat n2" \<rho>1 "TNat n4" \<rho>2] n2_e2 n4_e2 EPrim.prems by auto
  have n24_e2: "merge (TNat n2) (TNat n4) \<in> \<lbrakk>e2\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
    using EPrim.IH(2)[of "TNat n2" \<rho>1 "TNat n4" \<rho>2] n2_e2 n4_e2 EPrim.prems by auto      
  then show ?case using n1_n3 n2_n4 v1 v2 n13_e1 n24_e2 by auto      
next
  case (EIf e1 e2 e3)
  obtain n1 where n1_e1: "TNat n1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v1_e3: "n1 = 0 \<longrightarrow> v1 \<in> \<lbrakk>e3\<rbrakk>\<rho>1" and
    v1_e2: "n1 \<noteq> 0 \<longrightarrow> v1 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" using EIf(4) by auto
  obtain n2 where n2_e1: "TNat n2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v2_e3: "n2 = 0 \<longrightarrow> v2 \<in> \<lbrakk>e3\<rbrakk>\<rho>2" and
    v2_e2: "n2 \<noteq> 0 \<longrightarrow> v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" using EIf(5) by auto
  have n1_n2: "n1 = n2"
    using EIf.IH(1)[of "TNat n1" \<rho>1 "TNat n2" \<rho>2] n1_e1 n2_e1 EIf.prems by auto
  have n12_e1: "merge (TNat n1) (TNat n2) \<in> \<lbrakk>e1\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
    using EIf.IH(1)[of "TNat n1" \<rho>1 "TNat n2" \<rho>2] n1_e1 n2_e1 EIf.prems by auto
  show ?case
  proof (cases "n1 = 0")
    case True
    have v1_v2: "v1 ~ v2"
      using EIf.IH(3)[of v1 \<rho>1 v2 \<rho>2] v1_e3 v2_e3 EIf.prems True n1_n2 by auto
    have "merge v1 v2 \<in> \<lbrakk>e3\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
      using EIf.IH(3)[of v1 \<rho>1 v2 \<rho>2] v1_e3 v2_e3 EIf.prems True n1_n2 by auto
    then show ?thesis using v1_v2 n1_n2 True n12_e1 by auto
  next
    case False
    have v1_v2: "v1 ~ v2"
      using EIf.IH(2)[of v1 \<rho>1 v2 \<rho>2] v1_e2 v2_e2 EIf.prems False n1_n2 by auto
    have "merge v1 v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
      using EIf.IH(2)[of v1 \<rho>1 v2 \<rho>2] v1_e2 v2_e2 EIf.prems False n1_n2 by auto
    then show ?thesis using v1_v2 n1_n2 False n12_e1 by auto
  qed    
qed
*)
(*
abbreviation strengthen :: "ty \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "strengthen v1 v2 e \<rho>1 \<rho>2 \<equiv> (v1 \<in> \<lbrakk>e\<rbrakk>\<rho>1 \<and> \<rho>2 <: \<rho>1 \<and> v1 <: v2
                               \<and> wf_ty v2 \<and> wf_env \<rho>1 \<and> wf_env \<rho>2
                               \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>\<rho>2)"

abbreviation determ :: "ty \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "determ v1 v2 e \<rho>1 \<rho>2 \<equiv> (v1 \<in> E e \<rho>1 \<and> v2 \<in> E e \<rho>2 \<and> wf_env \<rho>1 \<and> wf_env \<rho>2 \<and> consis_env \<rho>1 \<rho>2 
   \<longrightarrow> v1 ~ v2 \<and> merge v1 v2 \<in> \<lbrakk>e\<rbrakk>(\<rho>1 \<sqinter> \<rho>2))"

lemma strengthen_env_fun:
  fixes \<rho>1::"ty list" and \<rho>2::"ty list" and v1::ty and v2::ty 
  assumes str: "\<forall> v1 v2 \<rho>1 \<rho>2. strengthen v1 v2 e \<rho>1 \<rho>2" and 
    det: "\<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2" and
    r2_r1: "\<rho>2 <: \<rho>1" and
    wf_v1: "wf_fun v1" and wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and
    v1_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)" and
    v1_v2: "v1 <: v2" and wf_v2: "wf_fun v2"  
  shows "\<forall>v v'. v\<rightarrow>v' \<in> atoms v2 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>2)"
    using str det r2_r1 wf_v1 wf_r1 wf_r2 v1_e v1_v2 wf_v2
proof (induction v1 arbitrary: \<rho>1 \<rho>2 v2)
  case (TNat n)
  then have "False" by auto
  then show ?case ..
next
  case (TArrow v11 v12)
  have v12_e: "v12 \<in> \<lbrakk>e\<rbrakk>(v11#\<rho>1)" using TArrow.prems(7) by auto
  have wf_v11: "wf_ty v11" using TArrow using wf_atoms by blast
  show ?case
  proof clarify
    fix v v' assume vv_v2: "v\<rightarrow>v' \<in> atoms v2"
    have wf_v: "wf_ty v" using TArrow.prems(9) vv_v2 wf_atoms by blast
    have wf_vp: "wf_ty v'" using TArrow.prems(9) vv_v2 wf_atoms by blast
    have v_v11: "v <: v11" and v12_vp: "v12 <: v'" 
      using vv_v2 TArrow.prems(8) sub_any_fun_inv_atoms[of v11 v12 v2] by auto
    have wf_v11r1: "wf_env (v11 # \<rho>1)" using wf_v11 TArrow(7) by (simp add: nth_Cons') 
    have wf_vr2: "wf_env (v # \<rho>2)" using wf_v TArrow(8) by (simp add: nth_Cons')
    from TArrow.prems(1) v12_e
    show "v' \<in> \<lbrakk>e\<rbrakk>v#\<rho>2" 
      apply simp apply (erule_tac x=v12 in allE)
      apply (erule_tac x=v' in allE) apply (erule_tac x="v11#\<rho>1" in allE)
      apply (erule_tac x="v#\<rho>2" in allE) apply (erule impE) prefer 2 apply assumption
      apply (rule conjI) apply assumption
        apply (rule conjI) 
       apply (simp add: TArrow.prems(3))
      apply (rule conjI) apply clarify apply (case_tac k) apply simp using v_v11 apply blast
      using TArrow.prems(3) apply auto[1]
      apply (rule conjI) using v12_vp apply blast 
      apply (rule conjI) using wf_vp apply blast
      apply (rule conjI) using wf_v11r1 apply blast
        using wf_vr2 by blast
  qed    
next
  case (TInter f11 f12)
(*
  from TInter.IH(1)[of \<rho>2 \<rho>1] obtain f21 where f21_f11: "f21 <: f11" and wf_f21: "wf_fun f21"
    and f21_e: "\<forall>v v'. v \<rightarrow> v' \<in> atoms f21 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>v # \<rho>2" using TInter.prems by auto
  from TInter.IH(2)[of \<rho>2 \<rho>1] obtain f22 where f22_f12: "f22 <: f12" and wf_f22: "wf_fun f22"
    and f22_e: "\<forall>v v'. v \<rightarrow> v' \<in> atoms f22 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>v # \<rho>2" using TInter.prems by auto
  have v2_f12: "f21 \<sqinter> f22 <: f11 \<sqinter> f12" using f21_f11 f22_f12 sub_mon by blast
  have c_v1: "f11 ~ f12" using TInter.prems(4) by blast
  have f21_f22: "\<forall>f1 f2. f1 \<in> atoms f21 \<longrightarrow> f2 \<in> atoms f22 \<longrightarrow> f1 ~ f2"
  proof clarify
    fix f1 f2 assume f1_f21: "f1 \<in> atoms f21" and f2_f22: "f2 \<in> atoms f22"
    obtain f1a f1b where f1: "f1 = f1a \<rightarrow> f1b" using f1_f21 wf_f21 using atoms_wf_fun by blast
    obtain f2a f2b where f2: "f2 = f2a \<rightarrow> f2b" using f2_f22 wf_f22 using atoms_wf_fun by blast
    show "f1 ~ f2"
    proof (cases "f1a ~ f2a")
      case True
      from TInter.prems(2) have det_e: "determ f1b f2b e (f1a#\<rho>2) (f2a#\<rho>2)" by blast
      have f1b_e: "f1b \<in> \<lbrakk>e\<rbrakk>(f1a#\<rho>2)" using f21_e f1_f21 f1 by blast
      have f2b_e: "f2b \<in> \<lbrakk>e\<rbrakk>(f2a#\<rho>2)" using f22_e f2_f22 f2 by blast
      have wf_1ar2: "wf_env (f1a#\<rho>2)" using TInter(8) wf_f21 f1_f21 f1 wf_atoms[of f21 f1] 
          apply auto apply (case_tac k) apply auto done
      have wf_2ar2: "wf_env (f2a#\<rho>2)" using TInter(8) wf_f22 f2_f22 f2 wf_atoms[of f22 f2] 
          apply auto apply (case_tac k) apply auto done
      have c_1ar2_2ar2: "consis_env (f1a#\<rho>2) (f2a#\<rho>2)" using True TInter(8)
          apply auto apply (case_tac k) apply auto done          
      have "f1b ~ f2b" using det_e f1b_e f2b_e wf_1ar2 wf_2ar2 c_1ar2_2ar2 by blast
      then show ?thesis using True f1 f2 by simp
    next
      case False
      then show ?thesis using f1 f2 by simp
    qed      
  qed
  have c_v2: "f21 ~ f22" using f21_f22 wf_f21 wf_f22
    by (rule atoms_consis) 
  have wf_v2: "wf_fun (f21 \<sqinter> f22)" using wf_f21 wf_f22 c_v2 by blast
  have v2_e: "(\<forall>v v'. v \<rightarrow> v' \<in> atoms (f21 \<sqinter> f22) \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>v # \<rho>2)"
    using f21_e f22_e by auto
  show ?case using v2_f12 wf_v2 v2_e by blast
*)
  show ?case sorry
qed  

lemma merge_sub: "v1 ~ v2 \<Longrightarrow> merge v1 v2 <: v1"
  apply (case_tac v1) apply auto
  apply (case_tac v2) apply auto
  done

lemma merge_sub2: "v1 ~ v2 \<Longrightarrow> merge v1 v2 <: v2"
  apply (case_tac v1) apply auto
  apply (case_tac v2) apply auto
  done

lemma merge_mon: "\<lbrakk> A ~ B; C ~ D; A <: C; B <: D \<rbrakk> \<Longrightarrow> merge A B <: merge C D"
  using sub_mon merge_inter[of A B] merge_inter[of C D]
  by (meson sub_trans ty_equiv_def)
  
lemma wf_fun_sub: "\<lbrakk> wf_fun v1; v1 <: v2; wf_ty v2 \<rbrakk> \<Longrightarrow> wf_fun v2"
  by (metis consis_le consis_refl_aux consistent.simps(7) sub_nat_fun_inv sub_refl wf_fun_inv wf_ty.cases)  
    
lemma strengthen_var: "strengthen v1 v2 (EVar x) \<rho>1 \<rho>2"    
  apply clarify apply simp apply (case_tac "x < length \<rho>1") apply simp
    apply (meson sub_trans)
  apply force 
  done
  
lemma determ_var: "determ v1 v2 (EVar x) \<rho>1 \<rho>2"
      apply clarify
    apply simp apply (case_tac "x < length \<rho>1") apply simp 
     apply (rule conjI) apply (rule consis_le) apply force apply force apply force
      apply (rule conjI) 
      apply (rule merge_mon) apply force apply (rule consis_le) apply force apply force
      apply force apply force apply force apply (rule wf_merge) apply force apply force
   apply (rule consis_le) apply force apply force apply force apply force 
  done

lemma strengthen_nat: "strengthen v1 v2 (ENat x) \<rho>1 \<rho>2"
   apply auto
      apply (case_tac v2) apply auto 
  by (meson consis_refl consistent.simps(7) inconsis_le nat_wf_ty sub_refl)
    
lemma determ_nat:  "determ v1 v2 (ENat x) \<rho>1 \<rho>2" by auto

lemma strengthen_determ: "(\<forall> v1 v2 \<rho>1 \<rho>2. strengthen v1 v2 e \<rho>1 \<rho>2)
   \<and> (\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2)"
proof (induction e)
  case (EVar x)
  show ?case apply (rule conjI) using strengthen_var apply blast using determ_var by blast
next
  case (ENat x)
  show ?case  apply (rule conjI) using strengthen_nat apply blast using determ_nat by blast 
next
  case (ELam e)
  show ?case
  proof
    show "\<forall>v1 v2 \<rho>1 \<rho>2. strengthen v1 v2 (ELam e) \<rho>1 \<rho>2"
      apply (rule allI)+ apply (rule impI) apply (erule conjE)+
    proof -
      fix v1::ty and v2::ty and \<rho>1::"ty list" and \<rho>2::"ty list"
      assume v1_le: "v1 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>1" and l_r2_r1: "length \<rho>2 = length \<rho>1" and
        r2_r1_: "\<forall>k<length \<rho>2. \<rho>2 ! k <: \<rho>1 ! k" and v1_v2: "v1 <: v2" and wf_v2: "wf_ty v2" and
        wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2"
      have wf_v1: "wf_fun v1" and v1_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)"
        using v1_le by auto  
      have r2_r1: "\<rho>2 <: \<rho>1" using l_r2_r1 r2_r1_ by auto
      have wff_v2: "wf_fun v2" using wf_fun_sub wf_v2 v1_v2 wf_v1 by blast
      from strengthen_env_fun[of e \<rho>2 \<rho>1 v1 v2] r2_r1 ELam wf_v1 wff_v2 v1_v2 v1_e wf_r1 wf_r2
      have "(\<forall>v v'. v \<rightarrow> v' \<in> atoms v2 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>v # \<rho>2)" by fastforce
      then show "v2 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>2" using wff_v2 by simp
    qed
  next
    show "\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 (ELam e) \<rho>1 \<rho>2" 
      apply (rule allI)+ apply (rule impI) apply (erule conjE)+
    proof -
      fix v1 v2 \<rho>1 \<rho>2 assume v1_e: "v1 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>1" and v2_e: "v2 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>2" and
        wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and l_r1r2: "length \<rho>1 = length \<rho>2" and
        c_r1r2: "\<forall>k<length \<rho>1. \<rho>1 ! k ~ \<rho>2 ! k"
      have wf_v1: "wf_fun v1" and v1_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)" using v1_e by auto
      have wf_v2: "wf_fun v2" and v2_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v2 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>2)" using v2_e by auto          
      have v12: "merge v1 v2 = v1 \<sqinter> v2"
        using wf_v1 wf_v2 by (metis merge.simps(4) merge.simps(5) wf_fun_inv)          
      have v1_v2: "v1 ~ v2" apply (rule atoms_consis) using wf_v1 wf_v2 apply auto
      proof -
        fix a1 a2
        assume a1_v1: "a1 \<in> atoms v1" and a2_v2: "a2 \<in> atoms v2"
        obtain a11 a12 where a1: "a1=a11\<rightarrow>a12" using a1_v1 wf_v1 atoms_wf_fun by blast
        obtain a21 a22 where a2: "a2=a21\<rightarrow>a22" using a2_v2 wf_v2 atoms_wf_fun by blast
        show "a1 ~ a2"
        proof (cases "a11 ~ a21")
          case True
          have a12_e: "a12 \<in> \<lbrakk>e\<rbrakk>(a11#\<rho>1)" using v1_e a1_v1 a1 by simp
          have a22_e: "a22 \<in> \<lbrakk>e\<rbrakk>(a21#\<rho>2)" using v2_e a2_v2 a2 by simp
          have wf_r1: "wf_env (a11 # \<rho>1)"
            using wf_r1 wf_v1 a1_v1 apply simp apply clarify apply (case_tac k)
             apply simp 
             apply (metis a1 fun_wf_ty wf_arrow_inv wf_atoms wf_ty_arrow_inv)
             apply simp done
          have wf_r2: "wf_env (a21 # \<rho>2)" 
            using wf_r2 wf_v2 a2_v2 apply simp apply clarify apply (case_tac k)
              apply simp 
              apply (metis a2 fun_wf_ty wf_arrow_inv wf_atoms wf_ty_arrow_inv)
              apply simp done
          have c_r12: "consis_env (a11 # \<rho>1) (a21 # \<rho>2)" 
            using l_r1r2 c_r1r2 True apply simp apply clarify apply (case_tac k)
               apply simp apply simp done
          have "a12 ~ a22" using ELam.IH a12_e a22_e wf_r1 wf_r2 c_r12 by blast
          then show ?thesis using True a1 a2 by simp
        next
          case False
          then show ?thesis using a1 a2 by simp
        qed
      qed

      have v12_l: "merge v1 v2 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>1 \<sqinter> \<rho>2" apply simp
      proof
        show "wf_fun (merge v1 v2)"
          using wf_v1 wf_v2 v1_v2 by (simp add: inter_func v12)
      next
        show " \<forall>v v'. v \<rightarrow> v' \<in> atoms (merge v1 v2) \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>v # (\<rho>1 \<sqinter> \<rho>2)"
        proof clarify
          fix v v' assume vv_v12: "v \<rightarrow> v' \<in> atoms (merge v1 v2)"
          have wf_v: "wf_ty v" 
            by (meson fun_wf_ty v1_v2 vv_v12 wf_arrow_inv wf_atoms wf_merge wf_ty_arrow_inv wf_v1 wf_v2)
          have wf_vp: "wf_ty v'" 
            by (meson fun_wf_ty v1_v2 vv_v12 wf_arrow_inv wf_atoms wf_merge wf_ty_arrow_inv wf_v1 wf_v2)
          have "v\<rightarrow>v' \<in> atoms v1 \<or> v\<rightarrow>v' \<in> atoms v2" using v12 vv_v12 by simp        
          then show "v' \<in> \<lbrakk>e\<rbrakk>v # (\<rho>1 \<sqinter> \<rho>2)"
          proof
            assume vv_v1: "v\<rightarrow>v' \<in> atoms v1"
            have vp_e_r1: "v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)" using vv_v1 v1_e by blast
            have vr12_vr1: "v # (\<rho>1 \<sqinter> \<rho>2) <: v#\<rho>1" using l_r1r2 c_r1r2
              apply auto apply (case_tac k) apply auto using merge_sub apply auto done
            have wf_vr1: "wf_env (v#\<rho>1)" using wf_r1 wf_v apply auto apply (case_tac k) by auto
            have wf_vr2: "wf_env (v#(\<rho>1\<sqinter>\<rho>2))" using wf_r1 wf_r2 wf_v 
              apply auto apply (case_tac k) apply auto using c_r1r2 by blast
            have vp_vp: "v' <: v'" by auto
            from ELam have "strengthen v' v' e (v#\<rho>1) (v#(\<rho>1\<sqinter>\<rho>2))" by blast
            then show ?thesis using vp_e_r1 vr12_vr1 wf_vp wf_vr1 wf_vr2 vp_vp by blast
          next
            assume vv_v2: "v\<rightarrow>v' \<in> atoms v2"
            have vp_e_r2: "v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>2)" using vv_v2 v2_e by blast
            have vr12_vr1: "v # (\<rho>1 \<sqinter> \<rho>2) <: v#\<rho>2" using l_r1r2 c_r1r2
              apply auto apply (case_tac k) apply auto using merge_sub2 apply auto done
            have wf_vr1: "wf_env (v#\<rho>2)" using wf_r2 wf_v apply auto apply (case_tac k) by auto
            have wf_vr2: "wf_env (v#(\<rho>1\<sqinter>\<rho>2))" using wf_r1 wf_r2 wf_v 
              apply auto apply (case_tac k) apply auto using c_r1r2 by blast
            have vp_vp: "v' <: v'" by auto
            from ELam have "strengthen v' v' e (v#\<rho>2) (v#(\<rho>1\<sqinter>\<rho>2))" by blast
            then show ?thesis using vp_e_r2 vr12_vr1 wf_vp wf_vr1 wf_vr2 vp_vp by blast
          qed
        qed
      qed
      show "v1 ~ v2 \<and> merge v1 v2 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>1 \<sqinter> \<rho>2" using v1_v2 v12_l by simp
    qed
  qed    
next
  case (EApp e1 e2)
  then show ?case sorry
next
  case (EPrim f e1 e2)
  then show ?case sorry
next
  case (EIf e1 e2 e3)
  show ?case sorry
(*
  proof
    show "\<forall>v1 \<rho>1 \<rho>2. strengthen v1 (EIf e1 e2 e3) \<rho>1 \<rho>2" 
      apply (rule allI)+ apply (rule impI) apply (erule conjE)+
    proof -
      fix v1 and \<rho>1::"ty list" and \<rho>2::"ty list"
      assume v1_if: "v1 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>1" and l_r2_r1: "length \<rho>2 = length \<rho>1" and
         r2_r1: "\<forall>k<length \<rho>2. \<rho>2 ! k <: \<rho>1 ! k" and wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2"      
      obtain n where n_e1: "TNat n \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v1_e3: "n=0\<longrightarrow> v1 \<in> \<lbrakk>e3\<rbrakk>\<rho>1" and 
        v1_e2: "n\<noteq>0 \<longrightarrow> v1 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" using v1_if by auto
      have IH1: "strengthen (TNat n) e1 \<rho>1 \<rho>2" using EIf.IH(1) by blast
      obtain v2 where v2_n: "v2 <: TNat n" and wf_v2: "wf_ty v2" and v2_e1_r2: "v2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2"
        using IH1 n_e1 l_r2_r1 r2_r1 wf_r1 wf_r2 by blast
      have v2: "v2 = TNat n" using v2_n wf_v2
        by (metis consis_le consis_refl consistent.simps(7) merge.simps(1) merge_inter sub_refl ty_equiv_def) 
      show "\<exists>v2. v2 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>2 \<and> v2 <: v1 \<and> wf_ty v2"
      proof (cases "n = 0")
        case True
        have IH3: "strengthen v1 e3 \<rho>1 \<rho>2" using EIf.IH(3) by blast
        from IH3 l_r2_r1 r2_r1 wf_r1 wf_r2 v1_e3 True
        obtain v3 where v3_e3: "v3 \<in> \<lbrakk>e3\<rbrakk>\<rho>2" and v3_v1: "v3 <: v1" and wf_v3: "wf_ty v3" by blast        
        then show ?thesis using True v2_e1_r2 v2 by auto
      next
        case False
        have IH2: "strengthen v1 e2 \<rho>1 \<rho>2" using EIf.IH(2) by blast
        from IH2 l_r2_r1 r2_r1 wf_r1 wf_r2 v1_e2 False
        obtain v3 where v3_e2: "v3 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" and v3_v1: "v3 <: v1" and wf_v3: "wf_ty v3" by blast        
        then show ?thesis using False v2_e1_r2 v2 by auto
      qed      
    qed
  next    
    show "\<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 (EIf e1 e2 e3) \<rho>1 \<rho>2"
      apply (rule allI)+ apply (rule impI) apply (erule conjE)+
    proof -
      fix v1 v2 \<rho>1 \<rho>2
      assume v1_if: "v1 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>1" and v2_if: "v2 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>2"
         and wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and l_r1_r2: "length \<rho>1 = length \<rho>2" and 
         c_r1_r2: "\<forall>k<length \<rho>1. \<rho>1 ! k ~ \<rho>2 ! k" 
      obtain n1 where n1_e1: "TNat n1 \<in> \<lbrakk>e1\<rbrakk>\<rho>1" and v1_e3: "n1 = 0 \<longrightarrow> v1 \<in> \<lbrakk>e3\<rbrakk>\<rho>1" and
        v1_e2: "n1 \<noteq> 0 \<longrightarrow> v1 \<in> \<lbrakk>e2\<rbrakk>\<rho>1" using v1_if by auto
      obtain n2 where n2_e1: "TNat n2 \<in> \<lbrakk>e1\<rbrakk>\<rho>2" and v2_e3: "n2 = 0 \<longrightarrow> v2 \<in> \<lbrakk>e3\<rbrakk>\<rho>2" and
        v2_e2: "n2 \<noteq> 0 \<longrightarrow> v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>2" using v2_if by auto
      have IH1: "determ (TNat n1) (TNat n2) e1 \<rho>1 \<rho>2" using EIf.IH(1) by blast
      have n1_n2: "n1 = n2" using IH1 n1_e1 n2_e1 wf_r1 wf_r2 l_r1_r2 c_r1_r2 by simp
      have n12_e1: "merge (TNat n1) (TNat n2) \<in> \<lbrakk>e1\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
        using IH1 n1_e1 n2_e1 wf_r1 wf_r2 l_r1_r2 c_r1_r2 by auto
      show "v1 ~ v2 \<and> merge v1 v2 \<in> \<lbrakk>EIf e1 e2 e3\<rbrakk>\<rho>1 \<sqinter> \<rho>2"
      proof (cases "n1 = 0")
        case True
        have IH3: "determ v1 v2 e3 \<rho>1 \<rho>2" using EIf.IH(3) by blast
        have v1_v2: "v1 ~ v2"
          using IH3 v1_e3 v2_e3 True n1_n2 wf_r1 wf_r2 l_r1_r2 c_r1_r2 by auto
        have "merge v1 v2 \<in> \<lbrakk>e3\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
          using IH3 v1_e3 v2_e3 EIf.prems True n1_n2 wf_r1 wf_r2 l_r1_r2 c_r1_r2 by auto
        then show ?thesis using v1_v2 n1_n2 True n12_e1 by auto
      next
        case False
        have IH2: "determ v1 v2 e2 \<rho>1 \<rho>2" using EIf.IH(2) by blast
        have v1_v2: "v1 ~ v2"
          using IH2 v1_e2 v2_e2 EIf.prems False n1_n2 wf_r1 wf_r2 l_r1_r2 c_r1_r2 by auto
        have "merge v1 v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>1 \<sqinter> \<rho>2" 
          using IH2 v1_e2 v2_e2 EIf.prems False n1_n2 wf_r1 wf_r2 l_r1_r2 c_r1_r2 by auto
        then show ?thesis using v1_v2 n1_n2 False n12_e1 by auto
      qed      
    qed
  qed
*)
qed

lemma sub_atoms_inv: "\<lbrakk> v1 <: v2; a \<in> atoms v2 \<rbrakk> \<Longrightarrow> v1 <: a"
  using ax_atoms sub_trans sub_ty_def by blast  
  
lemma subsumption: "\<lbrakk> v1 \<in> \<lbrakk>e\<rbrakk>\<rho>; v1 <: v2; wf_ty v2 \<rbrakk> \<Longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>\<rho>"
  apply (induction e arbitrary: v1 v2 \<rho>)
       apply simp apply (case_tac "x < length \<rho>") apply simp 
        apply (rule sub_trans) apply blast apply blast
       apply force
    
    apply simp apply (case_tac v2) apply force apply force 
      apply (meson consis_le consis_refl consistent.simps(7) nat_wf_ty sub_refl)
    
     apply simp
    apply (rule conjI) using wf_fun_sub apply blast
     apply clarify
     apply (subgoal_tac "v1 <: v \<rightarrow> v'") prefer 2 using sub_atoms_inv apply blast
     apply (erule sub_any_fun_elim)
    oops

lemma arrow_lam: "\<lbrakk> wf_ty v; wf_ty v' \<rbrakk> \<Longrightarrow> (v\<rightarrow>v' \<in> \<lbrakk>\<lambda>e\<rbrakk>\<rho>) = (v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>))"
  by auto


    
      
lemma fold_merge_arrows: 
  fixes e::exp and \<Gamma>::"ty list" and A1::ty 
  shows "\<lbrakk> \<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2; all_funs \<Gamma>; wf_env \<rho>;
         (*wf_fun C; set \<Gamma> \<subseteq> atoms C; A\<rightarrow>B \<in> atoms C;*)
         set \<Gamma> \<subseteq> \<lbrakk>\<lambda>e\<rbrakk>\<rho>; A\<rightarrow>B \<in> \<lbrakk>\<lambda>e\<rbrakk>\<rho> \<rbrakk> \<Longrightarrow> 
         fold merge (map cod \<Gamma>) B \<in> \<lbrakk>e\<rbrakk>(fold merge (map dom \<Gamma>) A)#\<rho>"
proof (induction \<Gamma> arbitrary: A B)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  obtain A' B' where a: "a = A' \<rightarrow> B'" using Cons.prems(2) by (cases a) auto
  have d_e: "determ B' B e (A'#\<rho>) (A#\<rho>)" using Cons.prems(1) by blast
  have bp_e: "B' \<in> \<lbrakk>e\<rbrakk>A'#\<rho>" using Cons.prems a by simp
  have b_e: "B \<in> \<lbrakk>e\<rbrakk>A#\<rho>" using Cons.prems by simp      
  have a_ap: "A ~ A'" sorry
  have wf_a: "wf_ty A" sorry
  have wf_ap: "wf_ty A'" sorry
  have wf_apr: "wf_env (A'#\<rho>)" using wf_ap Cons.prems(3) apply auto
      apply (case_tac k) apply auto done
  have wf_ar: "wf_env (A#\<rho>)" using wf_a Cons.prems(3) apply auto
      apply (case_tac k) apply auto done      
  have c_apr_ar: "consis_env (A'#\<rho>) (A#\<rho>)" using Cons(4) a_ap apply auto
      apply (case_tac k) apply auto using consis_sym apply blast done
  from d_e bp_e b_e wf_apr wf_ar c_apr_ar 
  have "B' ~ B \<and> merge B' B \<in> \<lbrakk>e\<rbrakk>((A'#\<rho>) \<sqinter> (A#\<rho>))" by auto
  then have aa_bb_le: "(merge A' A) \<rightarrow> (merge B' B) \<in> \<lbrakk>\<lambda>e\<rbrakk>\<rho>" sorry
  have af_g: "all_funs \<Gamma>" using Cons.prems(2) by auto
  from Cons.IH[of "merge A' A" "merge B' B"] Cons.prems(1) af_g Cons.prems(3)
  have "fold merge (map cod \<Gamma>) (merge B' B)
      \<in> \<lbrakk>e\<rbrakk>fold merge (map IntersectionTypes.dom \<Gamma>) (merge A' A) # \<rho>"
     by (smt Cons.prems(4) aa_bb_le insert_subset list.simps(15))     
  then show ?case using a by simp
qed
*)
  
end
