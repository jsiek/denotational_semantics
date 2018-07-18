theory Deterministic
  imports Consistency Denot
begin

lemma wf_eval: "\<lbrakk> v \<in> \<lbrakk>e\<rbrakk>\<rho>; wf_env \<rho> \<rbrakk> \<Longrightarrow> wf_ty v"
  apply (induction e) apply (case_tac "x < length \<rho>") apply force+ done

lemma merge_inter: "A ~ B \<Longrightarrow> merge A B \<approx> A \<sqinter> B"
  apply (case_tac A)
    apply (case_tac B)
      apply force
    apply force
  apply force
  apply force
  apply force
  done
    
lemma merge_inter_equiv: "\<lbrakk> A ~ B; B \<approx> B' \<rbrakk> \<Longrightarrow> merge A B \<approx> A \<sqinter> B'"
  apply (case_tac A)
    apply (case_tac B)
      apply force
     apply force
    apply force
   apply force
    apply force
  done
  
lemma fold_merge_equiv_fold_meet_aux: fixes xs::"ty list"
  assumes c_xs: "\<forall>v1 v2. {v1,v2} \<subseteq> set xs \<longrightarrow> v1 ~ v2" and x_xp: "x \<approx> x'" and
    x_xs: "\<forall>v. v \<in> set xs \<longrightarrow> x ~ v" and wf_xs: "\<forall>v. v \<in> set xs \<longrightarrow> wf_ty v" and wf_x: "wf_ty x" 
  shows "fold merge xs x \<approx> fold op \<sqinter> xs x'"
  using c_xs x_xp x_xs wf_xs wf_x
proof (induction xs arbitrary: x x')
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have 1: "\<forall>v1 v2. {v1, v2} \<subseteq> set xs \<longrightarrow> v1 ~ v2" using Cons by auto
  have 2: "\<forall>v. v \<in> set xs \<longrightarrow> (merge a x) ~ v" using Cons apply clarify 
      apply (rule consis_merge_left) apply auto done
  have 3: "\<forall>v. v \<in> set xs \<longrightarrow> wf_ty v" using Cons by auto
  have 4: "wf_ty (merge a x)" using Cons wf_merge consis_sym by auto
  have 5: "merge a x \<approx> a \<sqinter> x'"
  proof -
    have "a ~ x" using Cons(4) consis_sym by auto
    then show ?thesis using Cons(3) merge_inter_equiv[of a x x'] by simp
  qed
  have "fold merge xs (merge a x) \<approx> fold op \<sqinter> xs (a \<sqinter> x')"
    using Cons.IH[of "merge a x" "a \<sqinter> x'"] 1 2 3 4 5 by blast  
  then show ?case by simp
qed

lemma merge_list_equiv_meet_list: fixes xs::"ty list"
  assumes c_xs: "\<forall>v1 v2. {v1,v2} \<subseteq> set xs \<longrightarrow> v1 ~ v2" and wf_xs: "\<forall>v. v \<in> set xs \<longrightarrow> wf_ty v" 
    and xs_ne: "xs \<noteq> []"
  shows "\<Prod>xs \<approx> \<Sqinter>xs"
proof -
  obtain x xs' where xs: "xs = x#xs'" using xs_ne by (cases xs) auto      
  have 1: "\<forall>v1 v2. {v1,v2} \<subseteq> set xs' \<longrightarrow> v1 ~ v2" using c_xs xs by auto
  have 2: "x \<approx> x" by auto
  have 3: "\<forall>v. v \<in> set xs' \<longrightarrow> x ~ v" using c_xs xs by auto
  have 4: "\<forall>v. v \<in> set xs' \<longrightarrow> wf_ty v" using wf_xs xs by auto
  have 5: "wf_ty x" using wf_xs xs by auto
  have "fold merge xs' x \<approx> fold op \<sqinter> xs' x" 
    using 1 2 3 4 5 fold_merge_equiv_fold_meet_aux[of xs' x x] by blast
  then show ?thesis using xs merge_list_def meet_list_def by simp
qed
  
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

lemma all_fun_ex: "\<lbrakk> all_funs \<Gamma>; x \<in> set \<Gamma>; \<And> a b. \<lbrakk> x = a \<rightarrow> b \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (cases x) apply auto done

lemma all_fun_ex_dom: "\<lbrakk> all_funs \<Gamma>; y \<in> set (map cod \<Gamma>) \<rbrakk> \<Longrightarrow> \<exists>x. x\<rightarrow>y \<in> set \<Gamma>"
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
      
  obtain \<Gamma>1 where g1_ne: "\<Gamma>1 \<noteq> []" and af_g1: "all_funs \<Gamma>1" and g1_f1: "set \<Gamma>1 \<subseteq> atoms f1" and
    v1_g1: "\<forall>v v'. v\<rightarrow>v' \<in> set \<Gamma>1 \<longrightarrow> v1 <: v" and g1_v1p: "\<Sqinter>(map cod \<Gamma>1) <: v1'"
    using f1_v11 sub_fun_any_inv_atoms[of f1 v1 v1'] by blast
  let ?C1 = "map cod \<Gamma>1"     
  obtain \<Gamma>2 where g2_ne: "\<Gamma>2 \<noteq> []" and af_g2: "all_funs \<Gamma>2" and g2_f2: "set \<Gamma>2 \<subseteq> atoms f2" and
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
  have c1_c2: "\<Prod>?C1 ~ \<Prod>?C2"
  proof (rule consis_merge_list)
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
  next
    show "\<forall>v. v \<in> set ?C1 \<longrightarrow> wf_ty v" using wf_c1 by blast
  next
    show "\<forall>v. v \<in> set ?C2 \<longrightarrow> wf_ty v" using wf_c2 by blast
  next
    show "map cod \<Gamma>1 \<noteq> []" using g1_ne by simp
  next
    show "map cod \<Gamma>2 \<noteq> []" using g2_ne by simp
  qed
  have c1_c1: "\<Prod>?C1 \<approx> \<Sqinter>?C1" using merge_list_equiv_meet_list wf_c1 c_c1 g1_ne by auto
  have c2_c2: "\<Prod>?C2 \<approx> \<Sqinter>?C2" using merge_list_equiv_meet_list wf_c2 c_c2 g2_ne by auto    
  have "\<Sqinter>?C1 ~ \<Sqinter>?C2" using c1_c1 c1_c2 c2_c2 
      using consis_le ty_equiv_def by auto 
  then show ?thesis using g1_v1p g2_v2p consis_le by blast
qed
  
lemma merge_app: assumes f1_v1: "v1' \<in> f1 \<bullet> v1" and f2_v2: "v2' \<in> f2 \<bullet> v2" and 
  f1_f2: "f1 ~ f2" and v1_v2: "v1 ~ v2" and v1p_v2p: "v1' ~ v2'"
  shows "merge v1' v2' \<in> merge f1 f2 \<bullet> merge v1 v2"
proof -
  have wf_v12: "wf_ty (merge v1' v2')" using f1_v1 f2_v2 v1p_v2p by auto 
  have f1_v1p: "f1 <: v1 \<rightarrow> v1'" using f1_v1 by simp
  have f2_v2p: "f2 <: v2 \<rightarrow> v2'" using f2_v2 by simp  
  have "merge f1 f2 <: f1 \<sqinter> f2" using merge_inter f1_f2 ty_equiv_def by auto
  also have "f1 \<sqinter> f2 <: (v1\<rightarrow>v1') \<sqinter> (v2\<rightarrow>v2')" using f1_v1p f2_v2p by (rule sub_mon)
  also have "(v1 \<rightarrow> v1') \<sqinter> (v2 \<rightarrow> v2') <: (v1 \<sqinter> v2) \<rightarrow> (v1' \<sqinter> v2')" by (rule sub_dist_union_fun)
  also have "... <: (merge v1 v2) \<rightarrow> (merge v1' v2')" apply (rule sub_arrow)
      using merge_inter v1_v2 v1p_v2p ty_equiv_def apply auto done
  finally have "merge f1 f2 <: (merge v1 v2) \<rightarrow> (merge v1' v2')" using sub_trans by auto
  then show ?thesis using wf_v12 by simp
qed

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
    using v1p_f1_v1 v2p_f2_v2 f1_f2 v1_v2 v1p_v2p merge_app by blast
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

abbreviation strengthen :: "ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "strengthen v1 e \<rho>1 \<rho>2 \<equiv> (v1 \<in> \<lbrakk>e\<rbrakk>\<rho>1 \<and> \<rho>2 <: \<rho>1 \<and> wf_env \<rho>1 \<and> wf_env \<rho>2 \<longrightarrow>
    (\<exists>v2. v2 \<in> \<lbrakk>e\<rbrakk>\<rho>2 \<and> v2 <: v1 \<and> wf_ty v2))"

abbreviation determ :: "ty \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "determ v1 v2 e \<rho>1 \<rho>2 \<equiv> (v1 \<in> E e \<rho>1 \<and> v2 \<in> E e \<rho>2 \<and> wf_env \<rho>1 \<and> wf_env \<rho>2 \<and> consis_env \<rho>1 \<rho>2 
   \<longrightarrow> v1 ~ v2 \<and> merge v1 v2 \<in> \<lbrakk>e\<rbrakk>(\<rho>1 \<sqinter> \<rho>2))"

lemma strengthen_determ: "(\<forall> v1 \<rho>1 \<rho>2. strengthen v1 e \<rho>1 \<rho>2)\<and>(\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2)"
proof (induction e)
  case (EVar x)
  then show ?case by auto
next
  case (ENat x)
  then show ?case by auto
next
  case (ELam e)
  show ?case
  proof
    show "\<forall>v1 \<rho>1 \<rho>2. strengthen v1 (ELam e) \<rho>1 \<rho>2"
      apply (rule allI)+ apply (rule impI) apply (erule conjE)+
    proof -
      fix v1 and \<rho>1::"ty list" and \<rho>2::"ty list"
      assume v1_le: "v1 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>1" and l_r2_r1: "length \<rho>2 = length \<rho>1" and
        r2_r1: "\<forall>k<length \<rho>2. \<rho>2 ! k <: \<rho>1 ! k" and wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2"
      have wf_v1: "wf_fun v1" and v1_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)"
        using v1_le by auto    
      
      
          
      show "\<exists>v2. v2 \<in> \<lbrakk>ELam e\<rbrakk>\<rho>2 \<and> v2 <: v1 \<and> wf_ty v2"     
        sorry
    qed      
  next
    show "\<forall>v1 v2 \<rho>1 \<rho>2. determ v1 v2 (ELam e) \<rho>1 \<rho>2" sorry
  qed    
next
  case (EApp e1 e2)
  then show ?case sorry
next
  case (EPrim f e1 e2)
  then show ?case sorry
next
  case (EIf e1 e2 e3)
  show ?case
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
qed
  
lemma strengthen_env_fun:
  fixes \<rho>1::"ty list" and \<rho>2::"ty list"
  assumes str: "\<forall> v1 \<rho>1 \<rho>2. strengthen v1 e \<rho>1 \<rho>2" and 
    det: "\<forall> v1 v2 \<rho>1 \<rho>2. determ v1 v2 e \<rho>1 \<rho>2" and
    r2_r1: "\<rho>2 <: \<rho>1" and
    wf_v1: "wf_fun v1" and wf_r1: "wf_env \<rho>1" and wf_r2: "wf_env \<rho>2" and
    v1_e: "\<forall>v v'. v\<rightarrow>v' \<in> atoms v1 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>1)"    
  shows "\<exists> v2. v2 <: v1 \<and> wf_fun v2 \<and> (\<forall>v v'. v\<rightarrow>v' \<in> atoms v2 \<longrightarrow> v' \<in> \<lbrakk>e\<rbrakk>(v#\<rho>2))"
    using str det r2_r1 wf_v1 wf_r1 wf_r2 v1_e
proof (induction v1 arbitrary: \<rho>1 \<rho>2)
  case (TNat n)
  then have "False" by auto
  then show ?case ..
next
  case (TArrow v11 v12)
  have v12_e: "v12 \<in> \<lbrakk>e\<rbrakk>(v11#\<rho>1)" using TArrow.prems(7) by auto
  have vr2_vr1: "v11#\<rho>2 <: v11#\<rho>1" using TArrow(5) apply auto apply (case_tac k) by auto
  have wf_v11: "wf_ty v11" using TArrow using wf_atoms by blast
  have wf_vr1: "wf_env (v11#\<rho>1)" using TArrow(7) wf_v11 apply auto apply (case_tac k) by auto
  have wf_vr2: "wf_env (v11#\<rho>2)" using TArrow(8) wf_v11 apply auto apply (case_tac k) by auto
  obtain v22 where v22_e: "v22 \<in> \<lbrakk>e\<rbrakk>(v11#\<rho>2)" and v22_v12: "v22 <: v12" and wf_v22: "wf_ty v22"
    using TArrow.prems(1) v12_e vr2_vr1 wf_vr1 wf_vr2 apply (erule_tac x=v12 in allE)
      apply (erule_tac x="v11#\<rho>1" in allE) apply (erule_tac x="v11#\<rho>2" in allE)
    apply (erule impE) apply force apply blast done
  have v12_v12: "v11 \<rightarrow> v22 <: v11 \<rightarrow> v12" using v22_v12 sub_arrow by auto
  have wf_v12: "wf_ty (v11 \<rightarrow> v22)" using wf_v11 wf_v22 by auto
  then show ?case using v22_e v12_v12 wf_v12 by auto
next
  case (TInter f11 f12)
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
      have "f1a \<in> \<lbrakk>e\<rbrakk>(f1b#\<rho>2)" using f21_e f1_f21 f1 sorry
          
      have "f1b ~ f2b" sorry
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
qed  
  

end
