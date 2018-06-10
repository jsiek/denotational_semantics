theory Subsumption
 imports Values Denot
begin

lemma is_val_sem: assumes v_e: "v \<in> \<lbrakk>e\<rbrakk>\<rho>" and v_r: "val_env \<rho>" shows "is_val v" 
  using v_e v_r
proof (induction e arbitrary: v \<rho>)
  case (EVar x)
  then show ?case by (case_tac "x < length \<rho>") auto
qed auto

proposition change_env_le: fixes v::val and \<rho>::"val list"
  assumes de: "v \<in> E e \<rho>" and vp_v: "v' \<sqsubseteq> v" 
    and vvp: "is_val v'" and rr: "\<rho> \<sqsubseteq> \<rho>'" and vr: "val_env \<rho>" and vrp: "val_env \<rho>'"
  shows "v' \<in> E e \<rho>'"
  using de rr vp_v vvp vr vrp
proof (induction e arbitrary: v v' \<rho> \<rho>' rule: exp.induct)
  case (EVar x)
  obtain v2 where lx: "\<rho>!x = v2" and v_v2: "v \<sqsubseteq> v2" and kr: "x< length \<rho>"
      using EVar by (case_tac "x < length \<rho>") auto 
  obtain v3 where lx2: "\<rho>'!x = v3" and v2_v3: "v2 \<sqsubseteq> v3"
    using lx EVar kr unfolding env_le_def by auto 
  have v_v3: "v \<sqsubseteq> v3" using v_v2 v2_v3  using le_trans by blast
  have vp_v3: "v' \<sqsubseteq> v3" using EVar v_v3 le_trans by blast 
  show ?case using EVar lx2 vp_v3 kr unfolding env_le_def by auto
next
  case (ELam e)
 obtain f where v: "v = VFun f" and vv: "is_val v" and
    body: "\<forall> v1 v2. (v1,v2) \<in> set f \<longrightarrow> v2 \<in> \<lbrakk>e\<rbrakk>(v1#\<rho>)" using ELam(2) by fastforce     
  obtain f' where vp: "v' = VFun f'" using v ELam(4)  by (case_tac v') auto 
  have v_fp: "is_val (VFun f')" using ELam(5) vp by simp
  from vp this show ?case 
  proof (simp,clarify)
    fix v1 v2 assume v12: "(v1,v2) \<in> set f'" 
    obtain v3 v4 where v34: "(v3,v4) \<in> set f" 
      and v3_v1: "v3 \<sqsubseteq> v1" and v2_v4: "v2 \<sqsubseteq> v4" 
      sorry (*
      using v12 ELam(4) v vp using le_fun_sub_pair by blast*)
    have v4_E: "v4 \<in> \<lbrakk>e\<rbrakk>(v3#\<rho>)" using v34 body by blast
    have rr2: "(v3#\<rho>) \<sqsubseteq> (v1#\<rho>')" using ELam(3) v3_v1 unfolding env_le_def apply auto
        apply (case_tac k) apply force apply force done
    have v_v2: "is_val v2" using ELam(5) vp v12 by auto 
    have v_v3r: "val_env (v3 # \<rho>)" using ELam(6) v34 v vv unfolding val_env_def 
        apply clarify apply (case_tac k) apply force apply force done
    have v_v1rp: "val_env (v1 # \<rho>')" using ELam(7) v12 v_fp unfolding val_env_def
        apply clarify apply (case_tac k) apply force apply force done        
    show "v2 \<in> E e (v1#\<rho>')" 
      using ELam(1)[of v4 "v3#\<rho>" "v1#\<rho>'" v2] v4_E rr2 v2_v4 v_v2 v_v3r v_v1rp by blast
  qed
next
  case (EApp e1 e2)
  obtain f v2 where 
    f_e1: "VFun f \<in> E e1 \<rho>" and v2_e2: "v2 \<in> E e2 \<rho>" and
    v23p_f: "[(v2,v)] \<sqsubseteq> f"  using EApp(3) by auto
  have v_vf: "is_val (VFun f)" using f_e1 is_val_sem EApp(7) by blast
  have v_v2: "is_val v2" using v2_e2 is_val_sem EApp by blast
  have f_e1b: "VFun f \<in> \<lbrakk>e1\<rbrakk> \<rho>'" 
    using EApp(7) EApp(8) EApp(1)[of "VFun f" \<rho> \<rho>' "VFun f"] f_e1 EApp(4) v_vf by blast
  have v2_e2b: "v2 \<in> \<lbrakk>e2\<rbrakk>\<rho>'" using EApp(7) EApp(8) v2_e2 EApp(4) v_v2 EApp.IH(2) by blast
  have "[(v2,v')] \<sqsubseteq> [(v2,v)]" using EApp(5) by (simp add: le_refl le_arrow)
  then have v2v_f: "[(v2,v')] \<sqsubseteq> f" using v23p_f le_fun_trans[of "[(v2,v')]" "[(v2,v)]" f] by simp
  show ?case using v2v_f f_e1b EApp(6) v2_e2b by auto
next
  case (EPrim f e1 e2)
  then show ?case by (smt E.simps(5) is_val_sem le_nat le_nat_fun_inv mem_Collect_eq val_le.cases)
next
  case (EIf e1 e2 e3)
  then show ?case apply simp apply clarify apply (rule_tac x=n in exI) apply (rule conjI) by auto
qed auto

end