theory Values
imports Main
begin

datatype val = VNat nat | VFun "(val \<times> val) list" 
type_synonym entry = "val \<times> val" 
type_synonym func = "entry list"  
abbreviation make_entry :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<mapsto>" 70) where
  "v \<mapsto> v' \<equiv> VFun [(v,v')]"
abbreviation bottom_fun :: "val" ("\<bottom>" 100) where
  "bottom_fun \<equiv> VFun []"

function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + fsize t" |
"fsize [] = 0" |
"fsize ((v,v')#t) = vsize v + vsize v' + fsize t"
  by pat_completeness auto
termination vsize by size_change

lemma vsize_pos[simp]: "0 < vsize v"
  apply (case_tac v) apply auto done
    
lemma fsize_append[simp]: "fsize (f1@f2) = fsize f1 + fsize f2"
  apply (induction f1 arbitrary: f2)
   apply force
  apply simp apply (case_tac a) apply simp 
  done
    
lemma fsize_append_right: "f3 \<noteq> [] \<Longrightarrow> fsize f2 < fsize (f2 @ f3)"
  apply (induction f2)
  apply simp apply (case_tac f3) apply force apply force
  apply force
  done

lemma fsize_append_left: "f2 \<noteq> [] \<Longrightarrow> fsize f3 < fsize (f2 @ f3)"
  apply (induction f2) apply simp apply (case_tac f2) apply force apply force done
    
lemma size_fun_mem: "(v,v') \<in> set f \<Longrightarrow> vsize v + vsize v' \<le> fsize f"
  by (induction f) auto 
  
lemma size_fun_mem2: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; (v1,v1') \<noteq> (v2,v2') \<rbrakk>
  \<Longrightarrow> vsize v1 + vsize v1' + vsize v2 + vsize v2' \<le> fsize f"
  apply (induction f arbitrary: v1 v1' v2 v2')
   apply force
   apply simp apply (erule disjE) 
   apply (erule disjE)
    apply clarify
    apply (erule impE) apply simp apply blast
   apply clarify apply (case_tac "a = v2") apply simp
    using size_fun_mem apply force
     apply simp using size_fun_mem apply force
    apply clarify apply (erule disjE) apply clarify
    defer
    apply fastforce
  proof -
    fix a :: val and b :: val and fa :: "(val \<times> val) list" and v1a :: val and v1'a :: val and v2a :: val and v2'a :: val
    assume "(v1a, v1'a) \<in> set fa"
    then have "vsize v1a + vsize v1'a \<le> fsize fa"
      by (meson size_fun_mem)
    then show "vsize v1a + vsize v1'a + vsize a + vsize b \<le> fsize ((a, b) # fa)"
      by auto
qed 
      
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = (if f1 = f2 then Some (VFun f1) else Some (VFun (f1 @ f2)))" |
  "v1 \<squnion> v2 = None"

lemma vsize_join: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> vsize v12 \<le> vsize v1 + vsize v2"
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force apply (case_tac v2) apply force apply simp
   apply (case_tac "x2 = x2a") apply force apply force
  done
    

lemma size_fun_mem_join_fst: assumes v11_f: "(v1,v1') \<in> set f" and v22_f: "(v2,v2') \<in> set f"
  and v123: "v1 \<squnion> v2 = Some v3" shows "vsize v3 \<le> (fsize f)"
proof (cases "v1 = v2")
  case True
  have 1: "vsize v1 + vsize v1' \<le> fsize f" using size_fun_mem v11_f by blast
  have 2: "v3 = v1" using v123 True by (case_tac v1) auto
  show ?thesis using 1 2 by simp
next
  case False
  have 1: "vsize v1 + vsize v1' + vsize v2 + vsize v2' \<le> fsize f"
    using size_fun_mem2 False v11_f v22_f by blast
  have 2: "vsize v3 \<le> vsize v1 + vsize v2" using vsize_join v123 by blast
  show ?thesis using 1 2 by simp
qed

  
lemma size_fun_mem_join: assumes v11_f: "(v1,v1') \<in> set f" and v22_f: "(v2,v2') \<in> set f"
  and v123: "v1' \<squnion> v2' = Some v3" shows "vsize v3 \<le> (fsize f)"
proof (cases "v1' = v2'")
  case True
  have 1: "vsize v1 + vsize v1' \<le> fsize f" using size_fun_mem v11_f by blast
  have 2: "v3 = v1'" using v123 True by (case_tac v1') auto
  show ?thesis using 1 2 by simp
next
  case False
  have 1: "vsize v1 + vsize v1' + vsize v2 + vsize v2' \<le> fsize f"
    using size_fun_mem2 False v11_f v22_f by blast
  have 2: "vsize v3 \<le> vsize v1' + vsize v2'" using vsize_join v123 by blast
  show ?thesis using 1 2 by simp
qed
    
fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> (val list) option" (infix "\<squnion>" 56) where
  "env_join [] [] = Some []" |
  "env_join (v#\<rho>) (v'#\<rho>') = 
      (case v \<squnion> v' of
         None \<Rightarrow> None
      | Some v'' \<Rightarrow> 
           (case \<rho>\<squnion>\<rho>' of
             None \<Rightarrow> None
           | Some \<rho>'' \<Rightarrow> Some (v''#\<rho>'')))" 

text{* 
  The following rules are adapted from BCD and EHR subtyping (Lambda Calculus with Types 2013).
  I removed refl and trans and changed the other rules to compensate so
  that I could prove refl and trans. The distr rule is inspired by 
     the one Olivier Laurent used in his paper in ITRS 2012.
*}
inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) 
    where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" |
  le_bot[intro!]: "\<bottom> \<sqsubseteq> VFun f" |
  le_fun_append_left: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f2; f3 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_fun_append_right: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; f2 \<noteq> []\<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_fun_left_append: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3; f1 \<noteq> []; f2 \<noteq> [] \<rbrakk>
                     \<Longrightarrow> VFun (f1@f2) \<sqsubseteq> VFun f3" |
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" |
  le_distr_L: "\<lbrakk> va \<squnion> vb = Some vab; vc \<mapsto> va \<sqsubseteq> vd; vc \<mapsto> vb \<sqsubseteq> vd;
                 vab \<noteq> va; vab \<noteq> vb \<rbrakk> \<Longrightarrow> vc \<mapsto> vab \<sqsubseteq> vd" 
(*
  le_distr_R1: "\<lbrakk> va \<squnion> vb = Some vab \<rbrakk> \<Longrightarrow> vc \<mapsto> vab \<sqsubseteq> vc \<mapsto> va"

  le_distr_R1: "va \<squnion> vb = Some vab \<Longrightarrow> vc \<mapsto> va \<sqsubseteq> vc \<mapsto> vab" |
  le_distr_R2: "va \<squnion> vb = Some vab \<Longrightarrow> vc \<mapsto> vb \<sqsubseteq> vc \<mapsto> vab"
*)
(*
  le_distr_R: "\<lbrakk> v1 \<sqsubseteq> v2 \<mapsto> v3a; v1 \<sqsubseteq> v2 \<mapsto> v3b; v3a \<squnion> v3b = Some v3ab;
                 v3ab \<noteq> v3a; v3ab \<noteq> v3b \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v2 \<mapsto> v3ab" 
*)
inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_fun_fun_inv: "VFun f1 \<sqsubseteq> VFun f2" and
  le_arrow_arrow_inv: "v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'"
  
lemma le_fun_cons_left: "\<lbrakk> VFun f1 \<sqsubseteq> VFun [b]; f2 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (b#f2)" 
  using le_fun_append_left by (metis append.left_neutral append_Cons)

lemma le_fun_cons_right: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f2 \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (b#f2)" 
  using le_fun_append_right by (metis append.simps(1) append_Cons)
    
lemma le_fun_left_cons: "\<lbrakk> VFun [a] \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3; f2 \<noteq> [] \<rbrakk>
   \<Longrightarrow> VFun (a#f2) \<sqsubseteq> VFun f3"
  using le_fun_append_left 
  using le_fun_left_append apply fastforce
  done
    
proposition le_refl_aux: "n = vsize v \<Longrightarrow> v \<sqsubseteq> v"
  apply (induction n arbitrary: v rule: nat_less_induct)
  apply (case_tac v)
   apply force
  apply (rename_tac f)
  apply clarify
  apply (case_tac f)
   apply force
  apply clarify
  apply (rename_tac v v' f)
  apply (case_tac f)
   apply simp apply (rule le_arrow)
    apply (erule_tac x="vsize v" in allE) apply force
    apply (erule_tac x="vsize v'" in allE) apply force
   apply clarify apply (rename_tac v2 v2' f')    
  apply (rule le_fun_left_cons)
    apply (rule le_fun_cons_left)
     apply (rule le_arrow) 
    apply (erule_tac x="vsize v" in allE) apply (erule impE) apply simp apply blast
    apply (erule_tac x="vsize v'" in allE) apply (erule impE) apply simp apply blast
    apply force
    apply (subgoal_tac "vsize (v2 \<mapsto> v2') < vsize (VFun ((v, v') # (v2, v2') # f'))")
       prefer 2 apply force
   apply (subgoal_tac "v2 \<mapsto> v2' \<sqsubseteq> v2 \<mapsto> v2'")
     prefer 2 apply (erule_tac x="vsize (v2 \<mapsto> v2')" in allE) apply force   
   apply (subgoal_tac "vsize (VFun f') < vsize (VFun ((v, v') # (v2, v2') # f'))")
    prefer 2 apply force
   apply (subgoal_tac "VFun f' \<sqsubseteq> VFun f'") prefer 2 apply blast
   prefer 2 apply force
  apply (case_tac f')
   apply clarify
    apply (rule le_fun_cons_right) apply blast
   apply (rule le_fun_left_cons)
    apply (rule le_fun_cons_right)
    apply (rule le_fun_cons_left) apply blast
    apply simp
    apply (subgoal_tac "VFun f' \<sqsubseteq> VFun ([(v,v'),(v2,v2')]@f')")
    prefer 2 apply (rule le_fun_append_right) apply blast
    apply blast
   apply force
    apply simp
  done
    
proposition le_refl[intro!]: "v \<sqsubseteq> v"
  using le_refl_aux by blast

lemma le_bot_inv_aux: fixes v1::val and f1::func
  assumes v12: "v1 \<sqsubseteq> v2" and v2b: "v2 = \<bottom>"
  shows "v1 = \<bottom>"
  using v12 v2b by (induction rule: val_le.induct) auto
      
lemma le_bot_inv[elim!]: "\<lbrakk> f \<sqsubseteq> \<bottom>; f = \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_bot_inv_aux by auto      
    
lemma le_any_nat_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v' = VNat n\<rbrakk> \<Longrightarrow> v = VNat n"
  by (induction rule: val_le.induct) auto
    
proposition le_any_nat_inv[elim!]: "\<lbrakk> v \<sqsubseteq> VNat n; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_any_nat_inv_aux[of v "VNat n" n] apply auto done
  
lemma le_nat_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VNat n\<rbrakk> \<Longrightarrow> v' = VNat n"
  by (induction arbitrary: n rule: val_le.induct) auto
    
proposition le_nat_any_inv[elim!]: "\<lbrakk> VNat n \<sqsubseteq> v; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_nat_any_inv_aux[of "VNat n" v n] apply auto done    

lemma le_fun_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VFun f \<rbrakk> \<Longrightarrow> \<exists> f'. v' = VFun f'"
  by (induction arbitrary: f rule: val_le.induct) auto
  
proposition le_fun_any_inv: "\<lbrakk> VFun f \<sqsubseteq> v; \<And>f'. v = VFun f' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_fun_any_inv_aux by blast

lemma le_fun_elt: assumes v1f: "(v,v') \<in> set f" shows "v\<mapsto>v' \<sqsubseteq> VFun f"
  using v1f apply (induction f) 
   apply force
  apply simp apply (erule disjE)
   apply simp
   apply (case_tac f)
    apply simp apply blast
   apply (subgoal_tac "VFun [a] \<sqsubseteq> VFun ([a]@f)")
   prefer 2 apply (rule le_fun_append_left) apply blast
   apply simp
   apply simp 
   apply (subgoal_tac "v \<mapsto> v' \<sqsubseteq> VFun ([a]@f)")
   prefer 2 apply (rule le_fun_append_right)
    apply simp
   apply simp
    apply simp
  done

lemma le_fun_subset: fixes f1::func shows "\<lbrakk> set f1 \<subseteq> set f2 \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
  apply (induction f1)
  apply force
  apply simp apply clarify
  apply (case_tac f1)
    apply simp apply (rule le_fun_elt) apply blast
  apply (rule le_fun_left_cons)
    apply (rule le_fun_elt) apply blast
   apply blast
    apply simp
    done
       
proposition le_join_left: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v1 \<sqsubseteq> v12" (* incl_L *)
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force
  apply (case_tac v2) apply force
  apply simp
  apply (case_tac "x2 = x2a") apply force 
  apply simp
  apply clarify
    apply (case_tac x2a) apply simp apply blast
  apply (rule le_fun_append_left) apply blast apply blast
  done
    
proposition le_join_right: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v2 \<sqsubseteq> v12" (* incl_R *) 
    apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force
  apply (case_tac v2) apply force
  apply simp
  apply (case_tac "x2 = x2a") apply force
  apply simp
  apply clarify
  apply (case_tac x2)
    apply force
   apply (rule le_fun_append_right) apply auto
  done
    
proposition le_left_join: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" (* glb *)
  apply (case_tac v1) apply (case_tac v2) apply simp
  apply (case_tac "x1 = x1a") apply force apply force
  apply force
  apply (case_tac v2) apply force
  apply simp
  apply (case_tac "x2 = x2a") apply force
  apply simp
  apply clarify
  apply (case_tac v3) apply simp 
   apply force
  apply clarify
  apply (case_tac x2) apply force
  apply (case_tac x2a) apply force
  apply (rule le_fun_left_append)
     apply force
    apply force
  apply blast
  apply blast
  done

proposition le_distr_trad1: fixes v1::val assumes v12: "v1 \<squnion> v2 = Some v12" 
  shows "v \<mapsto> v12 \<sqsubseteq> VFun [(v,v1),(v,v2)]"
  by (smt insert_iff le_distr_L le_fun_elt list.set(2) v12)

proposition le_distr_trad2: fixes v1::val assumes v12: "v1 \<squnion> v2 = Some v12" 
  shows "VFun [(v,v1),(v,v2)] \<sqsubseteq> v \<mapsto> v12"
  using Values.le_refl le_arrow le_fun_left_cons le_join_left le_join_right v12 by force

lemma append_len_geq: "f @ f' = list @ list' \<Longrightarrow> \<not> length f < length list \<Longrightarrow> \<exists>l'. f = list @ l'"
  apply (induction f arbitrary: f' list list')
  apply force
  apply simp
  apply (case_tac list)
    apply auto
  done

lemma join_eq_vsize: "v1 \<squnion> v2 = Some v3 \<Longrightarrow> 
     (v1 = v3) \<or> (v2 = v3) \<or> (vsize v1 < vsize v3 \<and> vsize v2 < vsize v3)"
  apply (case_tac v1) apply (case_tac v2) apply (case_tac "x1 = x1a") apply force
    apply force apply force apply (case_tac v2) apply force apply simp
  apply (case_tac "x2=x2a") apply force apply simp
  apply (case_tac v3) apply force apply simp apply (case_tac x2)
    apply force apply (case_tac x2a) apply force apply force
  done

lemma join_refl[simp]: fixes v::val shows "v \<squnion> v = Some v' \<Longrightarrow> v' = v"
  apply (case_tac v) apply auto done
    
lemma le_left_append_elim_aux: "\<lbrakk> n = fsize f1 + fsize f2 + fsize f3; VFun (f1@f2) \<sqsubseteq> VFun f3 \<rbrakk>
  \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3"
  apply (induction n arbitrary: f1 f2 f3 rule: nat_less_induct)
  apply (case_tac f1)
   apply force
  apply clarify apply (rename_tac v v' f1')
  apply (erule le_fun_fun_inv)
    -- "case 1"
    apply force  
    -- "case 2"
    apply (metis add_less_cancel_left fsize_append_right le_fun_append_left) 
    -- "case 3"
    apply (metis add_less_cancel_left fsize_append_left le_fun_append_right) 
    -- "case 4"
    apply (subgoal_tac "\<exists>f1a'. f1a = (v,v')#f1a'") prefer 2 apply (metis append_eq_Cons_conv)
    apply (erule exE) apply simp
    apply (case_tac "length f1' < length f1a'")    
      -- "case 4b"
      apply (subgoal_tac "\<exists> f1b. f1a' = f1' @ f1b") prefer 2 
      apply (metis append_len_geq less_SucI not_less_eq) apply (erule exE) apply clarify
      apply (subgoal_tac "f2 = f1b@f2a") prefer 2 apply force apply simp
      apply (case_tac f2a) apply force
      apply (subgoal_tac "VFun ((v,v')#f1') \<sqsubseteq> VFun f3 \<and> VFun f1b \<sqsubseteq> VFun f3") prefer 2
      apply (erule_tac x="fsize ((v,v')#f1') + fsize f1b + fsize f3" in allE)
      apply (erule impE) apply force apply (erule_tac x="(v,v')#f1'" in allE)
      apply (erule_tac x="f1b" in allE) apply (erule_tac x="f3" in allE) 
      apply (erule impE) apply force apply (erule impE) apply force
      apply blast
      apply (rule conjI) apply force apply (erule conjE)
      apply (rule le_fun_left_append) apply blast apply blast apply blast apply blast
      -- "case 4b"
      apply (subgoal_tac "\<exists> f1b. f1' = f1a'@f1b") prefer 2 apply (rule append_len_geq)
      apply assumption apply blast apply (erule exE) apply simp
      apply (subgoal_tac "f2a = f1b@f2") prefer 2 apply force apply simp
      apply (subgoal_tac "VFun f1b \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3") prefer 2
      apply (erule_tac x="fsize f1b + fsize f2 + fsize f3" in allE)
      apply force apply (erule conjE) apply (rule conjI)
      apply (subgoal_tac "VFun (((v, v') # f1a') @ f1b) \<sqsubseteq> VFun f3") apply force
      apply (case_tac f1b) apply force
      apply (rule le_fun_left_append) apply assumption apply assumption apply blast 
      apply blast apply assumption
    -- "case 5"
    apply force
    -- "case 6"
  -- "case le_distr_L"
  apply (case_tac f2)
     apply simp apply (rule conjI) apply (rule le_distr_L) apply assumption
       apply blast apply blast apply blast
     apply force apply force apply force
(*  -- "case le_distr_R"
  apply clarify    
  apply (subgoal_tac "v3a = v3ab \<or> v3b = v3ab \<or> (vsize v3a < vsize v3ab \<and> vsize v3b < vsize v3ab)")
    prefer 2 apply (rule join_eq_vsize) apply assumption
  apply (erule disjE) prefer 2
  apply (erule disjE) prefer 2
  apply (erule conjE)+
    
  apply (subgoal_tac "VFun ((v,v')#f1') \<sqsubseteq> v2 \<mapsto> v3a \<and> VFun f2 \<sqsubseteq> v2 \<mapsto> v3a")
  prefer 2 apply (erule_tac x="fsize ((v,v')#f1') + fsize f2 + fsize [(v2,v3a)]" in allE)
  apply (erule impE) apply force apply blast  apply (erule conjE)

  apply (subgoal_tac "VFun ((v,v')#f1') \<sqsubseteq> v2 \<mapsto> v3b \<and> VFun f2 \<sqsubseteq> v2 \<mapsto> v3b")
  prefer 2 apply (erule_tac x="fsize ((v,v')#f1') + fsize f2 + fsize [(v2,v3b)]" in allE)
  apply (erule impE) apply force apply blast  apply (erule conjE)

  apply (rule conjI) apply (rule le_distr_R) prefer 3 apply assumption apply blast apply blast
  apply blast apply blast
  apply (rule le_distr_R) prefer 3 apply assumption apply assumption apply assumption
  apply blast apply blast

  apply blast apply blast
*)
  done

lemma le_left_append_elim[elim!]: "\<lbrakk> VFun (f1@f2) \<sqsubseteq> VFun f3;
   \<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_left_append_elim_aux by blast

lemma join_elim[elim!]: "\<lbrakk> v1 \<squnion> v2 = Some v3; \<And>n. \<lbrakk> v1 = VNat n; v2 = VNat n; v3 = VNat n \<rbrakk> \<Longrightarrow> P;
         \<And> f1 f2. \<lbrakk> v1 = VFun f1; v2 = VFun f2; f1 \<noteq> f2; v3 = VFun (f1@f2) \<rbrakk> \<Longrightarrow> P;
         \<And> f. \<lbrakk> v1 = VFun f; v2 = VFun f; v3 = VFun f \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac v1) apply (case_tac v2) apply simp apply (case_tac "x1=x1a") apply force 
    apply force apply force apply (case_tac v2) apply force apply simp
    apply (case_tac "x2=x2a") apply force apply force
  done

lemma le_arrow_inv_aux: "\<lbrakk> v1 \<sqsubseteq> v2; v1 = v1a \<mapsto> v1b; v2 = v2a \<mapsto> v2b \<rbrakk> \<Longrightarrow> v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v2b"
proof (induction v1 v2 arbitrary: v1a v1b v2a v2b rule: val_le.induct)
  case (le_nat n)
  then show ?case by auto
next
  case (le_bot f)
  then show ?case by auto
next
  case (le_fun_append_left f1 f2 f3)
  then show ?case apply (case_tac f2) apply force apply force done
next
  case (le_fun_append_right f1 f3 f2)
  then show ?case apply (case_tac f2) apply force apply force done
next
  case (le_fun_left_append f1 f3 f2)
  then show ?case apply (case_tac f1) apply force apply (case_tac f2) apply auto done
next
  case (le_arrow v2 v1 v1' v2')
  have "v2 \<sqsubseteq> v1 \<and> v1' \<sqsubseteq> v2'" using le_arrow by blast
  then show "v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v2b" using le_arrow by simp
next
  case (le_distr_L va vb vab vc vd)
  show "v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v2b" 
  proof
    show "v2a \<sqsubseteq> v1a" using le_distr_L by (metis Pair_inject le_left_join list.inject val.inject(2))
  next
    show "v1b \<sqsubseteq> v2b" using le_distr_L by (metis Pair_inject le_left_join list.inject val.inject(2)) 
    qed
(*
next
  case (le_distr_R v1 v2' v3a v3b v3ab)
  have c: "v3a \<squnion> v3b = Some v2b" using le_distr_R by simp
  have x: "v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v3a" using le_distr_R.IH(1)[of v1a v1b v2a v3a] le_distr_R by simp
  have "v1b \<sqsubseteq> v2b" 
    using c apply (rule join_elim)
    using le_distr_R apply force
    using le_distr_R  apply simp apply (case_tac v3ab) apply force apply simp
     apply (metis le_fun_append_left le_nat_any_inv_aux self_append_conv vsize.elims)
    using le_distr_R by blast
  then show "v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v2b" using x by blast
*)
qed

lemma le_arrow_inv[elim!]: "\<lbrakk> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'; \<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_arrow_inv_aux by blast

inductive_cases le_fun_arrow_inv: "VFun f1 \<sqsubseteq> v2 \<mapsto> v2'" and
  le_arrow_fun_inv: "v1 \<mapsto> v1' \<sqsubseteq> VFun f2"

lemma non_empty_pos_fsize[intro!]: "f \<noteq> [] \<Longrightarrow> 0 < fsize f"
    by (case_tac f) auto
  
lemma le_trans_aux: assumes n: "n = vsize v1 + vsize v2 + vsize v3" and
    v1_v2: "v1 \<sqsubseteq> v2" and v2_v3: "v2 \<sqsubseteq> v3"
  shows "v1 \<sqsubseteq> v3"
  using n v2_v3 v1_v2
proof (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  case (1 n)
  show ?case
  proof (cases v1)
    case (VNat n1) then have v1: "v1 = VNat n1" .
    then show ?thesis using 1 by (case_tac v2) auto
  next
    case (VFun f1) then have v1: "v1 = VFun f1" .
    obtain f2 f3 where v2: "v2 = VFun f2" and v3: "v3 = VFun f3"
      using 1 v1 apply (case_tac v2) apply auto apply (case_tac v3) by auto

    have "VFun f2 \<sqsubseteq> VFun f3" using 1(3) v2 v3 by simp
    then show ?thesis
    proof (rule le_fun_fun_inv)
      (* Case 1 le_bot*)
      assume "f2 = []" then show ?thesis using "1.prems"(3) v2 v3 by blast

    next (* Case 2 le_fun_append_left *)
      fix f3a f3b assume f3: "f3 = f3a@f3b" and f2_f3a: "VFun f2 \<sqsubseteq> VFun f3a" and
        f3b_ne: "f3b \<noteq> []"
      then have f1_f3a: "VFun f1 \<sqsubseteq> VFun f3a" using 1(1) 1(2) 1(4) v1 v3 v2 
         apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (VFun f3a)" in allE) 
         apply (erule impE) apply force apply blast done
      then show "v1 \<sqsubseteq> v3" using v1 v3 f3 f3b_ne apply simp apply (rule le_fun_append_left) by auto

    next (* Case 3 le_fun_append_right *)
      fix f3a f3b assume f3: "f3 = f3a@f3b" and f2_f3a: "VFun f2 \<sqsubseteq> VFun f3b" and
        f3b_ne: "f3a \<noteq> []"
      then have f1_f3a: "VFun f1 \<sqsubseteq> VFun f3b" using 1(1) 1(2) 1(4) v1 v3 v2 
         apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (VFun f3b)" in allE) 
        apply (erule impE) apply force apply blast done
      then show "v1 \<sqsubseteq> v3" using v1 v3 f3 f3b_ne apply simp apply (rule le_fun_append_right) by auto

    next (* Case 4 le_fun_left_append *)
      fix f2a f2b assume f2: "f2 = f2a@f2b" and f2a_f3: "VFun f2a \<sqsubseteq> VFun f3"
        and f2b_f3: "VFun f2b \<sqsubseteq> VFun f3" and f2a_ne: "f2a \<noteq> []" and f2b_ne: "f2b \<noteq> []" 
      have f2_f3: "VFun f2 \<sqsubseteq> VFun f3" using f2a_f3 f2b_f3 f2 apply auto
          apply (rule le_fun_left_append) using f2a_ne f2b_ne apply auto done
      
      show "v1 \<sqsubseteq> v3" using 1(4) v1 v2 v3 apply simp
      proof (erule le_fun_fun_inv)
        assume "f1 = []" then show "VFun f1 \<sqsubseteq> VFun f3" by auto
      next
        fix f2c f2d assume f2_cd: "f2 = f2c @ f2d" and f1_f2c: "VFun f1 \<sqsubseteq> VFun f2c"
          and f2b_ne: "f2d \<noteq> []"
        show "VFun f1 \<sqsubseteq> VFun f3"
        proof (cases "length f2a < length f2c")
          case True
          obtain f2c' where f2c: "f2c = f2a @ f2c'" using f2 f2_cd 
            by (metis True add_lessD1 append_len_geq less_imp_add_positive less_not_refl2)
          have f2cp_ne: "f2c' \<noteq> []" using f2c f2 f2_cd True by auto
          obtain f2b' where f2b: "f2b = f2c' @ f2b'" using f2c f2 f2_cd by auto
          have f2cp_f3: "VFun f2c' \<sqsubseteq> VFun f3" using f2b f2b_f3 apply simp 
            apply (erule le_left_append_elim) by blast
          have f2c_f3: "VFun f2c \<sqsubseteq> VFun f3" using f2a_f3 f2cp_f3 f2c f2a_ne f2cp_ne 
            apply simp apply (rule le_fun_left_append) by auto
          show ?thesis using f1_f2c f2c_f3 1(1)
            apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2c) + vsize (VFun f3)" in allE)
            apply (erule impE) using "1.prems"(1) f2_cd f2b_ne v1 v2 v3 apply auto[1] by blast
        next
          case False
          obtain f2a' where f2a: "f2a = f2c @ f2a'" using f2 f2_cd False using append_len_geq by blast
          have f2c_f3: "VFun f2c \<sqsubseteq> VFun f3" using f2a_f3 f2a by auto
          show ?thesis using f1_f2c f2c_f3 1(1)
              apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2c) + vsize (VFun f3)" in allE)
              apply (erule impE) using "1.prems"(1) f2_cd f2b_ne v1 v2 v3 apply auto[1] by blast
        qed
      next
        fix f2c f2d assume f2_cd:"f2 = f2c @ f2d" and f1_f2d: "VFun f1 \<sqsubseteq> VFun f2d" and f2c_ne:"f2c \<noteq> []"          
        show "VFun f1 \<sqsubseteq> VFun f3" 
        proof (cases "length f2a < length f2c")
          case True
          obtain f2c' where f2c: "f2c = f2a @ f2c'" using f2 f2_cd 
            by (metis True add_lessD1 append_len_geq less_imp_add_positive less_not_refl2)
          have f2b: "f2b = f2c' @ f2d" using f2c f2 f2_cd by auto
          have "VFun f2d \<sqsubseteq> VFun f3" using f2b f2b_f3 by auto
          then show ?thesis using f1_f2d 1(1)
            apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2d) + vsize (VFun f3)" in allE)
            apply (erule impE) using "1.prems"(1) f2_cd f2c_ne v1 v2 v3 apply auto[1] by blast
        next
          case False
          obtain f2a' where f2a: "f2a = f2c @ f2a'" using f2 f2_cd False using append_len_geq by blast
          have f2d: "f2d = f2a' @ f2b" using f2a f2 f2_cd by auto
          have f2ap_f3: "VFun f2a' \<sqsubseteq> VFun f3" using f2a f2a_f3 by auto
          show ?thesis
          proof (cases "f2a'")
            case Nil
            then show ?thesis using f1_f2d f2d f2ap_f3 f2b_f3 1(1) apply simp
              apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2b) + vsize (VFun f3)" in allE)
              apply (erule impE) using "1.prems"(1) f2_cd f2c_ne v1 v2 v3 apply auto[1] by blast
          next
            case (Cons a list)
            have "VFun f2d \<sqsubseteq> VFun f3" using f2b_f3 f2d f2b_ne f2ap_f3
              apply simp apply (rule le_fun_left_append) apply blast apply blast
              using Cons apply blast apply blast done
            then show ?thesis using f1_f2d 1(1)
              apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2d) + vsize (VFun f3)" in allE)
              apply (erule impE) using "1.prems"(1) f2_cd f2c_ne v1 v2 v3 apply auto[1] by blast
          qed
        qed
      next
        fix f1a f1b assume f1: "f1 = f1a @ f1b" and f1a_f2: "VFun f1a \<sqsubseteq> VFun f2" and
          f1b_f2: "VFun f1b \<sqsubseteq> VFun f2" and f1a_ne: "f1a \<noteq> []" and f1b_ne: "f1b \<noteq> []"
        have f1a_f3: "VFun f1a \<sqsubseteq> VFun f3" using f1a_f2 f2_f3 1(1)
          apply (erule_tac x="vsize (VFun f1a) + vsize (VFun f2) + vsize (VFun f3)" in allE)
          apply (erule impE) using "1.prems"(1) f1 f1b_ne v1 v2 v3 apply auto[1] by blast
        have f1b_f3: "VFun f1b \<sqsubseteq> VFun f3" using f1b_f2 f2_f3 1(1)
          apply (erule_tac x="vsize (VFun f1b) + vsize (VFun f2) + vsize (VFun f3)" in allE)
          apply (erule impE) using "1.prems"(1) f1 f1a_ne v1 v2 v3 apply auto[1] by blast        
        show "VFun f1 \<sqsubseteq> VFun f3" using f1a_f3 f1b_f3 f1 apply simp apply (rule le_fun_left_append)
            using f1a_ne f1b_ne apply auto done
      next
        fix vc va vb vd assume f1: "f1 = [(va, vb)]" and f2_: "f2 = [(vc, vd)]" and
          vc_va: "vc \<sqsubseteq> va" and vb_vd: "vb \<sqsubseteq> vd"
        have "False" using f2 f2_ f2a_ne f2b_ne by (case_tac f2a) auto
        then show "VFun f1 \<sqsubseteq> VFun f3" ..
      next
        fix va::val and vb vab vc
        assume f1: "f1 = [(vc, vab)]" and vab: "va \<squnion> vb = Some vab" and
          vca_f2: "vc \<mapsto> va \<sqsubseteq> VFun f2" and vcb_f2: "vc \<mapsto> vb \<sqsubseteq> VFun f2" and
          vab_va: "vab \<noteq> va" and vab_vb: " vab \<noteq> vb"
        have vab_size: "vsize va < vsize vab \<and> vsize vb < vsize vab"
          using join_eq_vsize[of va vb vab] vab vab_va vab_vb by blast
        have vca_f3: "vc \<mapsto> va \<sqsubseteq> VFun f3" using vca_f2 f2_f3 1(1) vab_size
          apply (erule_tac x="vsize (vc\<mapsto>va) + vsize (VFun f2) + vsize (VFun f3)" in allE)
          apply (erule impE) using f1 f2 1(2) v1 v2 v3 apply force by blast
        have vcb_f3: "vc \<mapsto> vb \<sqsubseteq> VFun f3" using vcb_f2 f2_f3 1(1) vab_size
          apply (erule_tac x="vsize (vc\<mapsto>vb) + vsize (VFun f2) + vsize (VFun f3)" in allE)
          apply (erule impE) using f1 f2 1(2) v1 v2 v3 apply force by blast        
        show "VFun f1 \<sqsubseteq> VFun f3" using vca_f3 vcb_f3 vab f1 apply simp
          apply (rule le_distr_L) apply assumption apply assumption apply assumption
          using vab_va vab_vb by auto
(*
      next
        fix v2c and v2a::val and v2b v2ab
        assume f2_: "f2 = [(v2c, v2ab)]" and f1_v2ca: "VFun f1 \<sqsubseteq> v2c \<mapsto> v2a" and 
          f1_v2cb: "VFun f1 \<sqsubseteq> v2c \<mapsto> v2b" and v2ab: "v2a \<squnion> v2b = Some v2ab" and
          v2ab_v2a: "v2ab \<noteq> v2a" and v2ab_v2b: "v2ab \<noteq> v2b"
        have "False" using f2 f2_ f2a_ne f2b_ne by (cases f2a) auto
        then show "VFun f1 \<sqsubseteq> VFun f3" ..
*)
      qed
    next (* Case 5 le_arrow *)
      fix v3a v2a v2b v3b assume f2: "f2=[(v2a,v2b)]" and f3: "f3=[(v3a,v3b)]" and
        v3a_v2a: "v3a \<sqsubseteq> v2a" and v2b_v3b: "v2b \<sqsubseteq> v3b"
      show "v1 \<sqsubseteq> v3" using 1(4) v1 v2 v3 f2 apply simp apply (erule le_fun_arrow_inv)
      proof -
        assume f1: "f1 = []"
        then show "VFun f1 \<sqsubseteq> VFun f3" by blast
      next
        fix f2a f2b assume "[(v2a, v2b)] = f2a @ f2b" and "VFun f1 \<sqsubseteq> VFun f2a" and "f2b \<noteq> []"
        then show "VFun f1 \<sqsubseteq> VFun f3" by (case_tac f2a) auto
      next
        fix f2a f2b assume "[(v2a, v2b)] = f2a @ f2b" and "VFun f1 \<sqsubseteq> VFun f2b" and "f2a \<noteq> []"
        then show "VFun f1 \<sqsubseteq> VFun f3" by (case_tac f2a) auto
      next
        fix f1a f2a assume f1: "f1 = f1a @ f2a" and f1a_v2ab: "VFun f1a \<sqsubseteq> v2a \<mapsto> v2b" and 
          f2a_v2ab: "VFun f2a \<sqsubseteq> v2a \<mapsto> v2b" and f1a_ne: "f1a \<noteq> []" and f2a_ne: "f2a \<noteq> []" 
        have v2ab_v3ab: "v2a \<mapsto> v2b \<sqsubseteq> v3a \<mapsto> v3b" using v3a_v2a v2b_v3b by blast
        have f1a_v3ab: "VFun f1a \<sqsubseteq> v3a \<mapsto> v3b" using f1a_v2ab v2ab_v3ab 1(1) 1(2) v1 v2 v3 f1 f2 f3 f2a_ne
          apply (erule_tac x="vsize (VFun f1a) + vsize (v2a \<mapsto> v2b) + vsize (v3a \<mapsto> v3b)" in allE) 
          apply (erule impE) apply force apply blast done
        have f2a_v3ab: "VFun f2a \<sqsubseteq> v3a \<mapsto> v3b" using f2a_v2ab v2ab_v3ab 1(1) 1(2) v1 v2 v3 f1 f2 f3 f1a_ne
          apply (erule_tac x="vsize (VFun f2a) + vsize (v2a \<mapsto> v2b) + vsize (v3a \<mapsto> v3b)" in allE) 
          apply (erule impE) apply force apply blast done
        show "VFun f1 \<sqsubseteq> VFun f3" using f1a_v3ab f2a_v3ab v1 v3 f1 f3 f1a_ne f2a_ne apply simp
            apply (rule le_fun_left_append) apply auto done
      next
        fix v1 v1' assume f1: "f1 = [(v1, v1')]" and v2a_v1: "v2a \<sqsubseteq> v1" and v1p_v2b: "v1' \<sqsubseteq> v2b"
        have v3a_v1: "v3a \<sqsubseteq> v1" using v3a_v2a v2a_v1 1(1) 1(2) v1 v2 v3 f1 f2 f3
          apply (erule_tac x="vsize v3a + vsize v2a + vsize v1" in allE)
          apply (erule impE) apply force apply blast done          
        have v1p_v3b: "v1' \<sqsubseteq> v3b" using 1(1) 1(2) v1 v2 v3 f1 f2 f3 v1p_v2b v2b_v3b
          apply (erule_tac x="vsize v1' + vsize v2b + vsize v3b" in allE)
          apply (erule impE) apply force apply blast done          
        then show "VFun f1 \<sqsubseteq> VFun f3" using f1 f2 f3 v3a_v2a v2b_v3b v2a_v1 v1p_v2b v3a_v1 v1p_v3b
          apply simp apply (rule le_arrow) apply blast apply blast done
      next
        fix va::val and vb vab vc assume "v1 = VFun f1" and "v2 = v2a \<mapsto> v2b" and "v3 = VFun f3" and
          "f2 = [(v2a, v2b)]" and "f1 = [(vc, vab)]" and "va \<squnion> vb = Some vab" and
          "vc \<mapsto> va \<sqsubseteq> v2a \<mapsto> v2b" and "vc \<mapsto> vb \<sqsubseteq> v2a \<mapsto> v2b" and "vab \<noteq> va" and "vab \<noteq> vb" 
        then show "VFun f1 \<sqsubseteq> VFun f3" using f2 f3 v3a_v2a v2b_v3b
          apply simp apply clarify apply simp apply (rule le_arrow)
          using 1(1) 1(2) apply (erule_tac x="vsize v3a + vsize v2a + vsize vc" in allE)
           apply (erule impE) apply force apply blast
          apply (subgoal_tac "vab \<sqsubseteq> v2b") prefer 2 apply (meson le_left_join)
          using 1(1) 1(2) apply (erule_tac x="vsize vab + vsize v2b + vsize v3b" in allE)
           apply (erule impE) apply force apply blast done          
(*
      next
        fix v2c v2d assume f1_v2ac: "VFun f1 \<sqsubseteq> v2a \<mapsto> v2c" and "VFun f1 \<sqsubseteq> v2a \<mapsto> v2d" and
          v2b: "v2c \<squnion> v2d = Some v2b" and v2bc: "v2b \<noteq> v2c" and v2bd: "v2b \<noteq> v2d" 
        have size_v2b: "vsize v2c < vsize v2b \<and> vsize v2d < vsize v2b"
          using join_eq_vsize[of v2c v2d v2b] v2b v2bc v2bd by blast
        have "v2a \<mapsto> v2c \<sqsubseteq> v3a \<mapsto> v3b"
          apply (rule le_arrow) apply (simp add: v3a_v2a)using le_fun_any_inv v2b v2b_v3b by blast
        then show "VFun f1 \<sqsubseteq> VFun f3" using f3 f1_v2ac apply simp
          using 1(1) 1(2) v1 v2 v3 f2 size_v2b
          apply (erule_tac x="vsize (VFun f1) + vsize (v2a\<mapsto> v2c) + vsize (VFun f3)" in allE)
          apply (erule impE) apply force apply blast done
*)
      qed
        
    next (* Case 6 le_distr_L *)
      fix v2a::val and v2b v2ab vc and va::val and vb::val 
      assume f2: "f2 = [(vc, v2ab)]" and v2ab: "v2a \<squnion> v2b = Some v2ab" and
        vca_f3: "vc \<mapsto> v2a \<sqsubseteq> VFun f3" and vcb_f3: "vc \<mapsto> v2b \<sqsubseteq> VFun f3" and
        v2ab_va: "v2ab \<noteq> va" and v2ab_v2b: "v2ab \<noteq> v2b"

      show "v1 \<sqsubseteq> v3" using v1 v2 v3 f2 1(4) apply simp apply (erule le_fun_arrow_inv)
      proof -
        assume f1: "f1 = []"
        then show "VFun f1 \<sqsubseteq> VFun f3" by blast
      next
        fix f2a f3a
        assume vc_f23: "[(vc, v2ab)] = f2a @ f3a" and 
          f1_f2a: "VFun f1 \<sqsubseteq> VFun f2a" and f3a_ne: "f3a \<noteq> []"
        have "f2a = []" using vc_f23 f3a_ne by (cases f2a) auto
        then have "f1 = []" using f1_f2a by blast  
        then show "VFun f1 \<sqsubseteq> VFun f3" by blast
      next
        fix f2' f2a' assume vc_f23: "[(vc, v2ab)] = f2a' @ f2'" and
          f1_f2p: "VFun f1 \<sqsubseteq> VFun f2'" and f2a_ne: "f2a' \<noteq> []"
        have "f2' = []" using vc_f23 f2a_ne by (cases f2a') auto
        then have "f1 = []" using f1_f2p by blast
        then show "VFun f1 \<sqsubseteq> VFun f3" by blast
      next
        fix f1a f2a assume f1: "f1 = f1a @ f2a" and f1a_vcab: "VFun f1a \<sqsubseteq> vc \<mapsto> v2ab" and
          f2a_vcab: "VFun f2a \<sqsubseteq> vc \<mapsto> v2ab" and f1a_ne: "f1a \<noteq> []" and f2a_ne: "f2a \<noteq> []"
        have vcab_f3: "vc \<mapsto> v2ab \<sqsubseteq> VFun f3" using v2ab vca_f3 vcb_f3 v2ab_va v2ab_v2b v2 v3 f2 1(3) by blast
        have f1a_f3: "VFun f1a \<sqsubseteq> VFun f3" using f1a_vcab vcab_f3 1(1) 1(2)
          apply (erule_tac x="vsize (VFun f1a) + vsize (vc \<mapsto> v2ab) + vsize (VFun f3)" in allE)
          apply (erule impE) apply (simp add: f1 f2 f2a_ne non_empty_pos_fsize v1 v2 v3) by blast
        have f2a_f3: "VFun f2a \<sqsubseteq> VFun f3" using f2a_vcab vcab_f3 1(1) 1(2)
          apply (erule_tac x="vsize (VFun f2a) + vsize (vc \<mapsto> v2ab) + vsize (VFun f3)" in allE)
          apply (erule impE) using f1 f1a_ne f2 v1 v2 v3 apply auto[1] by blast
        show "VFun f1 \<sqsubseteq> VFun f3" using f1 f1a_f3 f2a_f3 f1a_ne f2a_ne
          apply simp apply (rule le_fun_left_append) apply auto done            
      next
        fix va vb assume f1: "f1 = [(va, vb)]" and vc_va: "vc \<sqsubseteq> va" and vb_v2ab: "vb \<sqsubseteq> v2ab"          
        show "VFun f1 \<sqsubseteq> VFun f3" sorry
      next
        show "VFun f1 \<sqsubseteq> VFun f3" sorry
(*
      next
        show "VFun f1 \<sqsubseteq> VFun f3" sorry            
*)
      qed
(*        
    next (* Case 7 le_distr_R *)
      fix v3c and v3a::val and v3b v3ab
      assume f3: "f3 = [(v3c, v3ab)]" and 
        f2_3a: "VFun f2 \<sqsubseteq> v3c \<mapsto> v3a" and f2_3b: "VFun f2 \<sqsubseteq> v3c \<mapsto> v3b" and
        v3ab: "v3a \<squnion> v3b = Some v3ab" and v3ab_v3a: "v3ab \<noteq> v3a" and v3ab_v3b: "v3ab \<noteq> v3b"
      have size_v3ab: "vsize v3a < vsize v3ab \<and> vsize v3b < vsize v3ab"
        using join_eq_vsize[of v3a v3b v3ab] v3ab v3ab_v3a v3ab_v3b by auto
      have f1_3ca: "VFun f1 \<sqsubseteq> v3c \<mapsto> v3a" using 1(1) 1(2) 1(4) v1 v2 v3 f2_3a f3
        apply (erule_tac x="vsize v1 + vsize v2 + vsize (v3c \<mapsto> v3a)" in allE)
        apply (erule impE) using size_v3ab apply force apply blast done
      have f1_3cb: "VFun f1 \<sqsubseteq> v3c \<mapsto> v3b"
        using 1(1) 1(2) 1(4) v1 v2 v3 f2_3b f3
        apply (erule_tac x="vsize v1 + vsize v2 + vsize (v3c \<mapsto> v3b)" in allE)
        apply (erule impE) using size_v3ab apply force apply blast done
      show ?thesis using v1 v3 f3 f1_3ca f1_3cb v3ab v3ab_v3a v3ab_v3b
          le_distr_R[of "VFun f1" v3c v3a v3b v3ab] by simp
*)
    qed
  qed
qed
    
lemma le_trans: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq>  v3" 
  using le_trans_aux by blast

proposition mon: fixes v1::val and v2::val and v1'::val and v2'::val and v12::val 
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'" and
    v12: "v1 \<squnion> v2 = Some v12" and v12p: "v1' \<squnion> v2' = Some v12'"
  shows "v12 \<sqsubseteq> v12'"
proof -
  have 3: "v1' \<sqsubseteq> v12'" using le_join_left v12p by auto
  have 4: "v2' \<sqsubseteq> v12'" using le_join_right v12p by auto
  have 5: "v1 \<sqsubseteq> v12'" using 1 3 le_trans by blast
  have 6: "v2 \<sqsubseteq> v12'" using 2 4 le_trans by blast
  show "v12 \<sqsubseteq> v12'" using 5 6 le_left_join[of v1 v12' v2 v12] v12 by simp
qed

datatype coercion = 
  CNat nat
  | CBot func
  | CAppL coercion func
  | CAppR coercion func
  | CLApp coercion coercion
  | CArrowL coercion
  | CArrowR coercion coercion
  | CDist coercion coercion
    
inductive wt_coercion :: "coercion \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" ("\<turnstile> _ : _ \<Rightarrow> _ " [54,54,54] 55) where
  cnat[intro!]: "\<turnstile> CNat n : VNat n \<Rightarrow> VNat n" |
  cbot[intro!]: "\<turnstile> CBot f : \<bottom> \<Rightarrow> VFun f" |
  cappl[intro!]: "\<lbrakk> \<turnstile> c : VFun f1 \<Rightarrow> VFun f2; f3 \<noteq> [] \<rbrakk> \<Longrightarrow> \<turnstile> CAppL c f3 : VFun f1 \<Rightarrow> VFun (f2@f3)"|
  cappr[intro!]: "\<lbrakk> \<turnstile> c : VFun f1 \<Rightarrow> VFun f3; f2 \<noteq> [] \<rbrakk> \<Longrightarrow> \<turnstile> CAppR c f2 : VFun f1 \<Rightarrow> VFun (f2@f3)"|
  clapp[intro!]: "\<lbrakk> \<turnstile> c1 : VFun f1 \<Rightarrow> VFun f3; \<turnstile> c2 : VFun f2 \<Rightarrow> VFun f3; f1 \<noteq> []; f2 \<noteq> [] \<rbrakk>
               \<Longrightarrow> \<turnstile> CLApp c1 c2 : VFun (f1@f2) \<Rightarrow> VFun f3" |
  carrowl[intro!]: "\<turnstile> c : vb \<Rightarrow> va \<Longrightarrow> \<turnstile> CArrowL c : (va\<mapsto>vc) \<Rightarrow> (vb\<mapsto>vc)" |
  carrowr[intro!]: "\<lbrakk> \<turnstile> c1 : vb \<Rightarrow> vd; \<turnstile> c2 : va\<mapsto>vd \<Rightarrow> vc\<rbrakk> \<Longrightarrow> \<turnstile> CArrowR c1 c2 : (va\<mapsto>vb) \<Rightarrow> vc" |
  cdist[intro!]: "\<lbrakk> va\<squnion>vb = Some vab; \<turnstile> c1 : vc\<mapsto>va \<Rightarrow> vd; \<turnstile> c2 : vc\<mapsto>vb \<Rightarrow> vd; vab\<noteq>va; vab\<noteq>vb\<rbrakk>
     \<Longrightarrow> \<turnstile> CDist c1 c2 : (vc \<mapsto> vab) \<Rightarrow> vd"

inductive_cases 
  cnat_inv[elim!]: "\<turnstile> CNat n2 : v2 \<Rightarrow> v3"
  
lemma c_arrow_aux: "\<lbrakk> \<turnstile> c1 : v2 \<Rightarrow> v1; \<turnstile> c2 : v1' \<Rightarrow> v2'\<rbrakk> \<Longrightarrow>
       \<exists>c. \<turnstile> c : v1 \<mapsto> v1' \<Rightarrow> v2 \<mapsto> v2'"
  by (subgoal_tac "\<turnstile> CArrowR c2 (CArrowL c1) : v1\<mapsto>v1' \<Rightarrow> v2\<mapsto>v2'") auto
  
abbreviation mk_arrow :: "coercion \<Rightarrow> coercion \<Rightarrow> coercion" (infix "\<hookrightarrow>" 60) where
  "c1 \<hookrightarrow> c2 \<equiv> CArrowR c2 (CArrowL c1)"  

lemma c_arrow: "\<lbrakk> \<turnstile> c1 : v2 \<Rightarrow> v1; \<turnstile> c2 : v1' \<Rightarrow> v2'\<rbrakk> \<Longrightarrow>
       \<turnstile> c1 \<hookrightarrow> c2 : v1 \<mapsto> v1' \<Rightarrow> v2 \<mapsto> v2'"
  using c_arrow_aux by blast

lemma le_wt_coerce: "v1 \<sqsubseteq> v2 \<Longrightarrow> \<exists>c. \<turnstile> c : v1 \<Rightarrow> v2"
  apply (induction rule: val_le.induct)
  apply (rule_tac x="CNat n" in exI) apply (rule cnat)
  apply (rule_tac x="CBot f" in exI) apply (rule cbot)
  apply (erule exE)+ apply (rule_tac x="CAppL c f3" in exI) apply (rule cappl) apply assumption+      
  apply (erule exE)+ apply (rule_tac x="CAppR c f2" in exI) apply (rule cappr) apply assumption+      
  apply (erule exE)+ apply (rule_tac x="CLApp c ca" in exI) apply (rule clapp) apply assumption+
    apply (erule exE)+ apply (rule_tac x="CArrowR ca (CArrowL c)" in exI) apply (rule carrowr)
    apply assumption apply (rule carrowl) apply assumption
  apply (erule exE)+ apply (rule_tac x="CDist c ca" in exI) apply auto
  done
    
lemma wt_coerce_le: "\<turnstile> c : v1 \<Rightarrow> v2 \<Longrightarrow> v1 \<sqsubseteq> v2"  
  apply (induction rule: wt_coercion.induct)
  apply (rule le_nat)
  apply (rule le_bot)
  apply (rule le_fun_append_left) apply blast apply blast
  apply (rule le_fun_append_right) apply blast apply blast
  apply (rule le_fun_left_append) apply blast apply blast apply blast apply blast
  apply (rule le_arrow) apply blast apply (rule le_refl)
  using Values.le_trans (* OK?? *) apply blast
  apply (rule le_distr_L) apply assumption+
  done

lemma c_fun_cons_left: "\<lbrakk> \<turnstile> c : VFun f1 \<Rightarrow> VFun [b]; f2 \<noteq> [] \<rbrakk> \<Longrightarrow>
    \<turnstile> CAppL c f2 : VFun f1 \<Rightarrow> VFun (b#f2)"
  using cappl[of c f1 "[b]" f2] by simp 
   
lemma c_fun_cons_right: "\<lbrakk> \<turnstile> c : VFun f1 \<Rightarrow> VFun f2 \<rbrakk> \<Longrightarrow>
    \<turnstile> CAppR c [b] : VFun f1 \<Rightarrow> VFun (b#f2)" 
  using cappr[of c f1 f2 "[b]"] by simp

lemma c_fun_left_cons: "\<lbrakk> \<turnstile> c1 : VFun [a] \<Rightarrow> VFun f3; \<turnstile> c2 : VFun f2 \<Rightarrow> VFun f3; f2 \<noteq> [] \<rbrakk>
   \<Longrightarrow> \<turnstile> CLApp c1 c2  : VFun (a#f2) \<Rightarrow> VFun f3"
  using clapp[of c1 "[a]" f3 c2 f2] by simp 

abbreviation c_cons :: "coercion \<Rightarrow> coercion \<Rightarrow> func \<Rightarrow> val \<Rightarrow> val \<Rightarrow> coercion" where
  "c_cons c1 c2 f2 v2 v2' \<equiv> CLApp (CAppL c1 f2) (CAppR c2 [(v2,v2')])"
    
lemma c_cons_good: assumes c1: "\<turnstile> c1 : v1\<mapsto>v1' \<Rightarrow> v2\<mapsto>v2'" and c2: "\<turnstile> c2 : VFun f1 \<Rightarrow> VFun f2"
    and f1_ne: "f1 \<noteq> []" and f2_ne: "f2 \<noteq> []"
  shows "\<turnstile> c_cons c1 c2 f2 v2 v2' : VFun ((v1,v1')#f1) \<Rightarrow> VFun ((v2,v2')#f2)"
proof -
  have 1: "\<turnstile> CAppL c1 f2 : v1\<mapsto>v1' \<Rightarrow> VFun ((v2,v2')#f2)" 
    using c1 f2_ne by (rule c_fun_cons_left)
  have 2: "\<turnstile> CAppR c2 [(v2,v2')] : VFun f1 \<Rightarrow> VFun ((v2,v2')#f2)"
    using c2 by (rule c_fun_cons_right)
  show ?thesis using 1 2 f1_ne by (rule c_fun_left_cons)
qed
  
fun mk_id :: "val \<Rightarrow> coercion" where
  "mk_id (VNat n) = CNat n" |
  "mk_id (VFun f) = 
     (case f of
       [] \<Rightarrow> CBot []
     | [(v,v')] \<Rightarrow> (mk_id v) \<hookrightarrow> (mk_id v')
     | (v1,v1')#f' \<Rightarrow> c_cons (mk_id (v1\<mapsto>v1')) (mk_id (VFun f')) f' v1 v1')"

lemma c_refl[intro!]: "\<turnstile> mk_id v : v \<Rightarrow> v"
  apply (induction rule: mk_id.induct)
  apply force
  apply (case_tac f) apply force  
  apply simp apply (case_tac a) apply simp
  apply (case_tac list) apply simp apply (rule c_arrow)
    apply force apply force
  apply simp apply (case_tac ab) apply simp
  apply (rule c_cons_good) apply force apply force apply force apply force
  done

lemma c_bot_inv_aux: fixes v1::val and f1::func
  assumes v12: "\<turnstile> c : v1 \<Rightarrow> v2" and v2b: "v2 = \<bottom>"
  shows "v1 = \<bottom>"
  using v12 v2b by (induction rule: wt_coercion.induct) auto

lemma c_bot_inv[elim!]: "\<lbrakk> \<turnstile> c : v \<Rightarrow> \<bottom>; v = \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using c_bot_inv_aux by auto      

lemma c_any_nat_inv_aux: "\<lbrakk> \<turnstile> c : v \<Rightarrow> v'; v' = VNat n\<rbrakk> \<Longrightarrow> v = VNat n"
  by (induction rule: wt_coercion.induct) auto
    
proposition c_any_nat_inv[elim!]: "\<lbrakk> \<turnstile> c : v \<Rightarrow> VNat n; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using c_any_nat_inv_aux by auto

lemma c_nat_any_inv_aux: "\<lbrakk> \<turnstile> c : v \<Rightarrow> v'; v = VNat n\<rbrakk> \<Longrightarrow> v' = VNat n"
  by (induction arbitrary: n rule: wt_coercion.induct) auto
    
proposition c_nat_any_inv[elim!]: "\<lbrakk> \<turnstile> c : VNat n \<Rightarrow> v; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using c_nat_any_inv_aux by auto    

lemma c_fun_any_inv_aux: "\<lbrakk> \<turnstile> c : v \<Rightarrow> v'; v = VFun f \<rbrakk> \<Longrightarrow> \<exists> f'. v' = VFun f'"
  by (induction arbitrary: f rule: wt_coercion.induct) auto
  
proposition c_fun_any_inv: "\<lbrakk> \<turnstile> c : VFun f \<Rightarrow> v; \<And>f'. v = VFun f' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using c_fun_any_inv_aux by blast

fun find_entry :: "val \<Rightarrow> val \<Rightarrow> func \<Rightarrow> coercion option" where
  "find_entry v v' [] = None" |
  "find_entry v v' ((v1,v1')#f) = 
     (if v = v1 \<and> v' = v1' then
        (case f of
          [] \<Rightarrow> Some (mk_id (v1 \<mapsto> v1'))
        | (v2,v2')#f' \<Rightarrow> Some (CAppL (mk_id (v\<mapsto>v')) f))
      else
        case (find_entry v v' f) of
          None \<Rightarrow> None
        | Some c \<Rightarrow> Some (CAppR c [(v1,v1')]))"
    
lemma set_find_entry: assumes v1f: "(v,v') \<in> set f" shows "\<exists>c. find_entry v v' f = Some c"
  using v1f apply (induction f) 
   apply force
   apply simp apply (erule disjE)
   apply simp apply (case_tac f) apply force apply force
  apply simp apply clarify apply simp apply (case_tac "v=a \<and> v' = b")
    apply clarify apply (case_tac f) apply force apply force
    apply (case_tac f) apply force apply force
  done
 
lemma c_fun_elt: assumes v1f: "find_entry v v' f = Some c"
  shows "\<turnstile> c : v\<mapsto>v' \<Rightarrow> VFun f"
  using v1f apply (induction v v' f arbitrary: c rule: find_entry.induct) 
   apply force
   apply simp apply (case_tac "v = v1 \<and> v' = v1'")
   apply (case_tac f) apply force
   apply simp apply clarify
   apply (rule c_fun_cons_left) apply blast apply blast
   apply simp apply (case_tac "find_entry v v' f") apply force
   apply simp apply clarify apply (rule c_fun_cons_right) apply auto
   done

fun subset_fun :: "func \<Rightarrow> func \<Rightarrow> coercion option" where
  "subset_fun [] f2 = Some (CBot f2)" |
  "subset_fun ((v,v')#f1) f2 = 
     (case find_entry v v' f2 of 
        None \<Rightarrow> None
     | Some c1 \<Rightarrow>
        (if f1 = [] then Some c1
         else
         (case subset_fun f1 f2 of
           None \<Rightarrow> None
         | Some c2 \<Rightarrow> 
           Some (CLApp c1 c2))))"

lemma c_fun_subset: "subset_fun f1 f2 = Some c \<Longrightarrow> \<turnstile> c : VFun f1 \<Rightarrow> VFun f2"
  apply (induction f1 f2 arbitrary: c rule: subset_fun.induct)
   apply force
  apply simp apply (case_tac "find_entry v v' f2")
  apply force
  apply simp
  apply (case_tac "f1 = []")
    apply simp apply (rule c_fun_elt) apply assumption
  apply (case_tac "subset_fun f1 f2")
   apply force
  apply simp apply clarify apply (subgoal_tac "\<turnstile> aa : VFun f1 \<Rightarrow> VFun f2") prefer 2 apply blast
  apply (rule c_fun_left_cons)
  apply (rule c_fun_elt) apply assumption+
  done
    
lemma set_fun_sub: "set f1 \<subseteq> set f2 \<Longrightarrow> \<exists>c. subset_fun f1 f2 = Some c"
  apply (induction f1)
  apply force
  apply (case_tac f1)
    apply simp apply (case_tac a) apply simp 
  using set_find_entry apply fastforce
  apply simp apply clarify
    
    
(*    
lemma c_trans_aux:     
    assumes n: "n = size c1 + size c2" and
    v1_v2: "\<turnstile> c1 : v1 \<Rightarrow> v2" and v2_v3: "\<turnstile> c2 : v2 \<Rightarrow> v3"
  shows "\<exists> c12. \<turnstile> c12 : v1 \<Rightarrow> v3"
  using n v2_v3 v1_v2
proof (induction n arbitrary: c1 c2 v1 v2 v3 rule: nat_less_induct)
  case (1 n)
  show ?case
  proof (cases c2)
    case (CNat n2)
    then show ?thesis apply (rule_tac x="CNat n2" in exI) using 1
        apply clarify apply simp
  next
    case (CBot x2)
    then show ?thesis sorry
  next
    case (CAppL x31 x32)
    then show ?thesis sorry
  next
    case (CAppR x41 x42)
    then show ?thesis sorry
  next
    case (CLApp x51 x52)
    then show ?thesis sorry
  next
    case (CArrowL x6)
    then show ?thesis sorry
  next
    case (CArrowR x71 x72)
    then show ?thesis sorry
  next
    case (CDist x81 x82)
    then show ?thesis sorry
  qed
qed
*)


end