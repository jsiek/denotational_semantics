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
"fsize ((v,v')#t) = 1 + vsize v + vsize v' + fsize t"
  by pat_completeness auto
termination vsize by size_change

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
    
lemma size_fun_mem: "(v,v') \<in> set f \<Longrightarrow> vsize v + vsize v' < fsize f"
  by (induction f) auto  
  
lemma size_fun_mem2: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; (v1,v1') \<noteq> (v2,v2') \<rbrakk>
  \<Longrightarrow> vsize v1 + vsize v1' + vsize v2 + vsize v2' < fsize f"
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
    then have "vsize v1a + vsize v1'a < fsize fa"
      by (meson size_fun_mem)
    then show "vsize v1a + vsize v1'a + vsize a + vsize b < fsize ((a, b) # fa)"
      by auto
qed 
      
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = (if f1 = f2 then Some (VFun f1) else Some (VFun (f1 @ f2)))" |
  "v1 \<squnion> v2 = None"
  
lemma size_fun_mem_join_fst: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; v1 \<squnion> v2 = Some v3 \<rbrakk>
   \<Longrightarrow> vsize v3 < Suc (fsize f)"
  apply (case_tac "v1 = v2")
   apply simp apply (case_tac v1) apply (case_tac v2) apply simp
     apply clarify using size_fun_mem apply force
    apply clarify apply simp using size_fun_mem apply force
  apply (case_tac v1) apply (case_tac v2) apply simp apply force
  apply (case_tac v2) apply force
  apply (subgoal_tac "vsize v1 + vsize v1' + vsize v2 + vsize v2' < fsize f")
    prefer 2 using size_fun_mem2 apply force
  apply simp apply clarify apply simp
  done
    
lemma size_fun_mem_join: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; v1' \<squnion> v2' = Some v3' \<rbrakk>
   \<Longrightarrow> vsize v3' < Suc (fsize f)"
  apply (case_tac "v1' = v2'")
   apply simp apply (case_tac v1') apply (case_tac v2') apply simp
     apply clarify using size_fun_mem apply force
    apply clarify apply simp using size_fun_mem apply force
  apply (case_tac v1') apply (case_tac v2') apply simp apply force
  apply (case_tac v2') apply force
  apply (subgoal_tac "vsize v1 + vsize v1' + vsize v2 + vsize v2' < fsize f")
    prefer 2 using size_fun_mem2 apply force
  apply simp apply clarify apply simp
  done
    
lemma vsize_join: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> vsize v12 \<le> vsize v1 + vsize v2"
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force apply (case_tac v2) apply force apply simp
   apply (case_tac "x2 = x2a") apply force apply force
  done
    
fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> (val list) option" (infix "\<squnion>" 56) where
  "env_join [] [] = Some []" |
  "env_join (v#\<rho>) (v'#\<rho>') = 
      (case v \<squnion> v' of
         None \<Rightarrow> None
      | Some v'' \<Rightarrow> 
           (case \<rho>\<squnion>\<rho>' of
             None \<Rightarrow> None
           | Some \<rho>'' \<Rightarrow> Some (v''#\<rho>'')))" 

  (* Adapted from BCD and EHR subtyping (Lambda Calculus with Types 2013),
     removed refl and trans, changed other rules to compensate and
     enable the proof of refl and trans. *) 
inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) 
    where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" |
  le_bot[intro!]: "\<bottom> \<sqsubseteq> VFun f" |
  le_fun_append_left: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f2; f3 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_fun_append_right: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; f2 \<noteq> []\<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_fun_left_append: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3; f1 \<noteq> []; f2 \<noteq> [] \<rbrakk>
                     \<Longrightarrow> VFun (f1@f2) \<sqsubseteq> VFun f3" |
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" |
  le_distr: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2s; v2' \<squnion> v2'' = Some v2s \<rbrakk> \<Longrightarrow> v1\<mapsto>v1' \<sqsubseteq> VFun [(v2,v2'), (v2,v2'')]"

inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_fun_fun_inv: "VFun f1 \<sqsubseteq> VFun f2" 
(* and
  
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v1" and
  le_any_fun_inv[elim!]: "v \<sqsubseteq> VFun f" and
  le_fun_any_inv[elim!]: "VFun f \<sqsubseteq> v" and
  le_cons_left_inv: " (a # f2) \<sqsubseteq>  f3" and
  le_single_left_inv: "[a] \<sqsubseteq> f" and
  le_single_cons_right_inv: "[a] \<sqsubseteq> (b#f)" and
  le_cons_left_single_inv: "a#f \<sqsubseteq> [b]" and
  le_single_both_inv: "[a] \<sqsubseteq> [b]" and
  le_cons_right_inv: "f1 \<sqsubseteq> (a#f2)" and
  le_cons_cons_inv: "a#f1 \<sqsubseteq> (b#f2)" and
  le_bot_right_inv: "v \<sqsubseteq> \<bottom>"
*)
  
lemma le_fun_cons_left: "\<lbrakk> VFun [a] \<sqsubseteq> VFun [b]; f3 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun [a] \<sqsubseteq> VFun (b#f3)" 
  using le_fun_append_left by (metis append.left_neutral append_Cons)

lemma le_fun_cons_right: "\<lbrakk> VFun [a] \<sqsubseteq> VFun f3 \<rbrakk> \<Longrightarrow> VFun [a] \<sqsubseteq> VFun (b#f3)" 
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
    apply (metis add.commute leI le_arrow less_le_trans list.set_intros(1) not_add_less2 size_fun_mem vsize.simps(2)) 
    apply clarify apply (rename_tac v2 v2' f')    
  apply (rule le_fun_left_cons)
    apply (rule le_fun_cons_left)
    apply (metis add_lessD1 leI le_arrow less_le_trans list.set_intros(1) not_add_less2 size_fun_mem vsize.simps(2))
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

lemma append_len_geq: "f @ f' = list @ list' \<Longrightarrow> \<not> length f < length list \<Longrightarrow> \<exists>l'. f = list @ l'"
  apply (induction f arbitrary: f' list list')
  apply force
  apply simp
  apply (case_tac list)
    apply auto
  done
    
lemma le_left_append_elim_aux: "\<lbrakk> n = fsize f1 + fsize f2 + fsize f3; VFun (f1@f2) \<sqsubseteq> VFun f3 \<rbrakk>
  \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3"
  apply (induction n arbitrary: f1 f2 f3 rule: nat_less_induct)
  apply (case_tac f1)
   apply force
  apply clarify apply (rename_tac v v' f)
  apply (erule le_fun_fun_inv)
    apply force  
    apply clarify apply (metis add_less_cancel_left fsize_append_right le_fun_append_left) 
    apply clarify apply (metis add_less_cancel_left fsize_append_left le_fun_append_right) 
    apply simp
    apply (case_tac f1a) apply force apply simp   
    apply (case_tac f2a) apply force apply simp    
    apply clarify
    apply (case_tac "length f < length list")
    apply (subgoal_tac "\<exists> f'. list = f @ f'") prefer 2 
      apply (metis (no_types, lifting) Suc_eq_plus1 add_lessD1 append_eq_append_conv2 length_append less_add_one not_less_eq)
     apply (erule exE) apply clarify 
     apply (subgoal_tac "fsize ((a,b)#f) + fsize f' + fsize f3 < Suc (vsize a + vsize b + fsize f + fsize f2 + fsize f3)")    
      prefer 2 apply force
     apply (rule conjI)
     apply (metis Cons_eq_appendI)
     apply (subgoal_tac "f2 = f' @ (aa, ba) # lista") prefer 2 apply force
     apply clarify apply (metis append_Cons append_self_conv le_fun_left_append less_not_refl2) 
    apply (subgoal_tac "\<exists> l'. f = list @ l'") 
     apply clarify 
  apply (case_tac l')
      apply simp apply clarify
     apply (subgoal_tac "((ab, bb) # listb) @ f2 = (aa, ba) # lista") prefer 2 apply force
     apply simp apply clarify 
    apply (subgoal_tac "fsize ((aa, ba) # listb) + fsize f2 + fsize f3 < Suc (Suc (vsize a + vsize b + (fsize list + (vsize aa + vsize ba + fsize listb)) + fsize f2 +
                    fsize f3))") prefer 2 apply force
     apply (erule_tac x="fsize ((aa, ba) # listb) + fsize f2 + fsize f3" in allE) 
     apply (erule impE) apply force apply (erule_tac x="(aa, ba) # listb" in allE)
    apply (erule_tac x="f2" in allE) apply (erule_tac x="f3" in allE)
     apply (subgoal_tac "VFun ((aa, ba) # listb) \<sqsubseteq> VFun f3")
     apply (subgoal_tac "VFun (((a, b) # list) @ ((aa, ba) # listb)) \<sqsubseteq> VFun f3") apply force
       apply (rule le_fun_left_append) apply blast apply blast apply blast
       apply blast
      apply force
    apply (rule append_len_geq)
     apply force
    apply force
    apply force
   apply (simp add: le_arrow) 
   apply (simp add: le_distr)
  apply force
    done
    
lemma le_left_append_elim[elim!]: "\<lbrakk> VFun (f1@f2) \<sqsubseteq> VFun f3;
   \<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_left_append_elim_aux by blast
    
lemma le_append_join: "\<lbrakk> VFun f1 \<sqsubseteq> VFun (f2@f3); VFun f2 \<sqsubseteq> VFun f4; VFun f3 \<sqsubseteq> VFun f4\<rbrakk>
    \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f4"
    sorry
    
(*
lemma le_append_commute: "VFun (f1@f2) \<sqsubseteq> VFun f3 \<Longrightarrow> VFun (f2@f1) \<sqsubseteq> VFun f3"
  apply (induction f1 arbitrary: f2 f3)
  apply force
  apply (case_tac f1)
    apply (erule le_fun_fun_inv)
    apply force
    apply (simp add: val_le.le_fun_append_left)
    apply (simp add: val_le.le_fun_append_right)
    apply simp apply clarify apply (rule le_fun_left_append) apply 
    
lemma le_left_cons: "VFun ((a,b)#f1) \<sqsubseteq> VFun f2 \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
  apply (induction f1 arbitrary: a b f2)
  apply force
  apply (case_tac a) apply clarify
  apply (erule le_fun_fun_inv)
    apply force
    apply force
    apply force
    apply simp apply clarify 
    
    sorry
*)
    
lemma le_trans_aux: assumes n: "n = vsize v1 + vsize v2 + vsize v3" and
    v1_v2: "v1 \<sqsubseteq> v2" and v2_v3: "v2 \<sqsubseteq> v3"
  shows "v1 \<sqsubseteq> v3"
  using n v1_v2 v2_v3 
  apply (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  apply (case_tac v2) apply (case_tac v1) apply (case_tac v3) apply force apply force
    apply force apply (case_tac v1) apply force apply (case_tac v2) apply force
    apply (case_tac v3) apply force
  apply clarify
  apply (erule le_fun_fun_inv) 
  -- "case 1" 
  apply blast
  -- "case 2"
  apply simp apply clarify
    apply (subgoal_tac "vsize (VFun x2a) + vsize (VFun f2) + vsize (VFun x2c) < Suc (Suc (Suc (fsize x2a + (fsize f2 + fsize f3) + fsize x2c)))")
    prefer 2 apply simp apply (case_tac f3) apply force apply force
      apply blast apply clarify
  -- "case 3"
  apply (subgoal_tac "vsize (VFun x2a) + vsize (VFun f3) + vsize (VFun x2c) < vsize (VFun x2a) + vsize (VFun (f2 @ f3)) + vsize (VFun x2c)")
      prefer 2 apply simp apply (case_tac f2) apply force apply force
     apply blast
  -- "case 4"
    apply simp apply clarify
    apply (rule le_fun_left_append)
    apply(subgoal_tac "vsize (VFun f1) + vsize (VFun x2b) + vsize (VFun x2c)< Suc (Suc (Suc (fsize f1 + fsize f2 + fsize x2b + fsize x2c)))")
        prefer 2 apply simp apply (case_tac f2) apply force apply force
       apply blast
    apply(subgoal_tac "vsize (VFun f2) + vsize (VFun x2b) + vsize (VFun x2c)< Suc (Suc (Suc (fsize f1 + fsize f2 + fsize x2b + fsize x2c)))")
        prefer 2 apply simp apply (case_tac f1) apply force apply force
      apply blast
     apply blast apply blast
  -- "case 5"
   apply clarify 
   apply (erule le_fun_fun_inv)
    -- "case 5.1" 
        apply force 
    -- "case 5.2" 
    apply clarify apply (rule le_fun_append_left)
    apply (subgoal_tac "vsize (v1a \<mapsto> v1') + vsize (v2a \<mapsto> v2') + vsize (VFun f2) < vsize (v1a \<mapsto> v1') + vsize (v2a \<mapsto> v2') + vsize (VFun (f2 @ f3))")
      prefer 2 apply simp apply (case_tac f3) apply force apply force
        apply blast apply blast
    -- "case 5.3"
    apply clarify apply (rule le_fun_append_right)  
    apply (subgoal_tac "vsize (v1a \<mapsto> v1') + vsize (v2a \<mapsto> v2') + vsize (VFun f3) < vsize (v1a \<mapsto> v1') + vsize (v2a \<mapsto> v2') + vsize (VFun (f2 @ f3))")
      prefer 2 apply simp apply (case_tac f2) apply force apply force
        apply blast apply blast
    -- "case 5.4"
    apply simp apply (case_tac f1) apply force apply force
    -- "case 5.5"
    apply simp apply (rule le_arrow)
    apply (subgoal_tac "vsize v2b + vsize v1b + vsize v1a < Suc (Suc (Suc (Suc (Suc (Suc (vsize v1a + vsize v1' + (vsize v1b + vsize v1'a) +
                                        (vsize v2b + vsize v2'a)))))))")
      prefer 2 apply force
     apply blast
    apply (subgoal_tac "vsize v1' + vsize v1'a + vsize v2'a < Suc (Suc (Suc (Suc (Suc (Suc (vsize v1a + vsize v1' + (vsize v1b + vsize v1'a) +
                                        (vsize v2b + vsize v2'a)))))))")
      prefer 2 apply force
    apply blast
    -- "case 5.6"
   apply simp apply clarify apply (rule le_distr)
     apply (subgoal_tac "vsize v2b + vsize v1b + vsize v1a < Suc (Suc (Suc (Suc (Suc (Suc (Suc (vsize v1a + vsize v1' + (vsize v1b + vsize v1'a) +
                                             (vsize v2b + vsize v2'a + (vsize v2b + vsize v2'')))))))))")
      prefer 2 apply force
     apply blast
    prefer 2 apply blast
    apply (subgoal_tac "vsize v1' + vsize v1'a + vsize v2s < Suc (Suc (Suc (Suc (Suc (Suc (Suc (vsize v1a + vsize v1' + (vsize v1b + vsize v1'a) +
                                             (vsize v2b + vsize v2'a + (vsize v2b + vsize v2'')))))))))")
    prefer 2 apply simp apply (subgoal_tac "vsize v2s \<le> vsize v2'a + vsize v2''")
      prefer 2 apply (rule vsize_join) apply blast apply simp
    apply blast
  -- "case 6"
  apply clarify apply simp
  apply (erule le_fun_fun_inv)
    -- "case 6.1"
    apply force
    -- "case 6.2"
      apply simp apply (rule le_fun_append_left)
      apply (subgoal_tac "v1a \<mapsto> v1' \<sqsubseteq> VFun [(v2a, v2'), (v2a, v2'')]")
      apply (subgoal_tac "vsize (v1a \<mapsto> v1') + vsize (VFun [(v2a, v2'), (v2a, v2'')]) + vsize (VFun f2) < Suc (Suc (Suc (Suc (Suc (Suc (vsize v1a + vsize v1' +
                                        (vsize v2a + vsize v2' + (vsize v2a + vsize v2'')) +
                                        (fsize f2 + fsize f3)))))))")
         prefer 2 apply simp apply (case_tac f3) apply force apply force
        apply blast
       apply (simp add: le_distr)
      apply blast
    -- "case 6.3"
     apply simp apply (rule le_fun_append_right)
      apply (subgoal_tac "v1a \<mapsto> v1' \<sqsubseteq> VFun [(v2a, v2'), (v2a, v2'')]")
      apply (subgoal_tac "vsize (v1a \<mapsto> v1') + vsize (VFun [(v2a, v2'), (v2a, v2'')]) + vsize (VFun f3) < Suc (Suc (Suc (Suc (Suc (Suc (vsize v1a + vsize v1' +
                                        (vsize v2a + vsize v2' + (vsize v2a + vsize v2'')) +
                                        (fsize f2 + fsize f3)))))))")
         prefer 2 apply simp apply (case_tac f2) apply force apply force
        apply blast
       apply (simp add: le_distr)
      apply blast
    -- "case 6.4"
    apply (case_tac f1) apply force    
    apply (case_tac f2) apply force
    apply clarify apply simp apply clarify apply (case_tac list) prefer 2 apply force
    apply clarify apply (case_tac lista) prefer 2 apply force apply simp apply clarify
    apply (subgoal_tac "v1a \<mapsto> v1' \<sqsubseteq> VFun ([(aa,b)]@[(aa,ba)])")
    apply (rule le_append_join)
    apply assumption apply blast apply blast apply (simp add: le_distr)
    -- "case 6.5"
    apply force
    -- "case 6.6"
    apply force
  done

lemma le_trans: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq>  v3" 
  using le_trans_aux by blast
    
proposition mon: fixes v1::val and v2::val and v1'::val and v2'::val and v12::val 
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'" and
    v12: "v1 \<squnion> v2 = Some v12" and v12p: "v1' \<squnion> v2' = Some v12'"
  shows "v12 \<sqsubseteq> v12'"
proof -
  have 3: "v1' \<sqsubseteq> v12'" using le_join_left v12p by blast
  have 4: "v2' \<sqsubseteq> v12'" using le_join_right v12p by blast
  have 5: "v1 \<sqsubseteq> v12'" using 1 3 le_trans by blast
  have 6: "v2 \<sqsubseteq> v12'" using 2 4 le_trans by blast
  show "v12 \<sqsubseteq> v12'" using 5 6 le_left_join v12 by blast
qed

(*
lemma le_fun_append_left_sub: assumes f1_f1p: "VFun f1 \<sqsubseteq> VFun f1'" shows "VFun f1 \<sqsubseteq> VFun (f1'@f2)"
proof -
  have "VFun f1' \<sqsubseteq> VFun (f1'@f2)" using le_fun_append_left by blast
  then show ?thesis using f1_f1p le_trans by blast
qed

lemma le_fun_append_right_sub: assumes f1_f1p: "VFun f2 \<sqsubseteq> VFun f2'" shows "VFun f2 \<sqsubseteq> VFun (f1@f2')"
proof -
  have "VFun f2' \<sqsubseteq> VFun (f1@f2')" using le_fun_append_right by blast
  then show ?thesis using f1_f1p le_trans by blast
qed
  
lemma le_fun_elt: assumes v1f: "(v,v') \<in> set f" shows "v\<mapsto>v' \<sqsubseteq> VFun f"
  using v1f apply (induction f) 
   apply force
  apply simp apply (erule disjE)
   apply simp
   apply (case_tac "f=[a]")
    apply simp using le_fun_left_join apply (metis append_Cons append_Nil le_fun_append_left)
   apply clarify
  using le_join_left apply (metis append.left_neutral append_Cons le_fun_append_left)
  apply (subgoal_tac "v \<mapsto> v' \<sqsubseteq> VFun ([a] @ f)") prefer 2
   apply (rule le_fun_append_right_sub) apply blast
  apply simp
  done
 
lemma le_fun_subset: fixes f1::func shows "\<lbrakk> set f1 \<subseteq> set f2 \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
  apply (induction f1)
  apply force
  apply simp apply clarify
  apply (subgoal_tac "a\<mapsto>b \<sqsubseteq> VFun f2") prefer 2 apply (rule le_fun_elt) apply blast
  using le_fun_left_join by force
    
lemma le_fun_subset_sub: "\<lbrakk> \<forall> a a'. (a,a')\<in>set f1\<longrightarrow> (\<exists> b b'. (b,b')\<in>set f2 \<and> a\<mapsto>a' \<sqsubseteq> b\<mapsto>b') \<rbrakk>
   \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
proof (induction f1 arbitrary: f2)
  case Nil
  then show ?case by auto
next
  case (Cons aa f1')
  obtain a a' where aa: "aa = (a,a')" apply (cases aa) apply auto done
  have 2: "VFun f1' \<sqsubseteq> VFun f2"
  proof -
    have "\<forall>a a'.(a, a') \<in> set f1' \<longrightarrow> (\<exists>b b'.(b, b') \<in> set f2 \<and>
           a \<mapsto> a' \<sqsubseteq> b \<mapsto> b')" using Cons(2) apply auto done
    then show ?thesis using Cons.IH[of f2] by blast 
  qed
  have 3: "VFun [aa] \<sqsubseteq> VFun f2"
  proof -
    obtain b b' where bb_f2: "(b,b') \<in> set f2" and aa_bb: "a\<mapsto>a' \<sqsubseteq> b\<mapsto>b'"
      using Cons(2) aa apply simp apply blast done
    have "VFun [(b,b')] \<sqsubseteq> VFun f2" apply (rule le_fun_subset) using bb_f2 apply auto done
    then show ?thesis using aa_bb le_trans[of "a\<mapsto>a'" "b\<mapsto>b'" "VFun f2"] aa by simp 
  qed
  show "VFun (aa # f1') \<sqsubseteq> VFun f2"
  proof (cases "[aa] = f1'")
    case True
    then show ?thesis using 3 using le_fun_left_join by fastforce
  next
    case False
    then have 1: "VFun [aa] \<squnion> VFun f1' = Some (VFun (aa#f1'))" by simp
    show "VFun (aa # f1') \<sqsubseteq> VFun f2" using 1 2 3 le_left_join by blast
  qed
qed

proposition arrow_join: fixes A::val and B::val and C::val and D::val
  assumes ac: "A \<squnion> C = Some AC" and bd: "B \<squnion> D = Some BD"
  shows "VFun [(AC, BD)] \<sqsubseteq> VFun [(A,B),(C,D)]"
proof -
  have 1: "VFun [(AC,BD)] \<sqsubseteq> VFun [(AC,B),(AC,D)]" using bd by (simp add: le_distr)
  have 2: "VFun [(AC,B),(AC,D)] \<sqsubseteq> VFun [(A,B),(C,D)]" using ac 
    by (smt insert_iff le_arrow le_fun_subset_sub le_join_left le_join_right list.set(2) val_le.le_refl)
  show ?thesis using 1 2 le_trans[of "VFun [(AC,BD)]"] by auto
qed

lemma append_sub: fixes x::func shows "VFun (x @ x) \<sqsubseteq> VFun x"
  apply (induction x)
   apply force
  using le_fun_left_join by blast
    
lemma join_self: fixes C::val shows "\<exists> C'. C \<squnion> C = Some C' \<and> C' \<sqsubseteq> C"
  apply (induction C) apply force
  apply auto
  done

inductive_cases le_fun_one_two_inv: "C \<mapsto> D \<sqsubseteq> VFun [(A1,B1),(A2,B2)]"

fun join_list :: "val list \<Rightarrow> val option" ("\<Squnion>") where
  jl_none: "\<Squnion> [] = None" |
  jl_one: "\<Squnion> [v] = Some v" |
  jl_cons: "\<Squnion> (v#vs) = 
     (case \<Squnion> vs of
        None \<Rightarrow> None
     | Some v' \<Rightarrow> v \<squnion> v')" 

abbreviation equivalent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<approx>" 60) where
  "v \<approx> v' \<equiv> v \<sqsubseteq> v' \<and> v' \<sqsubseteq> v"
  
proposition join_sym: fixes v1::val assumes v12: "v1\<squnion>v2 = Some v12" and v21: "v2\<squnion>v1 = Some v21"
  shows "v12 \<approx> v21"
proof
  have 3: "v1 \<sqsubseteq> v21" using le_join_right v21 by blast
  have 4: "v2 \<sqsubseteq> v21" using le_join_left v21 by blast
  show "v12 \<sqsubseteq> v21" using le_left_join 3 4 v12 by blast
next
  have 1: "v1 \<sqsubseteq> v12" using le_join_left v12 by blast
  have 2: "v2 \<sqsubseteq> v12" using le_join_right v12 by blast  
  show "v21 \<sqsubseteq> v12" using 1 2 le_left_join v21 by blast
qed

proposition arrow_compatible: assumes aa: "a \<approx> a'" and bb: "b \<approx> b'" shows "a\<mapsto>b \<approx> a' \<mapsto> b'"
  by (simp add: aa bb le_arrow)

lemma join_env_nth: "\<lbrakk> \<rho>1 \<squnion> \<rho>2 = Some \<rho>3; x < length \<rho>1; length \<rho>1 = length \<rho>2 \<rbrakk>
                      \<Longrightarrow> \<rho>1 ! x \<squnion> \<rho>2 ! x = Some (\<rho>3 ! x)"
  apply (induction arbitrary: x \<rho>3 rule: env_join.induct)
  apply fastforce
  apply simp apply (case_tac "v \<squnion> v'") apply force apply simp
    apply (case_tac "\<rho> \<squnion> \<rho>'") apply force apply simp
    apply (case_tac x) apply force apply force
  apply force  
  apply force
  done 

lemma join_list_sub: "\<lbrakk> A \<in> set L; \<Squnion>L = Some B \<rbrakk> \<Longrightarrow> A \<sqsubseteq> B"
  apply (induction L arbitrary: A B)
  apply force
  apply simp apply (erule disjE)
  apply (case_tac L) apply force
    apply (case_tac "join_list L") apply auto
    apply (simp add: le_join_left)
  apply (case_tac L) apply force
    apply (case_tac "join_list L") apply auto
    apply (metis le_join_right val_le.le_trans)
    apply (meson le_join_right val_le.le_trans)
  done

lemma join_list_glb: "\<lbrakk> \<forall> A. A \<in> set L \<longrightarrow> A \<sqsubseteq> B; \<Squnion>L = Some As \<rbrakk> \<Longrightarrow> As \<sqsubseteq> B"
proof (induction L arbitrary: As)
  case Nil
  then show ?case by auto
next
  case (Cons A1 L') then have a1l_as: "\<Squnion> (A1 # L') = Some As" by blast
  show ?case
  proof (cases L')
    case Nil
    then show ?thesis using Cons by auto
  next
    case (Cons A2 L'')
    obtain As' where asp: "\<Squnion> L' = Some As'" 
      using Cons a1l_as by (case_tac "\<Squnion> (A2 # L'')") auto
    have as2: "A1 \<squnion> As' = Some As" using asp a1l_as Cons by simp
    have "\<forall>A. A \<in> set L' \<longrightarrow> A \<sqsubseteq> B" by (simp add: Cons.prems(1))
    then have asp_b: "As' \<sqsubseteq> B" using Cons.IH Cons(1) asp by blast
    have a1_b: "A1 \<sqsubseteq> B" by (simp add: Cons.prems(1))
    show ?thesis using as2 a1_b asp_b using le_left_join by blast
  qed
qed
  
lemma join_list_sub_glb: fixes B2s::val and B3s::val and L2::"val list"
  assumes b2s: "\<Squnion> L2 = Some B2s" and b3s: "\<Squnion> L3 = Some B3s"
    and P: "\<forall> B2. B2 \<in> set L2 \<longrightarrow> (\<exists> B3. B3 \<in> set L3 \<and> B2 \<sqsubseteq> B3)"
  shows "B2s \<sqsubseteq> B3s"
proof -
  have 1: "\<forall> B2. B2 \<in> set L2 \<longrightarrow> B2 \<sqsubseteq> B3s"
  proof clarify
    fix B2 assume b2_l2: "B2 \<in> set L2"
    obtain B3 where b3_l3: "B3 \<in> set L3" and b2_b3: "B2 \<sqsubseteq> B3" using P b2_l2 by blast
    have "B3 \<sqsubseteq> B3s" using join_list_sub[of B3 L3 B3s] b3_l3 b3s by blast
    then show "B2 \<sqsubseteq> B3s" using b2_b3 le_trans by blast
  qed  
  show "B2s \<sqsubseteq> B3s" using 1 b2s join_list_glb by blast
qed

lemma upper_bound_join: fixes v1::val and v2::val and v3::val 
  assumes v1_v3: "v1 \<sqsubseteq> v3" and v2_v3: "v2 \<sqsubseteq> v3"
  shows "\<exists> v12. v1 \<squnion> v2 = Some v12"
  using v1_v3 v2_v3 apply (case_tac v3) apply (case_tac v1) apply force
    apply force apply (case_tac v1) apply force apply (case_tac v2) apply force
    apply simp
  done

lemma uppper_bound_join_list:
  assumes ub: "\<forall> v. v \<in> set L \<longrightarrow> v \<sqsubseteq> v3" and ll: "0 < length L"
  shows "\<exists> Ls. \<Squnion>L = Some Ls \<and> Ls \<sqsubseteq> v3"
  using ub ll apply (induction L arbitrary: v3)  
   apply force
  apply simp
  apply (subgoal_tac "\<forall>v. v \<in> set L \<longrightarrow> v \<sqsubseteq> v3") prefer 2 apply blast
  apply (case_tac L)
   apply force
  apply (subgoal_tac " \<exists>Ls. \<Squnion> L = Some Ls \<and> Ls \<sqsubseteq> v3") prefer 2 apply blast
  apply (erule exE) apply (erule conjE)
  apply (subgoal_tac "a \<sqsubseteq> v3") prefer 2 apply force
  apply (subgoal_tac "\<exists> b. a \<squnion> Ls = Some b") prefer 2
  using upper_bound_join apply force
  apply (erule exE) apply simp
  using le_left_join by blast

lemma le_join: fixes v1::val and v2::val
  assumes v1_v2: "v1 \<sqsubseteq> v2" shows "\<exists> v12. v1 \<squnion> v2 = Some v12 \<and> v2 \<approx> v12"
  using v1_v2
  apply (induction rule: val_le.induct)
  -- "case le_refl"
  apply (case_tac v) apply force apply force
  -- "case le_trans" 
  apply (erule exE)+
  apply (subgoal_tac "v1 \<sqsubseteq> v3") prefer 2 using le_trans apply blast
  apply (subgoal_tac "\<exists> v13. v1 \<squnion> v3 = Some v13") prefer 2 
  using upper_bound_join apply blast
        apply (erule exE) apply (rule_tac x=v13 in exI) apply simp
  using le_join_right le_left_join apply blast
  -- "case le_bot"
  apply force
  -- "case le_fun_append_left"
  apply (metis (no_types, lifting) Values.vfun_join le_fun_append_left le_fun_append_right le_left_join val_le.le_refl)  
  -- "case le_fun_append_right"
  apply (metis (no_types, lifting) Values.vfun_join le_fun_append_right le_left_join val_le.le_refl)
  -- "case le_fun_left_join"
  apply (metis (no_types, lifting) Values.vfun_join le_fun_append_right le_fun_left_join val_le.le_trans)
  -- "case le_arrow"      
  apply (metis Values.vfun_join le_arrow le_fun_append_right le_fun_elt le_fun_left_join list.set_intros(1))
  -- "case le_distr"
  by (metis Values.vfun_join le_distr le_fun_append_right le_fun_left_join val_le.le_refl)    
    
*)
end