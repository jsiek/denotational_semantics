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
  le_distr: "\<lbrakk> v1 \<sqsubseteq> v2a \<mapsto> v2b; v1 \<sqsubseteq> v2a \<mapsto> v2c \<rbrakk> \<Longrightarrow> 
      v1 \<sqsubseteq> VFun [(v2a,v2b), (v2a,v2c)]"

inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_fun_fun_inv: "VFun f1 \<sqsubseteq> VFun f2" and
  le_arrow_arrow_inv: "v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'"
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

lemma append_len_geq: "f @ f' = list @ list' \<Longrightarrow> \<not> length f < length list \<Longrightarrow> \<exists>l'. f = list @ l'"
  apply (induction f arbitrary: f' list list')
  apply force
  apply simp
  apply (case_tac list)
    apply auto
  done

(*    
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
  apply clarify
  apply (subgoal_tac "VFun ((v, v') # f) \<sqsubseteq> v2a \<mapsto> v2b")  
    prefer 2 apply (erule_tac x="vsize (VFun ((v,v')#f)) + vsize (VFun f2) + vsize (v2a\<mapsto>v2b)" in allE)
    apply (erule impE) apply simp
 
  done
*)    
lemma le_left_append_elim: "\<lbrakk> VFun (f1@f2) \<sqsubseteq> VFun f3;
   \<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  sorry
(*  using le_left_append_elim_aux by blast
*)    
(*    
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
    apply (rename_tac f3 v1 v1' v2j B C v2' v2 v2'' l)
    apply (subgoal_tac "v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2j") 
    apply (subgoal_tac "v2 \<mapsto> v2j \<sqsubseteq> VFun f3")
    apply (subgoal_tac "vsize (v1 \<mapsto> v1') + vsize (v2 \<mapsto> v2j) + vsize (VFun f3) < Suc (Suc (Suc (Suc (Suc (Suc (vsize v1 + vsize v1' +
                                        (vsize v2 + vsize v2' + (vsize v2 + vsize v2'')) +
                                        fsize f3))))))")
    prefer 2  apply simp apply (subgoal_tac "vsize v2j \<le> vsize v2' + vsize v2''")
       prefer 2 apply (simp add: vsize_join) apply force
      apply blast
    prefer 2 apply (rule le_arrow) apply blast apply blast
    
    apply (subgoal_tac "v1 \<mapsto> v1' \<sqsubseteq> VFun ([(v2,v2')]@[(v2,v2'')])")
       prefer 2 apply (simp add: le_distr)
    apply (subgoal_tac "VFun ([(v2,v2')]@[(v2,v2'')]) \<sqsubseteq> VFun f3")
       prefer 2 apply (rule le_fun_left_append) apply blast apply blast apply blast apply blast
    defer
    -- "case 6.5"
    apply force
    -- "case 6.6"
    apply force
  oops
*)
lemma le_trans: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq>  v3" 
(*  using le_trans_aux by blast
  *)
  oops
    
proposition mon: fixes v1::val and v2::val and v1'::val and v2'::val and v12::val 
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'" and
    v12: "v1 \<squnion> v2 = Some v12" and v12p: "v1' \<squnion> v2' = Some v12'"
  shows "v12 \<sqsubseteq> v12'" oops
(*proof -
  have 3: "v1' \<sqsubseteq> v12'" using le_join_left v12p by blast
  have 4: "v2' \<sqsubseteq> v12'" using le_join_right v12p by blast
  have 5: "v1 \<sqsubseteq> v12'" using 1 3 le_trans by blast
  have 6: "v2 \<sqsubseteq> v12'" using 2 4 le_trans by blast
  show "v12 \<sqsubseteq> v12'" using 5 6 le_left_join v12 by blast
qed
*)

lemma le_arrow_inv[elim!]: "\<lbrakk> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'; \<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule le_arrow_arrow_inv)
  apply (case_tac f2) apply force apply force
  apply (case_tac f3) apply force apply simp apply (case_tac list) apply force
    apply force
  apply (case_tac f1) apply force apply (case_tac f2) apply force apply force
  apply blast
  done

inductive_cases le_fun_arrow_inv: "VFun f1 \<sqsubseteq> v2 \<mapsto> v2'"

lemma non_empty_pos_fsize[intro!]: "f \<noteq> [] \<Longrightarrow> 0 < fsize f"
    by (case_tac f) auto
  
lemma le_trans_aux2: assumes n: "n = vsize v1 + vsize v2 + vsize v3" and
    v1_v2: "v1 \<sqsubseteq> v2" and v2_v3: "v2 \<sqsubseteq> v3"
  shows "v1 \<sqsubseteq> v3"
  using n v2_v3 v1_v2
  apply (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  apply (case_tac v2) apply (case_tac v1) apply (case_tac v3) apply force apply force
    apply force apply (case_tac v1) apply force apply (case_tac v2) apply force
    apply (case_tac v3) apply force
  apply clarify
  apply (rename_tac n v1 v2 v3 f1 f2 f3)
  apply (erule le_fun_fun_inv) 
  -- "case 1" 
  apply blast
  -- "case 2"
  apply clarify apply (rename_tac f3a f3b)
    apply (subgoal_tac "VFun f1 \<sqsubseteq> VFun f3a") prefer 2 
    apply (subgoal_tac "vsize (VFun f1) + vsize (VFun f2) + vsize (VFun f3a) < vsize (VFun f1) + vsize (VFun f2) + vsize (VFun (f3a @ f3b))")
    prefer 2 apply force
    apply blast apply (rule le_fun_append_left) apply blast apply blast
  -- "case 6"     
  prefer 4
  apply clarify
  apply (subgoal_tac "VFun f1 \<sqsubseteq> v2a \<mapsto> v2b")
  apply (subgoal_tac "VFun f1 \<sqsubseteq> v2a \<mapsto> v2c")
  apply (rule le_distr) apply blast apply blast 
  apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (v2a \<mapsto> v2c)" in allE)
  apply (erule impE) apply force apply blast
  apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (v2a \<mapsto> v2b)" in allE)
  apply (erule impE) apply force apply blast
  -- "case 3"
  apply clarify apply (rule le_fun_append_right) 
  apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (VFun f3a)" in allE)
  apply (erule impE) apply simp apply (case_tac f2a) apply force apply force apply force
  apply force
  -- "case 5"
  prefer 2
  apply clarify 
    apply (erule le_fun_arrow_inv)
    apply force
    apply (case_tac f2a) apply force apply force
    apply (case_tac f3a) apply force apply (case_tac f2a) apply force apply force
    apply clarify apply (rule le_fun_left_append) 
    apply (erule_tac x="vsize (VFun f1a) + vsize (v1a\<mapsto>v1') + vsize (v2a \<mapsto> v2')" in allE)
      apply (erule impE) apply simp apply (case_tac f2a) apply force apply force apply blast
    apply (erule_tac x="vsize (VFun f2a) + vsize (v1a\<mapsto>v1') + vsize (v2a \<mapsto> v2')" in allE)
      apply (erule impE) apply force
      apply blast apply blast apply blast
   apply clarify apply (rule le_arrow)
    apply (erule_tac x="vsize v2a + vsize v1a + vsize v1b" in allE)
    apply (erule impE) apply force apply blast
    apply (erule_tac x="vsize v1'a + vsize v1' + vsize v2'" in allE)
    apply (erule impE) apply force apply blast  
  -- "case 4"
  apply clarify 
  apply (rename_tac f2a f2b)
  apply (erule le_fun_fun_inv)
    -- "case 4.1"
    apply blast 
    -- "case 4.2"
    apply (case_tac "length f2c < length f2a")
      -- "case 4.2.a"
      apply (subgoal_tac "\<exists> f2a'. f2a = f2c@f2a'") prefer 2 
      apply (metis add_lessD1 append_len_geq less_imp_add_positive less_not_refl2)
      apply (erule exE) apply simp apply (erule le_left_append_elim)
      apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2c) + vsize (VFun f3)" in allE)
      apply (erule impE) apply simp apply blast
      apply blast
      -- "case 4.2.b" 
      apply (subgoal_tac "\<exists>f2a'. f2c = f2a@f2a'") prefer 2 apply (rule append_len_geq)
      apply (subgoal_tac "f2c@f3a = f2a@f2b") prefer 2 apply force
      apply blast apply blast apply (erule exE) apply simp apply clarify
      apply (erule le_left_append_elim) 
      apply (case_tac f2a') apply simp 
      apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2a) + vsize (VFun f3)" in allE)
      apply (erule impE) apply force apply blast
      apply (subgoal_tac "VFun (f2a@f2a') \<sqsubseteq> VFun f3") prefer 2 apply (rule le_fun_left_append)
          apply blast apply blast apply blast apply blast
      apply (erule_tac x="vsize (VFun f1) + vsize (VFun (f2a@f2a')) + vsize (VFun f3)" in allE)
      apply (erule impE) apply force
      apply blast
    -- "case 4.3"
    
    
    
  oops
    
end