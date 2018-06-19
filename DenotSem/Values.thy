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
                 vab \<noteq> va; vab \<noteq> vb \<rbrakk> \<Longrightarrow> vc \<mapsto> vab \<sqsubseteq> vd" |
  le_distr_R: "\<lbrakk> v1 \<sqsubseteq> v2 \<mapsto> v3a; v1 \<sqsubseteq> v2 \<mapsto> v3b; v3a \<squnion> v3b = Some v3ab;
                 v3ab \<noteq> v3a; v3ab \<noteq> v3b \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v2 \<mapsto> v3ab" 
(*
  I can prove trans for the following, but it's not equivalent to the trad rule
  le_distr1: "\<lbrakk> v1 \<sqsubseteq> v2a \<mapsto> v2b; v1 \<sqsubseteq> v2a \<mapsto> v2c \<rbrakk> \<Longrightarrow> 
      v1 \<sqsubseteq> VFun [(v2a,v2b), (v2a,v2c)]"
  le_distr2: "\<lbrakk> v1 \<sqsubseteq> v2a \<mapsto> v2; v2b \<squnion> v2c = Some v2 \<rbrakk> \<Longrightarrow> 
      v1 \<sqsubseteq> VFun [(v2a,v2b), (v2a,v2c)]"
*)
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
(*  for le_distr1 apply clarify
  apply (subgoal_tac "VFun ((v,v')#f1') \<sqsubseteq> VFun [(v2a,v2b)] \<and> VFun f2 \<sqsubseteq> VFun [(v2a,v2b)]") prefer 2
  apply (erule_tac x="fsize ((v,v')#f1') + fsize f2 + fsize [(v2a,v2b)]" in allE)
   apply (erule impE) apply force apply blast apply (erule conjE)
  apply (subgoal_tac "VFun ((v,v')#f1') \<sqsubseteq> VFun [(v2a,v2c)] \<and> VFun f2 \<sqsubseteq> VFun [(v2a,v2c)]") prefer 2
  apply (erule_tac x="fsize ((v,v')#f1') + fsize f2 + fsize [(v2a,v2c)]" in allE)
   apply (erule impE) apply force apply blast apply (erule conjE)  
  apply (rule conjI) prefer 2
  apply (rule le_distr) apply blast apply blast
  apply (rule le_distr) apply blast apply blast
*)
(* for le_distr2
  apply clarify
  apply (subgoal_tac "VFun ((v,v')#f1') \<sqsubseteq> VFun [(v2a,v2)] \<and> VFun f2 \<sqsubseteq> VFun [(v2a,v2)]") prefer 2
   apply (erule_tac x="fsize ((v,v')#f1') + fsize f2 + fsize [(v2a,v2)]" in allE)
   apply (erule impE) apply (subgoal_tac "vsize v2 \<le> vsize v2b + vsize v2c") prefer 2
   apply (rule vsize_join) apply blast apply simp
   apply (subgoal_tac "0 < vsize v2a") prefer 2 apply (rule vsize_pos) apply arith
   apply blast apply (erule conjE)
   apply (rule conjI) apply (rule le_distr) apply assumption apply assumption
    apply (rule le_distr) apply assumption apply assumption
*)
  -- "case le_distr_L"
  apply (case_tac f2)
     apply simp apply (rule conjI) apply (rule le_distr_L) apply assumption
       apply blast apply blast apply blast
     apply force apply force apply force
  -- "case le_distr_R"
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
        have f2_f3: "VFun f2 \<sqsubseteq> VFun f3" using f2a_f3 f2b_f3 f2 apply auto
          apply (rule le_fun_left_append) using f2a_ne f2b_ne apply auto done
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
        show "VFun f1 \<sqsubseteq> VFun f3" sorry
      next
        show "VFun f1 \<sqsubseteq> VFun f3" sorry
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
        show "VFun f1 \<sqsubseteq> VFun f3" sorry
      next
        show "VFun f1 \<sqsubseteq> VFun f3" sorry
      qed

    next (* Case 6 le_distr_L *)
      fix v2a::val and v2b v2ab vc and va::val and vb::val 
      assume "f2 = [(vc, v2ab)]" and "v2a \<squnion> v2b = Some v2ab" and
       "vc \<mapsto> v2a \<sqsubseteq> VFun f3" and "vc \<mapsto> v2b \<sqsubseteq> VFun f3" and "v2ab \<noteq> va" and "v2ab \<noteq> v2b"
      show "v1 \<sqsubseteq> v3" sorry

    next (* Case 7 le_distr_R *)
      fix v2 v3aa v3b v3ab
      show ?thesis sorry
    qed
  qed
qed
  
lemma le_trans_aux2: assumes n: "n = vsize v1 + vsize v2 + vsize v3" and
    v1_v2: "v1 \<sqsubseteq> v2" and v2_v3: "v2 \<sqsubseteq> v3"
  shows "v1 \<sqsubseteq> v3"
  using n v2_v3 v1_v2
  apply (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  apply (case_tac v1) apply (case_tac v2) apply force apply force apply (case_tac v2) apply force
  apply (case_tac v3) apply force 
  apply (rename_tac n v1 v2 v3 f1 f2 f3)
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
(* -- "case 6" 
 for distr1
  apply clarify
  apply (subgoal_tac "VFun f1 \<sqsubseteq> v2a \<mapsto> v2b")
  apply (subgoal_tac "VFun f1 \<sqsubseteq> v2a \<mapsto> v2c")
  apply (rule le_distr) apply blast apply blast 
  apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (v2a \<mapsto> v2c)" in allE)
  apply (erule impE) apply force apply blast
  apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (v2a \<mapsto> v2b)" in allE)
  apply (erule impE) apply force apply blast
*)
(* for distr2
 apply clarify 
  apply (subgoal_tac "VFun f1 \<sqsubseteq> v2a \<mapsto> v2b") prefer 2
    apply (erule_tac x="vsize (VFun f1) + vsize (VFun f2) + vsize (v2a \<mapsto> v2b)" in allE)
    apply (erule impE) apply simp apply (subgoal_tac "vsize v2b \<le> vsize v2ba + vsize v2c") prefer 2
    apply (rule vsize_join) apply assumption 
    apply (subgoal_tac "0 < vsize v2a") prefer 2 apply (rule vsize_pos) apply arith apply blast
    apply (rule le_distr) apply assumption apply assumption 
*)
(*  apply clarify
  apply (erule le_arrow_fun_inv)
    -- "case 6.1"     
    apply clarify
*)    
(*  apply (erule le_fun_arrow_inv)
    -- "case 6.1"     
    apply force
    -- "case 6.2"
    apply (case_tac f2a) prefer 2 apply force apply simp
    apply (subgoal_tac "\<bottom> \<sqsubseteq> VFun (f3)") prefer 2 apply blast
    apply (erule_tac x="vsize (VFun f1) + vsize (VFun []) + vsize (VFun f3)" in allE)
    apply (erule impE) apply force apply blast
    -- "case 6.3"
    apply (case_tac f2a) apply force apply simp apply (erule conjE)+ apply clarify
    apply simp
    apply (subgoal_tac "vc \<mapsto> vab \<sqsubseteq> VFun f3") prefer 2 apply (rule le_distr) apply assumption
      apply assumption apply assumption 
    apply (rule le_fun_left_append) 
    apply (erule_tac x="vsize (VFun f1a) + vsize (vc \<mapsto> vab) + vsize (VFun f3)" in allE)
    apply (erule impE) apply force apply blast
    apply (erule_tac x="vsize (VFun f2a) + vsize (vc \<mapsto> vab) + vsize (VFun f3)" in allE)
      apply (erule impE) apply force apply blast
    apply blast
    -- "case 6.4" 
    apply force
    -- "case 6.5"    
    apply clarify 
*)    
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
    apply (erule_tac x="vsize (VFun f1a) + vsize (v1b\<mapsto>v1') + vsize (v2b \<mapsto> v2')" in allE)
      apply (erule impE) apply simp apply (case_tac f2a) apply force apply force apply blast
    apply (erule_tac x="vsize (VFun f2a) + vsize (v1b\<mapsto>v1') + vsize (v2b \<mapsto> v2')" in allE)
      apply (erule impE) apply force
      apply blast apply blast apply blast
   apply clarify apply (rule le_arrow)
    apply (erule_tac x="vsize v2b + vsize v1b + vsize v1c" in allE)
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
    apply (case_tac "length f2c < length f2a")
      -- "case 4.3.a"
      apply (subgoal_tac "\<exists> f2c'. f2a = f2c@f2c'") prefer 2 
      apply (metis add_lessD1 append_len_geq less_imp_add_positive less_not_refl2)
      apply (erule exE) apply simp apply (erule le_left_append_elim)
      apply (subgoal_tac "f3a = f2c' @ f2b") prefer 2 apply force apply simp
      apply (subgoal_tac "VFun (f2c'@f2b) \<sqsubseteq> VFun f3") prefer 2 apply (rule le_fun_left_append)
      apply blast apply assumption apply blast apply blast 
      apply (erule_tac x="vsize (VFun f1) + vsize (VFun (f2c'@f2b)) + vsize (VFun f3)" in allE)      
      apply (erule impE) apply force apply blast
      -- "case 4.3.b"
      apply (subgoal_tac "\<exists>f2a'. f2c = f2a@f2a'") prefer 2 apply (rule append_len_geq)
      apply (subgoal_tac "f2c@f3a = f2a@f2b") prefer 2 apply force
      apply blast apply blast apply (erule exE) apply simp apply clarify apply simp
      apply (erule le_left_append_elim)
      apply (case_tac f2a') apply simp
      apply (erule_tac x="vsize (VFun f1) + vsize (VFun f3a) + vsize (VFun f3)" in allE)      
      apply (erule impE) apply force apply blast
      apply clarify apply (case_tac f2a) apply force
      apply (erule_tac x="vsize (VFun f1) + vsize (VFun f3a) + vsize (VFun f3)" in allE)      
      apply force
    -- "case 4.4" 
    apply clarify apply (subgoal_tac "VFun (f2a@f2b) \<sqsubseteq> VFun f3") prefer 2
    apply (rule le_fun_left_append) apply assumption apply assumption apply blast apply blast
    apply (subgoal_tac "VFun f1a \<sqsubseteq> VFun f3") prefer 2 
    apply (erule_tac x="vsize (VFun f1a) + vsize (VFun (f2a@f2b)) + vsize (VFun f3)" in allE)      
      apply (erule impE) apply force apply blast
    apply (subgoal_tac "VFun f2c \<sqsubseteq> VFun f3") prefer 2 
    apply (erule_tac x="vsize (VFun f2c) + vsize (VFun (f2a@f2b)) + vsize (VFun f3)" in allE)      
      apply (erule impE) apply force apply blast
    apply (rule le_fun_left_append) apply assumption apply assumption apply blast apply blast
    -- "case 4.5"
    apply (case_tac f2a) apply blast apply (case_tac f2b) apply blast apply force
    -- "case 4.6"
    apply (case_tac f2a) apply blast apply (case_tac f2b) apply blast apply clarify
    apply simp apply (erule conjE)+ apply (case_tac list) apply simp apply clarify
    prefer 2 apply force
  (* for le_distr1 rule:
    apply (erule_tac x="vsize (VFun f1) + vsize (v2a \<mapsto> v2b) + vsize (VFun f3)" in allE)   
    apply (erule impE) apply force apply blast
*)
proof -
  fix f1 f3 v2 v2j and v2b::val and v2c a b list aa ba lista
  assume IH: "\<forall>m<Suc (Suc (Suc (fsize f1 + (vsize v2 + vsize v2b + (vsize v2 + vsize v2c)) + fsize f3))).
          \<forall>x xa xb.
             m = vsize x + vsize xa + vsize xb \<longrightarrow> xa \<sqsubseteq> xb \<longrightarrow> x \<sqsubseteq> xa \<longrightarrow> x \<sqsubseteq> xb" and
       v2b_f3: "v2 \<mapsto> v2b \<sqsubseteq> VFun f3" and v2c_f3: "v2 \<mapsto> v2c \<sqsubseteq> VFun f3" and
       f1_v2_v2j: "VFun f1 \<sqsubseteq> v2 \<mapsto> v2j" and v2j: "v2b \<squnion> v2c = Some v2j"
  
  
       
  show "VFun f1 \<sqsubseteq> VFun f3" 
(*
    apply (subgoal_tac "VFun ([(v2a,v2ba)]@[(v2a,v2c)]) \<sqsubseteq> VFun f3") prefer 2
    apply (rule le_fun_left_append) apply assumption apply assumption
    apply blast apply blast
    apply (subgoal_tac "v2a \<mapsto> v2ba \<sqsubseteq> v2a \<mapsto> v2b") prefer 2
      apply (rule le_arrow) apply blast apply (rule le_join_left) apply assumption
    apply (subgoal_tac "v2a \<mapsto> v2c \<sqsubseteq> v2a \<mapsto> v2b") prefer 2
      apply (rule le_arrow) apply blast apply (rule le_join_right) apply assumption
    apply (subgoal_tac "v2a \<mapsto> v2c \<sqsubseteq> VFun ([(v2a, v2ba),(v2a, v2c)])") prefer 2
    apply (rule le_distr) apply assumption apply assumption
    
  apply (erule_tac x="vsize (VFun f1) + vsize (v2a \<mapsto> v2c) + vsize X" in allE)
  done*) sorry
qed
    
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

proposition le_distr_trad: fixes v1::val assumes v12: "v1 \<squnion> v2 = Some v12" 
  shows "v \<mapsto> v12 \<sqsubseteq> VFun [(v,v1),(v,v2)]"
  oops


end