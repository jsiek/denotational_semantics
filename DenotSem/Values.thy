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

lemma size_fun_mem: "(v,v') \<in> set f \<Longrightarrow> vsize v + vsize v' < fsize f"
  by (induction f) auto  
  
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 @ f2))" |
  "v1 \<squnion> v2 = None"
  
fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> (val list) option" (infix "\<squnion>" 56) where
  "env_join [] [] = Some []" |
  "env_join (v#\<rho>) (v'#\<rho>') = 
      (case v \<squnion> v' of
         None \<Rightarrow> None
      | Some v'' \<Rightarrow> 
           (case \<rho>\<squnion>\<rho>' of
             None \<Rightarrow> None
           | Some \<rho>'' \<Rightarrow> Some (v''#\<rho>'')))" 

  (* Adapted from BCD and EHR subtyping (Lambda Calculus with Types 2013) *) 
inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) and
    fun_le :: "func \<Rightarrow> func \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) 
    where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" | 
  le_fun[intro!]: "f1 \<sqsubseteq> f2 \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2" | 

  le_bot[intro!]: "[] \<sqsubseteq> f" |  
  le_cons_left[intro!]: "\<lbrakk>  [p] \<sqsubseteq> f2; f1 \<sqsubseteq> f2; f1 \<noteq> [] \<rbrakk>
                           \<Longrightarrow> (p#f1) \<sqsubseteq> f2" |
  le_cons_right1[intro!]: "\<lbrakk> f1 \<sqsubseteq> [b]; f2 \<noteq> [] \<rbrakk> \<Longrightarrow> f1 \<sqsubseteq> (b#f2)" |
  le_cons_right2[intro!]: "f1 \<sqsubseteq> f2 \<Longrightarrow> f1 \<sqsubseteq> (p#f2)" |
  
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> [(v1,v1')] \<sqsubseteq> [(v2,v2')]" |
  le_distr: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> [(v,v12)] \<sqsubseteq> [(v,v1),(v,v2)]" (* arrow intersect *)
 
inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_fun_fun_inv[elim!]: "VFun f1 \<sqsubseteq> VFun f2" and
  le_any_nat_inv[elim!]: "v \<sqsubseteq> VNat x" and
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
 
lemma le_fun_bot_inv_aux: fixes v1::val and f1::func 
  shows "(v1 \<sqsubseteq> v2 \<longrightarrow> True) \<and> (f1 \<sqsubseteq> f2 \<longrightarrow> f2 = [] \<longrightarrow> f1 = [])"
  by (induction rule: val_le_fun_le.induct) auto

lemma le_fun_bot_inv[elim!]: "\<lbrakk> f \<sqsubseteq> []; f = [] \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_fun_bot_inv_aux by auto      

lemma le_bot[intro!]: "\<bottom> \<sqsubseteq> VFun f" by auto
  
lemma le_fun_refl_aux: "\<lbrakk> \<forall>m<Suc (fsize f). \<forall>x. m = vsize x \<longrightarrow> x \<sqsubseteq> x \<rbrakk> \<Longrightarrow> f \<sqsubseteq> f"
  apply (induction f) 
   apply force 
  apply (case_tac f)
   apply simp apply (case_tac a) 
   apply (subgoal_tac "aa \<sqsubseteq> aa") prefer 2 
    apply (erule_tac x="vsize aa" in allE) apply (erule impE) apply force
    apply force
   apply (subgoal_tac "b \<sqsubseteq> b") prefer 2 
    apply (erule_tac x="vsize b" in allE) apply (erule impE) apply force
    apply force
   apply simp
   apply (rule le_arrow)
    apply assumption apply assumption
   apply (rule le_cons_left)
    prefer 3 apply force
   apply (rule le_cons_right1) 
    apply (case_tac a)
   apply (subgoal_tac "ab \<sqsubseteq> ab") prefer 2 
    apply (erule_tac x="vsize ab" in allE) apply (erule impE) apply force
    apply force
   apply (subgoal_tac "b \<sqsubseteq> b") prefer 2 
    apply (erule_tac x="vsize b" in allE) apply (erule impE) apply force
    apply force
    apply simp apply (rule le_arrow) apply blast apply blast 
   apply force
    apply (rule le_cons_right2)
  by (metis Suc_lessI fsize.elims le_less_trans less_add_Suc2 less_imp_le list.sel(3) list.simps(3))
    
lemma le_refl_aux: fixes v::val shows "n = vsize v \<Longrightarrow> v \<sqsubseteq> v"
  apply (induction n arbitrary: v rule: nat_less_induct)
  apply (case_tac v) apply force apply simp using le_fun_refl_aux apply blast
  done
    
proposition le_refl[intro!]: fixes v::val shows "v \<sqsubseteq> v" using le_refl_aux by blast
 
proposition le_fun_refl[intro!]: fixes f::func shows "f \<sqsubseteq> f" using le_refl_aux by blast
    
lemma le_fun_elt: "a \<in> set f \<Longrightarrow> [a] \<sqsubseteq> f"
  apply (induction f)
   apply force
  apply simp apply (erule disjE)
   apply (case_tac f) apply simp
     apply blast
   apply simp  apply (rule le_cons_right1)
    apply blast
   apply simp
    apply (case_tac f) apply simp 
    apply (rule le_cons_right2) apply auto
  done
    
lemma le_fun_elt_sub: "\<lbrakk> [a] \<sqsubseteq> [b]; b \<in> set f \<rbrakk> \<Longrightarrow> [a] \<sqsubseteq> f"
  apply (induction f)
   apply simp
  apply simp apply (erule disjE)  apply simp
    apply (case_tac f) apply simp
    apply (rule le_cons_right1)
    apply force
   apply force
  apply (case_tac f) apply simp
  apply (rule le_cons_right2)
    apply simp
  done
        
lemma le_fun_subset: fixes f1::func shows "\<lbrakk> set f1 \<subseteq> set f2 \<rbrakk> \<Longrightarrow> f1 \<sqsubseteq> f2"
  apply (induction f1 arbitrary: f2)
   apply force
  apply simp apply (erule conjE)
  apply (case_tac f1)
   apply simp 
   apply (rule le_fun_elt) apply blast
  apply (rule le_cons_left)
   apply (rule le_fun_elt) apply blast
    apply force
   apply force
  done

lemma le_fun_subset_sub: "\<lbrakk> \<forall> a\<in>set f1. \<exists> b \<in> set f2. [a] \<sqsubseteq> [b] \<rbrakk> \<Longrightarrow> f1 \<sqsubseteq> f2"
proof (induction f1 arbitrary: f2)
  case Nil
  then show ?case by auto
next
  case (Cons a f1')
  obtain b where b_f2: "b \<in> set f2" and a_b: "[a] \<sqsubseteq> [b]" using Cons by auto
  have 1: "\<forall>a\<in>set f1'. \<exists>b\<in>set f2. [a] \<sqsubseteq> [b]" using Cons by auto
  show ?case
  proof (cases f1')
    case Nil
    show ?thesis using Nil b_f2 a_b le_fun_elt_sub by auto
  next
    case (Cons a' f1'') then have f1p: "f1' = a' # f1''" .
    show ?thesis
    proof (cases f2)
      case Nil
      then show ?thesis using b_f2 by auto
    next
      case (Cons a list)
      then show ?thesis
        by (metis "1" Cons.IH a_b b_f2 le_cons_left le_fun_elt_sub)
    qed
  qed
qed

(*  
  le_distr messes up the following lemma's. -Jeremy

lemma le_fun_sub_elt: "[a] \<sqsubseteq> f \<Longrightarrow> \<exists> b \<in> set f. [a] \<sqsubseteq> [b]"
  apply (induction f)
   apply force
  apply (case_tac f)
   apply force
  apply (erule le_single_cons_right_inv)
    apply force
   prefer 2 apply force
  apply (subgoal_tac "\<exists>b\<in>set f. [a] \<sqsubseteq> [b]") prefer 2 apply blast apply (erule bexE)
  apply force
  done
    
lemma le_fun_sub_subset_aux: fixes v1::val and f1::func
  shows "(v1 \<sqsubseteq> v2 \<longrightarrow> True) \<and> (f1 \<sqsubseteq> f2 \<longrightarrow> (\<forall>a. a\<in>set f1 \<longrightarrow> (\<exists> b \<in> set f2. [a] \<sqsubseteq> [b])))"
proof (induction rule: val_le_fun_le.induct)
  case (le_cons_left p f2 f1)
  show ?case using le_cons_left.IH(1) le_cons_left.IH(2) by auto
next
  case (le_arrow v2 v1 v1' v2')
  then show ?case by (simp add: val_le_fun_le.le_arrow)
qed auto
    
lemma le_fun_sub_subset: "\<lbrakk> f1 \<sqsubseteq> f2; a\<in>set f1 \<rbrakk> \<Longrightarrow> \<exists> b \<in> set f2. [a] \<sqsubseteq> [b]"
  using le_fun_sub_subset_aux by (simp add: le_fun_sub_subset_aux)
    
lemma le_fun_sub_pair: "\<lbrakk> f1 \<sqsubseteq> f2; (a,b) \<in> set f1 \<rbrakk> \<Longrightarrow> \<exists>a' b'. (a',b')\<in>set f2 \<and> a' \<sqsubseteq> a \<and> b \<sqsubseteq> b'"
  using le_fun_sub_subset[of f1 f2 "(a,b)"] apply auto 
  by (metis fst_conv le_cons_cons_inv le_fun_bot_inv list.simps(3) snd_conv)
*)
  
lemma le_join_left: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v1 \<sqsubseteq> v12" (* incl_L *)
  apply (case_tac v1) apply (case_tac v2) apply (case_tac v12) apply simp
     apply (case_tac "x1=x1a") apply force apply force
    apply simp apply (case_tac "x1=x1a") apply force apply force
   apply (case_tac v12) apply force apply force
  apply (case_tac v2) apply (case_tac v12) apply force apply force
  apply (case_tac v12) apply force
  using le_fun_subset by auto

lemma le_join_right: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v2 \<sqsubseteq> v12" (* incl_R *)
  apply (case_tac v1) apply (case_tac v2) apply (case_tac v12) apply simp
     apply (case_tac "x1=x1a") apply force apply force
    apply simp apply (case_tac "x1=x1a") apply force apply force
   apply (case_tac v12) apply force apply force
  apply (case_tac v2) apply (case_tac v12) apply force apply force
  apply (case_tac v12) apply force
  using le_fun_subset by auto

    
lemma le_left_join: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" (* glb *)
  sorry
    (*
  apply (case_tac v1) apply (case_tac v2) apply (case_tac v12) apply simp
     apply (case_tac "x1=x1a") apply force apply force
    apply simp apply (case_tac "x1=x1a") apply force apply force
   apply (case_tac v12) apply force apply force
  apply (case_tac v2) apply (case_tac v12) apply force apply force
  apply (case_tac v12) apply force
  apply (case_tac v3) apply force apply simp
  by (metis Un_iff le_fun le_fun_fun_inv le_fun_sub_subset_aux le_fun_subset_sub set_append)
*)    
lemma le_fun_trans_aux:
   fixes f1::func and f2::func and f3::func
   assumes IH: "\<forall>m < vsize (VFun f1) + vsize (VFun f2) + vsize (VFun f3).
          (\<forall>v1 v2 v3. m = vsize v1 + vsize v2 + vsize v3 
          \<longrightarrow> v1 \<sqsubseteq> v2 \<longrightarrow> v2 \<sqsubseteq> v3 \<longrightarrow> v1 \<sqsubseteq> v3)"
    and f1_f2: "f1 \<sqsubseteq> f2" and f2_f3: "f2 \<sqsubseteq> f3"
  shows "f1 \<sqsubseteq> f3"
  sorry
(*    
proof -
  have 1: "\<forall>a\<in>set f1. \<exists> b \<in> set f2. [a] \<sqsubseteq> [b]" using f1_f2 le_fun_sub_subset by simp
  have 2: "\<forall>a\<in>set f2. \<exists> b \<in> set f3. [a] \<sqsubseteq> [b]" using f2_f3 le_fun_sub_subset by simp
  have 3: "\<forall>a\<in>set f1. \<exists> b \<in> set f3. [a] \<sqsubseteq> [b]"
  proof clarify
    fix v1 v1' assume v1_f1: "(v1,v1') \<in> set f1"
    obtain v2 v2' where v2_f2: "(v2,v2') \<in> set f2" and v1_v2: "[(v1,v1')] \<sqsubseteq> [(v2,v2')]"
      using 1 v1_f1 by auto
    obtain v3 v3' where v3_f3: "(v3,v3') \<in> set f3" and v2_v3: "[(v2,v2')] \<sqsubseteq> [(v3,v3')]"
      using 2 v2_f2 by auto
    have s_v1_f1: "vsize v1 + vsize v1' < fsize f1" using v1_f1 size_fun_mem by simp
    have s_v2_f2: "vsize v2 + vsize v2' < fsize f2" using v2_f2 size_fun_mem by simp
    have s_v3_f3: "vsize v3 + vsize v3' < fsize f3" using v3_f3 size_fun_mem by simp
    have v1p_v2p: "v1' \<sqsubseteq> v2'" using v1_v2 apply (rule le_single_both_inv) by auto
    have v2p_v3p: "v2' \<sqsubseteq> v3'" using v2_v3 apply (rule le_single_both_inv) by auto
    have v1p_v3p: "v1' \<sqsubseteq> v3'" using v1p_v2p v2p_v3p IH
        apply (erule_tac x="vsize v1' + vsize v2' + vsize v3'" in allE)
      apply (erule impE) using s_v1_f1 s_v2_f2 s_v3_f3 apply force apply blast done
    have v2_v1: "v2 \<sqsubseteq> v1" using v1_v2 apply (rule le_single_both_inv) by auto
    have v3_v2: "v3 \<sqsubseteq> v2" using v2_v3 apply (rule le_single_both_inv) by auto
    have v3_v1: "v3 \<sqsubseteq> v1" using v2_v1 v3_v2 IH
        apply (erule_tac x="vsize v3 + vsize v2 + vsize v1" in allE)
      apply (erule impE) using s_v1_f1 s_v2_f2 s_v3_f3 apply force by blast
    show "\<exists>b\<in>set f3. [(v1, v1')] \<sqsubseteq> [b]" by (meson le_arrow v1p_v3p v3_f3 v3_v1)
  qed
  show ?thesis using 3 le_fun_subset_sub by blast
qed
*)

lemma le_val_trans_aux:
  fixes v1::val and v2::val and v3::val
  assumes n: "n = vsize v1 + vsize v2 + vsize v3" and
    v1_v2: "v1 \<sqsubseteq> v2" and v2_v3: "v2 \<sqsubseteq> v3" shows "v1 \<sqsubseteq> v3" using n v1_v2 v2_v3
proof (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  case (1 n)
  then show ?case
    apply (case_tac v1) apply (case_tac v2) apply (case_tac v3) apply fastforce+
    apply (case_tac v2) apply fastforce apply (case_tac v3) apply fastforce
    apply simp apply (rule le_fun) apply (erule le_fun_fun_inv)+
      using le_fun_trans_aux apply auto done
qed

proposition le_trans[trans]: fixes v2::val shows "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  using le_val_trans_aux by blast

lemma le_fun_trans:
   fixes f1::func and f2::func and f3::func
   assumes f1_f2: "f1 \<sqsubseteq> f2" and f2_f3: "f2 \<sqsubseteq> f3" shows "f1 \<sqsubseteq> f3"
proof -
  have 1: "VFun f1 \<sqsubseteq> VFun f2" using f1_f2 by auto 
  have 2: "VFun f2 \<sqsubseteq> VFun f3" using f2_f3 by auto
  have "VFun f1 \<sqsubseteq> VFun f3" using 1 2 le_trans by blast
  then show "f1 \<sqsubseteq> f3" by auto
qed    

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
  by (simp add: aa bb le_arrow le_fun)

lemma append_sub: fixes x::func shows " x @ x \<sqsubseteq> x"
  apply (induction x)
  apply force
  by (metis Un_iff le_fun_refl le_fun_subset_sub set_append)
    
lemma join_self: fixes C::val shows "\<exists> C'. C \<squnion> C = Some C' \<and> C' \<sqsubseteq> C"
  apply (induction C) apply force
  apply auto apply (rule append_sub) 
  done
    
theorem beta_sound_binary: fixes A1::val and A2::val and B1::val and B2::val 
  assumes cd_ab: "C\<mapsto>D \<sqsubseteq> AB" and ab: "(A1\<mapsto>B1)\<squnion>(A2\<mapsto>B2) = Some AB"
  shows "(A1 \<sqsubseteq> C \<and> D \<sqsubseteq> B1) \<or> (A2 \<sqsubseteq> C \<and> D \<sqsubseteq> B2 ) 
      \<or> (\<exists>A3 B3. A3 \<sqsubseteq> C \<and> A1 \<squnion> A2 = Some A3 \<and> D \<sqsubseteq> B3 \<and> B1 \<squnion> B2 = Some B3)"
  using cd_ab ab apply simp
  apply (subgoal_tac "VFun [(C,D)] \<sqsubseteq> VFun [(A1,B1),(A2,B2)]") prefer 2 apply fastforce
  apply (erule le_fun_fun_inv) apply (erule le_single_cons_right_inv)
  apply (metis Pair_inject le_cons_left_single_inv le_fun_bot_inv not_Cons_self2)
  apply (metis Pair_inject le_fun_bot_inv le_single_both_inv list.simps(3))  
  apply simp
  apply (rule disjI2) apply (rule disjI2)
  apply clarify
    apply (subgoal_tac "\<exists> C'. C \<squnion> C = Some C' \<and> C' \<sqsubseteq> C") apply (erule exE)
   apply (rule_tac x="C'" in exI) apply (rule conjI) apply blast
   apply (rule conjI) apply blast
   apply (rule_tac x=D in exI) apply force
    using join_self apply blast
  done

fun select :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" where
  "select xs [] = []" |
  "select xs (i#I) = (xs!i)#(select xs I)"

fun join_list :: "val list \<Rightarrow> val option" where
  "join_list [v] = Some v" |
  "join_list (v#vs) = 
     (case join_list vs of
        None \<Rightarrow> None
     | Some v' \<Rightarrow> v \<squnion> v')" 
 
lemma select_append_map[simp]: "select (f1 @ f2) (map (\<lambda>i. i+length f1) I) = select f2 I"
  apply (induction I) apply fastforce by (simp add: nth_append)

lemma select_cons_map[simp]: "select (a#f2) (map Suc I) = select f2 I"
  using select_append_map[of "[a]" f2] by fastforce 
      
theorem beta_sound: fixes C::val and D::val and f::func 
  assumes cd_f: "C\<mapsto>D \<sqsubseteq> VFun f"
  shows "\<exists> I A B. 0 < length I \<and> join_list (map fst (select f I)) = Some A \<and> A \<sqsubseteq> C
                           \<and> join_list (map snd (select f I)) = Some B \<and> D \<sqsubseteq> B"
  using cd_f 
proof (induction f)
  case Nil
  then show ?case by auto
next
  case (Cons a f)
  have "[(C, D)] \<sqsubseteq> a # f " using Cons(2) by (meson le_fun_fun_inv)
  then show ?case
  proof (rule le_single_cons_right_inv)
    assume "[(C, D)] \<sqsubseteq> [a]"
    then show ?thesis
      apply (case_tac a)
      apply (rule_tac x="[0]" in exI)
      apply simp 
      apply (metis (no_types, lifting) fst_conv le_fun_bot_inv le_single_cons_right_inv not_Cons_self2 sndI)
      done
  next
    assume "[(C, D)] \<sqsubseteq> f"
    then show ?thesis using Cons
      apply (subgoal_tac "\<exists>I A B.
           0 < length I \<and>
           join_list (map fst (select f I)) = Some A \<and>
           A \<sqsubseteq> C \<and>
           join_list (map snd (select f I)) = Some B \<and> D \<sqsubseteq> B") prefer 2 apply force
      apply (erule exE)+ apply (erule conjE)+
      apply (rule_tac x="map Suc I" in exI)
      apply (rule_tac x=A in exI)
      apply (rule_tac x=B in exI)
      apply (rule conjI) apply fastforce apply (rule conjI)
       apply (subgoal_tac "select (a # f) (map Suc I) = select f I") prefer 2 apply fastforce
       apply fastforce
      apply force
      done
  next
    fix v2::val and v1 and v1'::val and v2'
    assume "(C, D) = (v1, v1')" and "v2 \<sqsubseteq> v1" and "v1' \<sqsubseteq> v2'" and "a = (v2, v2')"
      and "f = []"
    then show ?thesis sorry
  next
    fix v1::val and v2 v12 v assume "(C, D) = (v, v12)" and "v1 \<squnion> v2 = Some v12" and "a = (v, v1)"
      and "f = [(v, v2)]"
    show ?thesis sorry
  qed    
qed
(*
  apply (erule le_fun_fun_inv)
  apply (erule le_single_cons_right_inv) 
    -- "Case 1" 
    apply (case_tac a)
    apply (rule_tac x="[0]" in exI)
    apply simp 
  apply (metis (no_types, lifting) fst_conv le_fun_bot_inv le_single_cons_right_inv not_Cons_self2 sndI)
    apply (subgoal_tac "\<exists>I A B.
           0 < length I \<and>
           join_list (map fst (select f I)) = Some A \<and>
           A \<sqsubseteq> C \<and>
           join_list (map snd (select f I)) = Some B \<and> D \<sqsubseteq> B") prefer 2 apply force
   apply (erule exE)+ apply (erule conjE)+
    apply (rule_tac x="map Suc I" in exI)
    apply (rule_tac x=A in exI)
   apply (rule_tac x=B in exI)
    apply (rule conjI) apply fastforce apply (rule conjI)
    apply (subgoal_tac "select (a # f) (map Suc I) = select f I") prefer 2 apply fastforce
    apply fastforce
  -- "Case 2"
   apply (rule conjI) apply assumption apply (rule conjI) prefer 2 apply assumption
    apply fastforce
  -- "Case 3" 
  apply (rule_tac x="[0]" in exI) 
  apply clarify apply (rule_tac x=v2 in exI) apply (rule_tac x=v2' in exI)
   apply simp
  -- "Case 4"
  sorry
*)

section "Consistency"

inductive consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 52) and
    inconsistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "!~" 52) where
  vnat_consis[intro!]: "(VNat n) ~ (VNat n)" |
  vfun_consis[intro!]: "\<lbrakk> \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f1 \<and> (v2,v2') \<in> set f2 \<longrightarrow>
                        (v1 ~ v2 \<and> v1' ~ v2') \<or> v1 !~ v2 \<rbrakk> \<Longrightarrow> (VFun f1) ~ (VFun f2)" |
  vnat_inconsis[intro!]: "n \<noteq> n' \<Longrightarrow> (VNat n) !~ (VNat n')" |
  vfun_inconsis[intro!]: "\<lbrakk> (v1, v1') \<in> set f1; (v2, v2') \<in> set f2; v1 ~ v2; v1' !~ v2' \<rbrakk> 
                         \<Longrightarrow> (VFun f1) !~ (VFun f2)" |
  vnat_vfun_inconsis[intro!]: "VNat n !~ VFun f" |
  vfun_vnat_inconsis[intro!]: "VFun f !~ VNat n"

inductive_cases 
  vnat_consis_inv[elim!]: "VNat n ~ VNat n'" and
  vfun_consis_inv[elim!]: "VFun f ~ VFun f'" and
  vnat_inconsis_inv[elim!]: "VNat n !~ VNat n'" and
  vfun_inconsis_inv[elim!]: "VFun f !~ VFun f'" and
  vnat_vfun_consis_inv[elim!]: "VNat n ~ VFun f" and
  vfun_vnat_consis_inv[elim!]: "VFun f ~ VNat n"
  
inductive consis_env :: "val list \<Rightarrow> val list \<Rightarrow> bool" where
  consis_env_nil[intro!]: "consis_env [] []" |
  consis_env_cons[intro!]: "\<lbrakk> v ~ v'; consis_env \<rho> \<rho>' \<rbrakk> \<Longrightarrow> consis_env (v#\<rho>) (v'#\<rho>')" 

definition is_fun :: "func \<Rightarrow> bool" where
  "is_fun f \<equiv> VFun f ~ VFun f"
    
inductive is_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> is_fun f; \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v' \<rbrakk>
                        \<Longrightarrow> is_val (VFun f)"
inductive_cases
  vfun_is_val_inv[elim!]: "is_val (VFun f)"

definition val_env :: "val list \<Rightarrow> bool" where
  "val_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> is_val (\<rho>!k)"

definition env_le :: "val list \<Rightarrow> val list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "(\<rho>::val list) \<sqsubseteq> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k \<sqsubseteq> \<rho>'!k)" 
    
lemma consis_and_not_consis: "(v ~ v' \<longrightarrow> \<not> (v !~ v')) \<and> (v !~ v' \<longrightarrow> \<not>(v ~ v'))"
  by (induction rule: consistent_inconsistent.induct) blast+ 
        
lemma consis_or_not_aux: "\<forall> v v'. n = vsize v \<longrightarrow> v ~ v' \<or> v !~ v'"
 apply (induction n rule: nat_less_induct)
 apply (rule allI)+ apply (rule impI)
 apply (case_tac v)    
  apply (case_tac v')
    apply force
   apply force
  apply (case_tac v')
   apply force
  apply simp
  apply auto
    apply (metis add_lessD1 less_SucI size_fun_mem)
    apply (metis add_lessD1 less_SucI size_fun_mem)
    apply (metis add_lessD1 less_SucI size_fun_mem)
  by (metis add.commute add_lessD1 less_SucI size_fun_mem)    
    
lemma consis_or_not: "v ~ v' \<or> v !~ v'"
  using consis_or_not_aux by blast
  
lemma inconsis_not_consis[simp]: "(v1 !~ v2) = (\<not> (v1 ~ v2))"
  using consis_and_not_consis consis_or_not by blast
  
lemma consis_refl[intro!]: "is_val v \<Longrightarrow> v ~ v"
  apply (induction rule: is_val.induct)
  apply blast
  apply (simp only: is_fun_def)
  done

lemma consis_inconsis_sym: "(v ~ v' \<longrightarrow> v' ~ v) \<and> (v !~ v' \<longrightarrow> \<not>(v' ~ v))"
  apply (induction rule: consistent_inconsistent.induct) 
  apply blast
  using consis_or_not apply blast
  apply blast    
  using consis_and_not_consis apply blast
  apply blast    
  apply blast    
  done
    
lemma consis_sym[sym]: "v ~ v' \<Longrightarrow> v' ~ v"
  using consis_inconsis_sym by blast

lemma consis_join_val:
  assumes v1_v2: "v1 ~ v2" and v_v1: "is_val v1" and v_v2: "is_val v2"
  shows "\<exists> v12. (v1 \<squnion> v2) = Some v12 \<and> is_val v12"
proof (cases v1)
  case (VNat n1) then have v1: "v1 = VNat n1" .
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    show ?thesis using v1 VNat v1_v2 by auto
  next
    case (VFun f2)
    have "False" using v1_v2 v1 VFun by auto 
    then show ?thesis ..
  qed
next
  case (VFun f1) then have v1: "v1 = VFun f1" .
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    show ?thesis using v1 VNat v1_v2 by auto
  next
    case (VFun f2)
    let ?v12 = "VFun (f1@f2)"
    have j12: "v1 \<squnion> v2 = Some ?v12" using v1 VFun by simp
    have v_v12: "is_val ?v12"
      apply (rule vfun_is_val)
       apply (simp only: is_fun_def)
       apply (rule vfun_consis) 
       apply (metis (mono_tags, lifting) Un_iff VFun consis_refl consis_sym set_append v1 v1_v2 v_v1 v_v2 vfun_consis_inv)
      using v_v1 v_v2 using VFun v1 apply auto
      done
    show ?thesis using j12 v_v12 by blast
  qed
qed

lemma consis_le_inconsis_le:
  "(v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1 \<sqsubseteq> v1' \<and> v2 \<sqsubseteq> v2' \<longrightarrow> v1 ~ v2))
  \<and> (v1' !~ v2' \<longrightarrow> (\<forall> v1 v2. v1' \<sqsubseteq> v1 \<and> v2' \<sqsubseteq> v2 \<longrightarrow> v1 !~ v2))"
  sorry
    (*
  apply (induction rule: consistent_inconsistent.induct)
  apply blast
  defer
  apply blast
  defer
  apply blast
  apply blast

  apply (rule allI)+
  apply (rule impI) apply (erule conjE)
  apply (case_tac v1) apply force
  apply (case_tac v2) apply force
  apply simp apply (rule vfun_consis)
  apply (rule allI)+ apply (rule impI) apply (erule conjE)

  apply (erule le_fun_fun_inv)+
   apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f1 \<and> u \<sqsubseteq> v1a \<and> v1' \<sqsubseteq> u'")
   prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
   apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f2 \<and> u \<sqsubseteq> v2a \<and> v2' \<sqsubseteq> u'")
   prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption

   apply (erule exE)+
   apply (erule conjE)+
    
   apply (erule_tac x=u in allE)    
   apply (erule_tac x=u' in allE)    
   apply (erule_tac x=ua in allE)    
   apply (erule_tac x=u'a in allE)    

  apply (erule impE) apply force
  apply (erule disjE)
    apply force
  apply (rule disjI2)
    apply force 
    
  apply (rule allI)+
  apply (rule impI) apply (erule conjE)
  apply (case_tac v1a) apply force 
  apply (case_tac v2a) apply force
  apply clarify
  
  apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f2a \<and> u \<sqsubseteq> v1 \<and> v1' \<sqsubseteq> u'")
  prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
  apply (subgoal_tac "\<exists> v v'. (v,v') \<in> set f2b \<and> v \<sqsubseteq> v2 \<and> v2' \<sqsubseteq> v'")
  prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
  apply (erule exE)+ apply (erule conjE)+
  apply (rule vfun_inconsis) apply assumption apply assumption
  apply auto   
  done
*)
    
lemma consis_le: "\<lbrakk> v1 \<sqsubseteq> v1'; v2 \<sqsubseteq> v2'; v1' ~ v2' \<rbrakk> \<Longrightarrow> v1 ~ v2"
  using consis_le_inconsis_le by blast

lemma inconsis_le: "\<lbrakk> v1' \<sqsubseteq> v1; v2' \<sqsubseteq> v2; v1' !~ v2' \<rbrakk> \<Longrightarrow> v1 !~ v2"
  using consis_le_inconsis_le by blast
  
lemma lookup_consis[intro]: "\<lbrakk> consis_env \<rho> \<rho>'; x < length \<rho> \<rbrakk>
  \<Longrightarrow> (\<rho>!x) ~ (\<rho>'!x)"
  apply (induction arbitrary: x rule: consis_env.induct)
   apply force
  apply (case_tac x) apply force apply auto
  done

lemma cons_val_env_inv[elim!]:
  "\<lbrakk> val_env (v#\<rho>); \<lbrakk> is_val v; val_env \<rho> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    unfolding val_env_def by fastforce

lemma ext_val_env[intro!]: "\<lbrakk> is_val v; val_env \<rho> \<rbrakk> \<Longrightarrow> val_env (v#\<rho>)"
  unfolding val_env_def apply auto apply (case_tac k) apply auto done
      
lemma consis_env_join: fixes \<rho>1::"val list" assumes r1_r2: "consis_env \<rho>1 \<rho>2" 
  and v_r1: "val_env \<rho>1" and v_r2: "val_env \<rho>2"
  shows "\<exists> \<rho>3. \<rho>1 \<squnion> \<rho>2 = Some \<rho>3 \<and> val_env \<rho>3"
  using r1_r2 v_r1 v_r2 apply (induction rule: consis_env.induct)
   apply (rule_tac x="[]" in exI) apply force
   apply (erule cons_val_env_inv)
  apply (erule cons_val_env_inv)
   apply (subgoal_tac "\<exists>\<rho>3. \<rho> \<squnion> \<rho>' = Some \<rho>3 \<and> val_env \<rho>3") prefer 2 apply blast
  apply (subgoal_tac "\<exists> v3. v \<squnion> v' = Some v3 \<and> is_val v3")
    prefer 2 using consis_join_val apply blast
  apply (erule exE)+ apply (erule conjE)+
  apply (rule_tac x="v3#\<rho>3" in exI) 
  apply (rule conjI) apply fastforce
  apply blast
  done
    
lemma consis_env_length: "consis_env \<rho> \<rho>' \<Longrightarrow> length \<rho> = length \<rho>'"
  apply (induction rule: consis_env.induct) apply auto done
     
lemma join_env_length: "\<lbrakk> consis_env \<rho>1 \<rho>2; \<rho>1 \<squnion> \<rho>2 = Some \<rho>3  \<rbrakk> \<Longrightarrow> length \<rho>3 = length \<rho>1"
  apply (induction arbitrary: \<rho>3 rule: consis_env.induct)
   apply fastforce
  apply simp
  apply (case_tac "v \<squnion> v'") apply auto
  apply (case_tac "\<rho> \<squnion> \<rho>'") apply auto
  done
    
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

end