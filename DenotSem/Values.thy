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
  
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> [(v1,v1')] \<sqsubseteq> [(v2,v2')]" 
(* the following rule makes things much more complicated -Jeremy
  le_distr: "v \<mapsto> (v1 \<squnion> v2) \<sqsubseteq> (v\<mapsto>v1) \<squnion> (v \<mapsto>v2)" (* arrow intersect *)
*)
 
inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_fun_fun_inv[elim!]: "VFun f1 \<sqsubseteq> VFun f2" and
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
  apply (case_tac v1) apply (case_tac v2) apply (case_tac v12) apply simp
     apply (case_tac "x1=x1a") apply force apply force
    apply simp apply (case_tac "x1=x1a") apply force apply force
   apply (case_tac v12) apply force apply force
  apply (case_tac v2) apply (case_tac v12) apply force apply force
  apply (case_tac v12) apply force
  apply (case_tac v3) apply force apply simp
  by (metis Un_iff le_fun le_fun_fun_inv le_fun_sub_subset_aux le_fun_subset_sub set_append)
    
lemma le_fun_trans_aux:
   fixes f1::func and f2::func and f3::func
   assumes IH: "\<forall>m < vsize (VFun f1) + vsize (VFun f2) + vsize (VFun f3).
          (\<forall>v1 v2 v3. m = vsize v1 + vsize v2 + vsize v3 
          \<longrightarrow> v1 \<sqsubseteq> v2 \<longrightarrow> v2 \<sqsubseteq> v3 \<longrightarrow> v1 \<sqsubseteq> v3)"
    and f1_f2: "f1 \<sqsubseteq> f2" and f2_f3: "f2 \<sqsubseteq> f3"
  shows "f1 \<sqsubseteq> f3"
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

lemma member_join_fun: "True" ..
    
inductive consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 52) and
    inconsistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "!~" 52) where
  vnat_consis[intro!]: "(VNat n) ~ (VNat n)" |
  vfun_consis[intro!]: "\<lbrakk> \<forall> v1 v1' v2 v2'. v1\<mapsto>v1' \<sqsubseteq> VFun f1 \<and> v2\<mapsto>v2' \<sqsubseteq> VFun f2 \<longrightarrow>
                        (v1 ~ v2 \<and> v1' ~ v2') \<or> v1 !~ v2 \<rbrakk> \<Longrightarrow> (VFun f1) ~ (VFun f2)" |
  vnat_inconsis[intro!]: "n \<noteq> n' \<Longrightarrow> (VNat n) !~ (VNat n')" |
  vfun_inconsis[intro!]: "\<lbrakk> v1 \<mapsto> v1' \<sqsubseteq> VFun f1; v2 \<mapsto> v2' \<sqsubseteq> VFun f2; v1 ~ v2; v1' !~ v2' \<rbrakk> 
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

fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> (val list) option" (infix "\<squnion>" 56) where
  "env_join [] [] = Some []" |
  "env_join (v#\<rho>) (v'#\<rho>') = 
      (case v \<squnion> v' of
         None \<Rightarrow> None
      | Some v'' \<Rightarrow> 
           (case \<rho>\<squnion>\<rho>' of
             None \<Rightarrow> None
           | Some \<rho>'' \<Rightarrow> Some (v''#\<rho>'')))" 
 
definition env_le :: "val list \<Rightarrow> val list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "(\<rho>::val list) \<sqsubseteq> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k \<sqsubseteq> \<rho>'!k)" 
    
lemma inconsis_not_consis[simp]: "(v1 !~ v2) = (\<not> (v1 ~ v2))"
  sorry

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

theorem beta_sound: fixes A1::val and A2::val and B1::val and B2::val 
  assumes cd_ab: "C\<mapsto>D \<sqsubseteq> AB" and ab: "(A1\<mapsto>B1)\<squnion>(A2\<mapsto>B2) = Some AB"
  shows "(A1 \<sqsubseteq> C \<or> A2 \<sqsubseteq> C \<or> (\<exists>A3. A3 \<sqsubseteq> C \<and> A1 \<squnion> A2 = Some A3))
       \<and> (D \<sqsubseteq> B1 \<or> D \<sqsubseteq> B2 \<or> (\<exists>B3. D \<sqsubseteq> B3 \<and> B1 \<squnion> B2 = Some B3))"
  using cd_ab ab sorry
    
(*

lemma consis_val_join_val_aux:
  "(v1 ~ v2 \<longrightarrow> is_val v1 \<longrightarrow> is_val v2 \<longrightarrow> is_val (v1 \<squnion> v2))
      \<and> (v1 !~ v2 \<longrightarrow> True)"
  apply (induction rule: consistent_inconsistent.induct)
  apply force
  defer
      apply force
     apply force
  apply force
   apply force
  apply (rule impI)+
proof -
  fix f1 f2 assume IH: "\<forall>v1 v1' v2 v2'. v1 \<mapsto> v1' \<sqsubseteq> VFun f1 \<and> v2 \<mapsto> v2' \<sqsubseteq> VFun f2 \<longrightarrow>
          (v1 ~ v2 \<and> (is_val v1 \<longrightarrow> is_val v2 \<longrightarrow> is_val (v1 \<squnion> v2))) \<and>
          v1' ~ v2' \<and> (is_val v1' \<longrightarrow> is_val v2' \<longrightarrow> is_val (v1' \<squnion> v2')) \<or>
          v1 !~ v2 \<and> True" and
    vf1: "is_val (VFun f1)" and vf2: "is_val (VFun f2)"
  let ?v3 = "VFun (f1@f2)"
  have "is_val ?v3"
  proof (rule vfun_is_val) 
    show "is_fun (f1@f2)" 
      apply (simp only: is_fun_def) apply (rule vfun_consis)
    proof clarify
      fix v1 v1' v2 v2'
      assume v11_f12: "v1 \<mapsto> v1' \<sqsubseteq> VFun (f1 @ f2)" and v22_f12: "v2 \<mapsto> v2' \<sqsubseteq> VFun (f1 @ f2)" 
        and nc_v12: "\<not> v1 !~ v2"
      have v1_v2: "v1 ~ v2" using nc_v12 by simp
      
          
      have v1p_v2p: "v1' ~ v2'" sorry
      show "v1 ~ v2 \<and> v1' ~ v2'" using v1_v2 v1p_v2p by blast
    qed
  next
    show "\<forall>v v'. (v, v') \<in> set (f1 @ f2) \<longrightarrow> is_val v \<and> is_val v'" using vf1 vf2 by auto        
  qed    
  then show "is_val (VFun f1 \<squnion> VFun f2)" by simp
qed
*)    
  
end