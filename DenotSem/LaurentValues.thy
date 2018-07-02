theory LaurentValues
  imports Main
begin

datatype val = VNat nat | VArrow val val (infix "\<mapsto>" 60) | VUnion val val (infix "\<squnion>" 61) 
  
fun dom :: "val \<Rightarrow> val" where
  "dom (v\<mapsto>v') = v"
fun cod :: "val \<Rightarrow> val" where
  "cod (v\<mapsto>v') = v'"
abbreviation is_fun :: "val \<Rightarrow> bool" where
  "is_fun v \<equiv> (case v of v1\<mapsto>v2 \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation all_funs :: "val list \<Rightarrow> bool" where
  "all_funs \<Gamma> \<equiv> \<forall> v. v \<in> set \<Gamma> \<longrightarrow> is_fun v"

inductive deduce_le :: "val list \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 56) where
  wk_nat[intro!]: "\<lbrakk> \<Gamma>1@\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma>1@(VNat n)#\<Gamma>2 \<turnstile> Suc c: v" | 
  wk_fun[intro!]: "\<lbrakk> \<Gamma>1@\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma>1@(v1\<mapsto>v2)#\<Gamma>2 \<turnstile> Suc c: v" |
  union_R[intro!]: "\<lbrakk> \<Gamma> \<turnstile> c : v1; \<Gamma> \<turnstile> c : v2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Suc c : v1 \<squnion> v2" |
  union_L[intro]: "\<lbrakk> \<Gamma>1@v1#v2#\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma>1@(v1\<squnion>v2)#\<Gamma>2 \<turnstile> Suc c : v" | 
  le_nat[intro!]: "[VNat n] \<turnstile> c : VNat n" |
  le_arrow[intro!]: "\<lbrakk> all_funs \<Gamma>; 
                      \<forall> v v'. v\<mapsto>v' \<in> set \<Gamma> \<longrightarrow> [v1] \<turnstile> c : v;
                      map cod \<Gamma> \<turnstile> c : v2\<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Suc c : v1 \<mapsto> v2"

lemma weaken_size: "\<lbrakk> xs \<turnstile> c : ys; c \<le> c' \<rbrakk> \<Longrightarrow> xs \<turnstile> c' : ys"
  apply (induction xs c ys arbitrary: c' rule: deduce_le.induct) 
  apply (metis Suc_le_D Suc_le_mono wk_nat)  
  apply (metis Suc_le_D Suc_le_mono wk_fun)  
  using Suc_le_D apply force
  apply (metis Suc_le_D Suc_le_mono union_L)
  apply blast
  by (metis (no_types, lifting) Suc_le_D le_arrow less_eq_nat.simps(2) nat.case(2))
    
section "Permutations"
  
fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] a = 0" |
  count_cons: "count (b#ls) a = (if a = b then 1 else 0) + count ls a"

definition perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "perm \<Gamma> \<Gamma>' \<equiv> (\<forall> x. count \<Gamma> x = count \<Gamma>' x)"
  
lemma count_append[simp]: "count (xs@ys) v = count xs v + count ys v"
  apply (induction xs) apply auto done
  
lemma count_remove1_same[simp]: "count (remove1 v ls) v = (count ls v) - 1"
  apply (induction ls) apply auto done

lemma count_remove1_diff[simp]: "v \<noteq> v' \<Longrightarrow> count (remove1 v ls) v' = count ls v'"
  apply (induction ls) apply auto done

lemma count_remove_mid_same[simp]: "count (xs@v#ys) v = 1 + count (xs@ys) v"
  apply (induction xs) by auto

lemma count_remove_mid_diff[simp]: "v \<noteq> v' \<Longrightarrow> count (xs@v#ys) v' = count (xs@ys) v'"
  apply (induction xs) by auto
    
lemma perm_remove1[intro]: "perm (\<Gamma>1@v#\<Gamma>2) \<Gamma> \<Longrightarrow> perm (\<Gamma>1@\<Gamma>2) (remove1 v \<Gamma>)"
  unfolding perm_def 
  by (metis add_diff_cancel_left' count_remove1_diff count_remove1_same 
      count_remove_mid_diff count_remove_mid_same)  
  
lemma remove1_append_notin[simp]: "v \<notin> set ys \<Longrightarrow> remove1 v (ys @ v # zs) = ys @ zs"
    apply (induction ys) apply auto done
  
lemma remove1_ex_append: "v \<in> set xs \<Longrightarrow>
   \<exists> ys zs. xs=ys@v#zs \<and> remove1 v xs = ys@zs \<and> v \<notin> set ys"
  apply (induction xs)
   apply force
  apply (case_tac "v = a")
    apply simp apply (rule_tac x="[]" in exI) apply force
  apply simp
  apply clarify
  apply (rule_tac x="a#ys" in exI)
  apply (rule_tac x="zs" in exI) apply (rule conjI) apply simp
  apply (rule conjI)
    prefer 2 apply force
  apply force
    done    

lemma nz_count_mem[iff]: "(count ls v \<noteq> 0) = (v \<in> set ls)"
  apply (induction ls) apply auto done
   
lemma zero_count_not_mem: "(count ls v = 0) \<Longrightarrow> (v \<notin> set ls)"
  apply (induction ls) apply force apply simp
    apply (case_tac "v = a") apply force apply force done

lemma non_mem_zero_count: "v \<notin> set ls \<Longrightarrow> count ls v = 0"
  apply (induction ls) apply force apply force done

lemma zero_count_iff_non_mem[iff]: "(count ls v = 0) = (v \<notin> set ls)"
  by (meson non_mem_zero_count zero_count_not_mem)  
  
lemma perm_set_eq[intro]: "perm xs ys \<Longrightarrow> set xs = set ys"
  unfolding perm_def
  apply (rule equalityI) apply (rule subsetI)
  apply (subgoal_tac "count xs x \<noteq> 0") prefer 2 apply blast apply simp
  apply (rule subsetI) 
  apply (subgoal_tac "count ys x \<noteq> 0") prefer 2 apply blast
    apply (subgoal_tac "count xs x \<noteq> 0") prefer 2 apply simp
  apply blast
  done
    
lemma perm_remove_common1:
  "perm (\<Gamma>1 @ v# \<Gamma>2) (\<Gamma>1' @ v# \<Gamma>2') \<Longrightarrow> perm (\<Gamma>1 @ \<Gamma>2) (\<Gamma>1' @ \<Gamma>2')"
  unfolding perm_def by auto

lemma perm_add_common:
  "perm (\<Gamma>1@\<Gamma>2) (\<Gamma>1'@\<Gamma>2') \<Longrightarrow> perm (\<Gamma>1@\<Gamma>@\<Gamma>2) (\<Gamma>1'@\<Gamma>@\<Gamma>2')"
  unfolding perm_def by auto

lemma perm_ex_cons:
  "perm (v # \<Gamma>2) \<Gamma>' \<Longrightarrow> \<exists>\<Gamma>1' \<Gamma>2'. \<Gamma>' = \<Gamma>1' @ v # \<Gamma>2' \<and> v \<notin> set \<Gamma>1'" 
  apply (induction \<Gamma>' arbitrary: v \<Gamma>2)
   apply (simp add: perm_def) apply (erule_tac x=v in allE) apply force
  apply (case_tac "a = v") apply (rule_tac x="[]" in exI)
    apply (rule_tac x=\<Gamma>' in exI) apply force
  apply (subgoal_tac "perm (v#(remove1 a \<Gamma>2)) \<Gamma>'")
   apply (subgoal_tac "\<exists>\<Gamma>1' \<Gamma>2'. \<Gamma>' = \<Gamma>1' @ v # \<Gamma>2' \<and> v \<notin> set \<Gamma>1'") prefer 2 apply blast 
   apply (erule exE)+ apply clarify
   apply (rule_tac x="a#\<Gamma>1'" in exI)
    apply (rule_tac x="\<Gamma>2'" in exI)
    apply (rule conjI) apply force apply force
  unfolding perm_def apply (rule allI) apply (erule_tac x=x in allE)
  apply simp apply (case_tac "x=v") apply force 
  apply simp apply (case_tac "x=a") apply auto
  done

lemma perm_ex_append: "perm (\<Gamma>1@ v # \<Gamma>2) \<Gamma>' \<Longrightarrow> \<exists>\<Gamma>1' \<Gamma>2'. \<Gamma>' = \<Gamma>1' @ v # \<Gamma>2' \<and> v \<notin> set \<Gamma>1'"
  apply (induction \<Gamma>1 arbitrary: \<Gamma>2 \<Gamma>')
    using perm_ex_cons apply force
    apply simp
    apply (subgoal_tac "perm (\<Gamma>1 @ v # \<Gamma>2) (remove1 a \<Gamma>')") prefer 2
     apply (simp add: perm_def) apply clarify apply (erule_tac x=x in allE)
     apply (case_tac "x=v") apply simp apply (case_tac "v=a") apply force apply force
      apply simp apply (case_tac "x=a") apply force apply force
      apply (subgoal_tac "\<exists>\<Gamma>1'. (\<exists>\<Gamma>2'. (remove1 a \<Gamma>') = \<Gamma>1' @ v # \<Gamma>2') \<and> v \<notin> set \<Gamma>1'")
      prefer 2 apply blast apply (erule exE) apply (erule conjE) apply (erule exE)
     oops     

section "Admissible Rules"


  
(*  
lemma ex: "\<lbrakk> \<Gamma> \<turnstile> c : v; perm \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> \<exists>c'. \<Gamma>' \<turnstile> c' : v"
  apply (induction arbitrary: \<Gamma>' rule: deduce_le.induct)
  -- "case wk_nat" 
      apply (subgoal_tac "perm (\<Gamma>1@\<Gamma>2) (remove1 (VNat n) \<Gamma>')") prefer 2 
       apply (rule perm_remove1) apply force
    apply (subgoal_tac " \<exists>c'. remove1 (VNat n) \<Gamma>' \<turnstile> c' : v") prefer 2 apply blast
        apply clarify
    apply (subgoal_tac "VNat n \<in> set \<Gamma>'") prefer 2
         apply (subgoal_tac "set (\<Gamma>1 @ VNat n # \<Gamma>2) = set \<Gamma>'") prefer 2 
          apply (rule perm_set_eq) apply assumption apply force
        apply (subgoal_tac "\<exists> ys zs. \<Gamma>'=ys@(VNat n)#zs \<and> remove1 (VNat n) \<Gamma>' = ys@zs \<and> (VNat n) \<notin> set ys")
         prefer 2 apply (rule remove1_ex_append) apply blast
        apply clarify apply (rule_tac x="CWkNat c'" in exI) apply (rule wk_nat) apply blast
        apply force
    -- "case wk_fun"
      apply (subgoal_tac "perm (\<Gamma>1@\<Gamma>2) (remove1 (v1 \<mapsto> v1') \<Gamma>')") prefer 2 
       apply (rule perm_remove1) apply force
    apply (subgoal_tac " \<exists>c'. remove1 (v1 \<mapsto> v1') \<Gamma>' \<turnstile> c' : v") prefer 2 apply blast
        apply clarify
    apply (subgoal_tac "v1 \<mapsto> v1' \<in> set \<Gamma>'") prefer 2
         apply (subgoal_tac "set (\<Gamma>1 @ (v1 \<mapsto> v1') # \<Gamma>2) = set \<Gamma>'") prefer 2 
          apply (rule perm_set_eq) apply assumption apply force
        apply (subgoal_tac "\<exists> ys zs. \<Gamma>'=ys@(v1 \<mapsto> v1')#zs \<and> remove1 (v1 \<mapsto> v1') \<Gamma>' = ys@zs \<and> (v1 \<mapsto> v1') \<notin> set ys")
         prefer 2 apply (rule remove1_ex_append) apply blast
        apply clarify apply (rule_tac x="CWkFun c'" in exI) apply (rule wk_fun) apply blast
        apply force
    -- "case wk_bot"
    apply (subgoal_tac "perm (\<Gamma>1@\<Gamma>2) (remove1 (VBot) \<Gamma>')") prefer 2 
       apply (rule perm_remove1) apply force
    apply (subgoal_tac " \<exists>c'. remove1 (VBot) \<Gamma>' \<turnstile> c' : v") prefer 2 apply blast
        apply clarify
    apply (subgoal_tac "VBot \<in> set \<Gamma>'") prefer 2
         apply (subgoal_tac "set (\<Gamma>1 @ (VBot) # \<Gamma>2) = set \<Gamma>'") prefer 2 
          apply (rule perm_set_eq) apply assumption apply force
        apply (subgoal_tac "\<exists> ys zs. \<Gamma>'=ys@(VBot)#zs \<and> remove1 (VBot) \<Gamma>' = ys@zs \<and> (VBot) \<notin> set ys")
         prefer 2 apply (rule remove1_ex_append) apply blast
        apply clarify apply (rule_tac x="CWkBot c'" in exI) apply (rule wk_bot) apply blast
        apply force
    -- "case union_R"
    apply force
    -- "case union_L"
    apply clarify 
    apply (subgoal_tac "\<exists>\<Gamma>1' \<Gamma>2'. \<Gamma>'=\<Gamma>1'@(v1\<squnion>v2)#\<Gamma>2'") apply (erule exE)+
     apply (subgoal_tac "perm (\<Gamma>1 @ v1 # v2 # \<Gamma>2) (\<Gamma>1'@v1#v2#\<Gamma>2')") 
    apply (subgoal_tac "\<exists>c'. \<Gamma>1'@v1#v2#\<Gamma>2' \<turnstile> c' : v") prefer 2 apply blast
    apply (erule exE) apply (rule_tac x="CUnionL c'" in exI) apply (rule union_L)
       apply assumption apply assumption apply simp 
     apply (subgoal_tac "perm (\<Gamma>1 @  \<Gamma>2) (\<Gamma>1' @ \<Gamma>2')") prefer 2 apply (rule perm_remove_common1)
      apply blast
    apply (subgoal_tac "perm (\<Gamma>1 @ [v1, v2] @ \<Gamma>2) (\<Gamma>1' @ [v1, v2] @ \<Gamma>2')") prefer 2
    apply (rule perm_add_common) apply blast apply simp
        
    -- "case le_nat"
    defer
    -- "case le_arrow"
    
    oops
    
lemma wk_gen: "\<forall> c v v' \<Gamma> \<Delta>. n = size c \<longrightarrow> \<Gamma>@\<Delta> \<turnstile> c : v \<longrightarrow> (\<exists>c'. \<Gamma>@v'#\<Delta> \<turnstile> c' : v)"
  apply (induction n rule: nat_less_induct)
  apply clarify
  apply (case_tac c)
  oops
    
lemma weaken: "\<lbrakk> \<Gamma> \<turnstile> c : v; fset \<Gamma> \<subseteq> fset \<Gamma>' \<rbrakk> \<Longrightarrow> \<exists>c'. \<Gamma>' \<turnstile> c' : v"
 oops
 *) 
  
    
    
end