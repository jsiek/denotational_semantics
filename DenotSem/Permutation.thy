theory Permutation
  imports Main
begin
section "Permutations"

lemma count_cons[simp]: "count_list (b#ls) a = (if a = b then 1 else 0) + count_list ls a"
  by simp
   
declare count_list.simps(2)[simp del]
  
definition perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "perm \<Gamma> \<Gamma>' \<equiv> (\<forall> x. count_list \<Gamma> x = count_list \<Gamma>' x)"
  
lemma count_append[simp]: "count_list (xs@ys) v = count_list xs v + count_list ys v"
  apply (induction xs) apply auto done
  
lemma count_remove1_same[simp]: "count_list (remove1 v ls) v = (count_list ls v) - 1"
  apply (induction ls) apply auto done

lemma count_remove1_diff[simp]: "v \<noteq> v' \<Longrightarrow> count_list (remove1 v ls) v' = count_list ls v'"
  apply (induction ls) apply auto done

lemma count_remove_mid_same[simp]: "count_list (xs@v#ys) v = 1 + count_list (xs@ys) v"
  apply (induction xs) by auto

lemma count_remove_mid_diff[simp]: "v \<noteq> v' \<Longrightarrow> count_list (xs@v#ys) v' = count_list (xs@ys) v'"
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

lemma nz_count_mem[iff]: "(count_list ls v \<noteq> 0) = (v \<in> set ls)"
  apply (induction ls) apply auto done
   
lemma zero_count_not_mem: "(count_list ls v = 0) \<Longrightarrow> (v \<notin> set ls)"
  apply (induction ls) apply force apply simp
    apply (case_tac "v = a") apply force apply force done

lemma non_mem_zero_count: "v \<notin> set ls \<Longrightarrow> count_list ls v = 0"
  apply (induction ls) apply force apply force done

lemma zero_count_iff_non_mem[iff]: "(count_list ls v = 0) = (v \<notin> set ls)"
  by (meson non_mem_zero_count zero_count_not_mem)  
  
lemma perm_set_eq[intro]: "perm xs ys \<Longrightarrow> set xs = set ys"
  unfolding perm_def
  apply (rule equalityI) apply (rule subsetI)
  apply (subgoal_tac "count_list xs x \<noteq> 0") prefer 2 apply blast apply simp
  apply (rule subsetI) 
  apply (subgoal_tac "count_list ys x \<noteq> 0") prefer 2 apply blast
    apply (subgoal_tac "count_list xs x \<noteq> 0") prefer 2 apply simp
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
  unfolding perm_def
  apply (erule_tac x=v in allE)
  apply simp
  apply (subgoal_tac "v \<in> set \<Gamma>'") prefer 2 
   apply (metis nat.distinct(1) non_mem_zero_count)
  by (meson split_list_first)

lemma perm_empty[simp]: "perm [] xs \<Longrightarrow> xs = []"
  unfolding perm_def by simp
    
lemma perm_singleton[simp]: "perm [v] \<Gamma>' \<Longrightarrow> \<Gamma>' = [v]"   
  unfolding perm_def
  apply (case_tac \<Gamma>')
  apply (metis Nil_is_append_conv list.set_intros(1) remove1_ex_append zero_count_iff_non_mem)
  apply (case_tac "a = v") apply force
  by (metis count_list.simps  list.set_intros(1) zero_count_not_mem)    

lemma perm_map[intro!]: "perm xs ys \<Longrightarrow> perm (map f xs) (map f ys)"
  apply (induction xs arbitrary: f ys)
   apply simp apply (subgoal_tac "ys = []") prefer 2 apply (rule perm_empty) apply blast
   apply (simp add: perm_def)
   apply (subgoal_tac "\<exists>ys1 ys2. ys = ys1@a#ys2 \<and> a \<notin> set ys1") prefer 2 
   apply (meson perm_ex_cons) apply (erule exE)+ apply simp
  apply clarify
  apply (subgoal_tac "perm ([]@xs) (ys1@ys2)") prefer 2 
   apply (rule perm_remove_common1) apply force
  apply (subgoal_tac "perm (map f ([]@xs)) (map f (ys1@ys2))") prefer 2 apply force
  apply simp
  apply (subgoal_tac "perm ([] @ [f a] @ map f xs) (map f ys1 @ [f a]@ map f ys2)") prefer 2
    apply (rule perm_add_common) apply force
  apply force
  done
  
lemma perm_refl[intro!]: "perm L L"
  unfolding perm_def by auto

lemma perm_symm: "perm L1 L2 \<Longrightarrow> perm L2 L1"
  unfolding perm_def by auto
    
lemma perm_trans: "\<lbrakk> perm L1 L2; perm L2 L3 \<rbrakk> \<Longrightarrow> perm L1 L3"
  unfolding perm_def apply auto done
    
lemma perm_append[intro!]: "perm (L1@L2) (L2@L1)"
  unfolding perm_def apply auto done
    
lemma perm_cons_remove[intro!]: "v \<in> set L \<Longrightarrow> perm L (v#(remove1 v L))"    
  unfolding perm_def apply auto by (metis Suc_pred neq0_conv nz_count_mem)

end
