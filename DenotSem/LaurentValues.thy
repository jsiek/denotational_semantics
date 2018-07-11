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
  le_arrow[intro!]: "\<lbrakk> all_funs \<Gamma>; \<forall> v v'. v\<mapsto>v' \<in> set \<Gamma> \<longrightarrow> [v1] \<turnstile> c : v;
                      map cod \<Gamma> \<turnstile> c : v2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Suc c : v1 \<mapsto> v2"

lemma weaken_size: "\<lbrakk> xs \<turnstile> c : ys; c \<le> c' \<rbrakk> \<Longrightarrow> xs \<turnstile> c' : ys"
  apply (induction xs c ys arbitrary: c' rule: deduce_le.induct) 
  apply (metis Suc_le_D Suc_le_mono wk_nat)  
  apply (metis Suc_le_D Suc_le_mono wk_fun)  
  using Suc_le_D apply force
  apply (metis Suc_le_D Suc_le_mono union_L)
  apply blast
  by (metis (no_types, lifting) Suc_le_D le_arrow less_eq_nat.simps(2) nat.case(2))
    
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

section "Admissible Rules"

lemma wk_gen: "\<Gamma>@\<Delta> \<turnstile> c : v' \<Longrightarrow> (\<exists>c'. \<Gamma>@v#\<Delta> \<turnstile> c' : v')"
proof (induction v arbitrary: \<Gamma> \<Delta> c v')
  case (VNat n)
  then show ?case using wk_nat by blast
next
  case (VArrow v1 v2)
  then show ?case using wk_fun by blast
next
  case (VUnion v1 v2)
  obtain c2 where "\<Gamma>@v2#\<Delta> \<turnstile> c2 : v'" using VUnion.IH(2) VUnion.prems by blast
  then obtain c1 where "\<Gamma>@v1#v2#\<Delta> \<turnstile> c1 : v'" using VUnion.IH(1) by blast 
  then show ?case using union_L by blast
qed
  
lemma weaken: "\<Gamma>@\<Delta> \<turnstile> c : v' \<Longrightarrow> (\<exists>c'. \<Gamma>@\<Sigma>@\<Delta> \<turnstile> c' : v')"
  apply (induction \<Sigma> arbitrary: \<Gamma> \<Delta>)
   apply force
  apply (subgoal_tac "\<exists>c'. \<Gamma> @ \<Sigma> @ \<Delta> \<turnstile> c' : v'") prefer 2 apply blast apply (erule exE)
  apply (subgoal_tac "\<exists>c'. \<Gamma> @ a # (\<Sigma> @ \<Delta>) \<turnstile> c' : v' ") prefer 2 using wk_gen apply blast
  apply simp
  done

lemma ax: "\<exists>c. [v] \<turnstile> c : v"
proof (induction v)
  case (VNat n)
  then show ?case by blast
next
  case (VArrow v1 v2)
  obtain c1 where c1: "[v1] \<turnstile> c1 : v1" using VArrow.IH(1) by blast
  obtain c2 where c2: "[v2] \<turnstile> c2 : v2" using VArrow.IH(2) by blast
  have c1_2: "[v1] \<turnstile> max c1 c2 : v1" using weaken_size c1 by auto
  have c2_2: "[v2] \<turnstile> max c1 c2 : v2" using weaken_size c2 by auto
  show ?case using le_arrow[of "[(v1\<mapsto>v2)]" v1 "max c1 c2" v2] c1_2 c2_2
     apply (rule_tac x="Suc (max c1 c2)" in exI) apply simp done
next
  case (VUnion v1 v2)
  obtain c1 where c1: "[v1] \<turnstile> c1 : v1" using VUnion.IH(1) by blast
  obtain c2 where c2: "[v2] \<turnstile> c2 : v2" using VUnion.IH(2) by blast
  obtain c1' where c1p: "[v1,v2] \<turnstile> c1' : v1"
    using c1 wk_gen[of "[v1]" "[]" c1 v1 v2] by auto
  obtain c2' where c2p: "[v1,v2] \<turnstile> c2' : v2"
    using c2 wk_gen[of "[]" "[v2]" c2 v2 v1] by auto
  have "[v1,v2] \<turnstile> Suc (max c1' c2') : v1 \<squnion> v2"
    using weaken_size union_R c1p c2p by auto
  then show ?case using union_L[of "[]" v1 v2 "[]"] by auto
qed
  
lemma ex: "\<lbrakk> \<Gamma> \<turnstile> c : v; perm \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> c : v"
proof (induction \<Gamma> c v arbitrary: \<Gamma>' rule: deduce_le.induct)
  case (wk_nat \<Gamma>1 \<Gamma>2 c v n)
  from wk_nat(3) obtain \<Gamma>1' \<Gamma>2' where gp: "\<Gamma>' = \<Gamma>1'@(VNat n)#\<Gamma>2'"
    using perm_ex_append[of \<Gamma>1] by blast
  have "perm (\<Gamma>1@\<Gamma>2) (\<Gamma>1'@\<Gamma>2')" using gp perm_remove_common1 wk_nat.prems by fastforce
  then have cp: "\<Gamma>1'@\<Gamma>2' \<turnstile> c : v" using wk_nat.IH by blast
  then show ?case using gp by blast
next
  case (wk_fun \<Gamma>1 \<Gamma>2 c v v1 v2)
  from wk_fun(3) obtain \<Gamma>1' \<Gamma>2' where gp: "\<Gamma>' = \<Gamma>1'@(v1 \<mapsto> v2)#\<Gamma>2'"
    using perm_ex_append[of \<Gamma>1] by blast
  have "perm (\<Gamma>1@\<Gamma>2) (\<Gamma>1'@\<Gamma>2')" using gp perm_remove_common1 wk_fun.prems by fastforce
  then have cp: "\<Gamma>1'@\<Gamma>2' \<turnstile> c : v" using wk_fun.IH by blast
  then show ?case using gp by blast
next
  case (union_R \<Gamma> c v1 v2)
  have c1: "\<Gamma>' \<turnstile> c : v1" using union_R.IH(1) union_R.prems by blast
  have c2: "\<Gamma>' \<turnstile> c : v2" using union_R.IH(2) union_R.prems by blast
  then show ?case using c1 c2 by (simp add: deduce_le.union_R weaken_size)
next
  case (union_L \<Gamma>1 v1 v2 \<Gamma>2 c v)
  from union_L.prems obtain \<Gamma>1' \<Gamma>2' where gp: "\<Gamma>' = \<Gamma>1'@(v1 \<squnion> v2)#\<Gamma>2'"
    using perm_ex_append[of \<Gamma>1] by blast
  have "perm (\<Gamma>1@\<Gamma>2) (\<Gamma>1'@\<Gamma>2')" using gp perm_remove_common1 using union_L.prems by fastforce
  then have "perm (\<Gamma>1 @ [v1, v2] @ \<Gamma>2) (\<Gamma>1' @ [v1, v2] @ \<Gamma>2')" using perm_add_common by blast
  then have "perm (\<Gamma>1 @ v1 # v2 # \<Gamma>2) (\<Gamma>1' @ v1 # v2 # \<Gamma>2')" by simp    
  with union_L.IH[of "\<Gamma>1' @ v1 # v2 # \<Gamma>2'"] have
    cp: "\<Gamma>1' @ v1 # v2 # \<Gamma>2' \<turnstile> c : v" by blast
  then show ?case using gp by blast
next
  case (le_nat n c)
  then have gp: "\<Gamma>' = [VNat n]" by simp
  then show ?case by auto
next
  case (le_arrow \<Gamma> v1 c v2)
  have af_gp: "all_funs \<Gamma>'" using le_arrow(1) le_arrow(5) using perm_set_eq by blast
  have "perm (map cod \<Gamma>) (map cod \<Gamma>')" using le_arrow.prems by blast
  then have c2: "map cod \<Gamma>' \<turnstile> c : v2" using le_arrow.IH(2) by blast
  have c1: "\<forall> v v'. v\<mapsto>v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> c : v"
  proof clarify
    fix v v' assume vv_gp: "v\<mapsto>v' \<in> set \<Gamma>'"
    then have "v\<mapsto>v' \<in> set \<Gamma>" using le_arrow.prems perm_set_eq by blast
    then show "[v1] \<turnstile> c : v" using le_arrow.IH(1) by blast
  qed
  have c2_2: "map cod \<Gamma>' \<turnstile> c : v2" using c2 weaken_size by auto
  have c1_2: "\<forall>v v'. v\<mapsto>v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> c : v" using c1 weaken_size by auto    
  show ?case using af_gp c1_2 c2_2 by blast
qed
  
lemma append_eq_aux: "v \<noteq> v' \<Longrightarrow> v#ys = xs'@v'#ys' \<Longrightarrow> (\<exists>ls. xs'=v#ls \<and> ys=ls@v'#ys') 
                                           \<or> (\<exists>ls. ys'=ls@v#ys)"
  apply (induction xs' arbitrary: v v' ys ys')
  apply force
  apply auto
  done
  
lemma append_eq: "v \<noteq> v' \<Longrightarrow> xs@v#ys = xs'@v'#ys' \<Longrightarrow> (\<exists>ls. xs'=xs@v#ls \<and> ys=ls@v'#ys') 
                                           \<or> (\<exists>ls. xs=xs'@v'#ls \<and> ys'=ls@v#ys)"
  apply (induction xs arbitrary: v ys xs' v' ys')
  apply simp using append_eq_aux apply fastforce
  apply simp
  apply (case_tac xs') apply force apply simp
  done

lemma append_eq_elim: "\<lbrakk> xs@v#ys = xs'@v'#ys'; v \<noteq> v';
             \<And>ls. \<lbrakk> xs'=xs@v#ls; ys=ls@v'#ys' \<rbrakk> \<Longrightarrow> P; 
             \<And>ls. \<lbrakk> xs=xs'@v'#ls; ys'=ls@v#ys \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using append_eq apply metis done
    
lemma append_eq2_aux: "v#ys = xs'@v#ys' \<Longrightarrow>
   (\<exists>ls. xs'=v#ls \<and> ys=ls@v#ys') \<or> (\<exists>ls. ys'=ls@v#ys) \<or> ys = ys'"  
  apply (induction xs' arbitrary: v ys ys')
   apply force
  apply force
  done
  
lemma append_eq2: "xs@v#ys = xs'@v#ys' \<Longrightarrow>
     (\<exists>ls. xs'=xs@v#ls \<and> ys=ls@v#ys') 
       \<or> (\<exists>ls. xs=xs'@v#ls \<and> ys'=ls@v#ys)
       \<or> (xs = xs' \<and> ys = ys')"
  apply (induction xs arbitrary: v ys xs' ys')    
   apply simp using append_eq2_aux apply force
     apply (case_tac xs') apply force apply simp
  done
    
lemma union_Le_aux: "\<lbrakk> \<Gamma>' \<turnstile> k : C; \<Gamma>' = \<Gamma>@(A\<squnion>B)#\<Delta> \<rbrakk> \<Longrightarrow> \<exists>k'. \<Gamma>@A#B#\<Delta> \<turnstile> k' : C \<and> k' < k"
proof (induction \<Gamma>' k C arbitrary: \<Gamma> A B \<Delta> rule: deduce_le.induct)
  case (wk_nat \<Gamma>1 \<Gamma>2 c v n)
  let ?vp = "VNat n"
  have "(\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>) 
        \<or> (\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2)"
    using wk_nat.prems by (simp add: append_eq)
  then show ?case
  proof
    assume "\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>"
    then obtain \<Delta>' where g: "\<Gamma>=\<Gamma>1@?vp#\<Delta>'" and g2: "\<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>" by blast
    have "\<Gamma>1 @ \<Gamma>2 = \<Gamma>1 @ \<Delta>' @ (A \<squnion> B) # \<Delta>" using g g2 by simp
    with wk_nat.IH[of "\<Gamma>1 @ \<Delta>'" A B \<Delta>] obtain k' where 
      kp: "(\<Gamma>1 @ \<Delta>') @ A # B # \<Delta> \<turnstile> k' : v" and kp_c: "k' < c" by auto
    then have "\<Gamma>@A#B#\<Delta> \<turnstile> Suc k' : v" using g by auto
    then show ?thesis using kp_c by auto
  next
    assume "\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2"
    then obtain \<Delta>' where g1: "\<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>'" and d: "\<Delta>=\<Delta>'@?vp#\<Gamma>2" by blast
    have "\<Gamma>1@\<Gamma>2 = \<Gamma> @ (A \<squnion> B) # (\<Delta>' @ \<Gamma>2)" using g1 d by simp
    with wk_nat.IH[of \<Gamma> A B "\<Delta>'@\<Gamma>2"] obtain k' where
      kp: "\<Gamma>@A#B#(\<Delta>'@\<Gamma>2) \<turnstile> k' : v" and kp_c: "k' < c" by auto
    then have "(\<Gamma>@A#B#\<Delta>')@\<Gamma>2 \<turnstile> k' : v" by simp
    then have "(\<Gamma>@A#B#\<Delta>')@?vp#\<Gamma>2 \<turnstile> Suc k' : v" by blast
    then have "\<Gamma> @ A # B # \<Delta> \<turnstile> Suc k' : v" using d by simp  
    then show ?thesis using kp_c by auto 
  qed
next
  case (wk_fun \<Gamma>1 \<Gamma>2 c v v1 v2)
  let ?vp = "v1\<mapsto>v2"
  have "(\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>) 
        \<or> (\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2)"
    using wk_fun.prems by (simp add: append_eq)
  then show ?case
  proof
    assume "\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>"
    then obtain \<Delta>' where g: "\<Gamma>=\<Gamma>1@?vp#\<Delta>'" and g2: "\<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>" by blast
    have "\<Gamma>1 @ \<Gamma>2 = \<Gamma>1 @ \<Delta>' @ (A \<squnion> B) # \<Delta>" using g g2 by simp
    with wk_fun.IH[of "\<Gamma>1 @ \<Delta>'" A B \<Delta>] obtain k' where 
      kp: "(\<Gamma>1 @ \<Delta>') @ A # B # \<Delta> \<turnstile> k' : v" and kp_c: "k' < c" by auto
    then have "\<Gamma>@A#B#\<Delta> \<turnstile> Suc k' : v" using g by auto
    then show ?thesis using kp_c by auto
  next
    assume "\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2"
    then obtain \<Delta>' where g1: "\<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>'" and d: "\<Delta>=\<Delta>'@?vp#\<Gamma>2" by blast
    have "\<Gamma>1@\<Gamma>2 = \<Gamma> @ (A \<squnion> B) # (\<Delta>' @ \<Gamma>2)" using g1 d by simp
    with wk_fun.IH[of \<Gamma> A B "\<Delta>'@\<Gamma>2"] obtain k' where
      kp: "\<Gamma>@A#B#(\<Delta>'@\<Gamma>2) \<turnstile> k' : v" and kp_c: "k' < c" by auto
    then have "(\<Gamma>@A#B#\<Delta>')@\<Gamma>2 \<turnstile> k' : v" by simp
    then have "(\<Gamma>@A#B#\<Delta>')@?vp#\<Gamma>2 \<turnstile> Suc k' : v" by blast
    then have "\<Gamma> @ A # B # \<Delta> \<turnstile> Suc k' : v" using d by simp  
    then show ?thesis using kp_c by auto 
  qed
next
  case (union_R \<Gamma> c v1 v2 \<Gamma>')
  obtain k1 where k1: "\<Gamma>' @ A # B # \<Delta> \<turnstile> k1 : v1" and k1_c: "k1 < c" 
    using union_R.IH(1) union_R.prems by blast
  obtain k2 where k2: "\<Gamma>' @ A # B # \<Delta> \<turnstile> k2 : v2" and k2_c: "k2 < c" 
    using union_R.IH(2) union_R.prems by blast
  show ?case using k1 k1_c k2 k2_c weaken_size by (rule_tac x="Suc (max k1 k2)" in exI) auto
next
  case (union_L \<Gamma>1 v1 v2 \<Gamma>2 c v)
  let ?vp = "v1\<squnion>v2"
  show ?case
  proof (cases "v1\<squnion>v2 = A\<squnion>B")
    case True
    then have "(\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>) 
        \<or> (\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2)
        \<or> (\<Gamma>1=\<Gamma> \<and> \<Gamma>2=\<Delta>)" using append_eq2[of \<Gamma>1 "?vp" \<Gamma>2 \<Gamma> \<Delta>] union_L.prems by blast
    moreover {
      assume "\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>"
      then obtain \<Delta>' where g: "\<Gamma>=\<Gamma>1@?vp#\<Delta>'" and g2: "\<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>" by blast
      have "\<Gamma>1 @ v1 # v2 # \<Gamma>2 = (\<Gamma>1 @ v1 # v2 # \<Delta>') @ (A \<squnion> B) # \<Delta>"
        using g g2 union_L.prems by simp
      with union_L.IH[of "\<Gamma>1 @ v1 # v2 # \<Delta>'" A B \<Delta>]
      obtain k' where kp: "(\<Gamma>1 @ v1 # v2 # \<Delta>') @ A # B # \<Delta> \<turnstile> k' : v" and kp_c: "k' < c" by blast
      then have ?thesis 
        using \<open>\<exists>\<Delta>''. \<Gamma> = \<Gamma>1 @ (v1 \<squnion> v2) # \<Delta>'' \<and> \<Gamma>2 = \<Delta>'' @ (A \<squnion> B) # \<Delta>\<close> g2 by auto
    }
    moreover {
      assume "\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2"
      then obtain \<Delta>' where g1: "\<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>'" and d: "\<Delta>=\<Delta>'@?vp#\<Gamma>2" by blast
      have "\<Gamma>1 @ v1 # v2 # \<Gamma>2 = \<Gamma> @ (A \<squnion> B) # (\<Delta>' @ v1 # v2 # \<Gamma>2)" using g1 d union_L.prems by simp
      with union_L.IH[of \<Gamma> A B "\<Delta>' @ v1 # v2 # \<Gamma>2"]
      obtain k' where kp: "(\<Gamma> @ A # B # \<Delta>') @ v1 # v2 # \<Gamma>2 \<turnstile> k' : v" and kp_c: "k' < c" by auto
      then have "(\<Gamma> @ A # B # \<Delta>') @ ?vp # \<Gamma>2 \<turnstile> Suc k' : v" by blast
      then have ?thesis using d kp_c by auto  }
    moreover {
      assume "\<Gamma>1=\<Gamma> \<and> \<Gamma>2=\<Delta>"
      then have ?thesis using True union_L.hyps by blast
    } ultimately show ?thesis by blast      
  next
    case False
    then have "(\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>) 
        \<or> (\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2)"
      using union_L.prems(1) append_eq[of "v1\<squnion>v2" "A\<squnion>B" \<Gamma>1 \<Gamma>2 \<Gamma> \<Delta>] by blast
    then show ?thesis
    proof
      assume "\<exists> \<Delta>'. \<Gamma>=\<Gamma>1@?vp#\<Delta>' \<and> \<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>"
      then obtain \<Delta>' where g: "\<Gamma>=\<Gamma>1@?vp#\<Delta>'" and g2: "\<Gamma>2=\<Delta>'@(A\<squnion>B)#\<Delta>" by blast
      have "\<Gamma>1 @ v1 # v2 # \<Gamma>2 =  (\<Gamma>1 @ v1 # v2 # \<Delta>') @ (A \<squnion> B) # \<Delta>" using g g2 by simp
      with union_L.IH[of "\<Gamma>1 @ v1 # v2 # \<Delta>'" A B \<Delta>] obtain k' where 
        kp: "(\<Gamma>1 @ v1 # v2 # \<Delta>') @ A # B # \<Delta> \<turnstile> k' : v" and kp_c: "k' < c" by auto
      then have "\<Gamma>@A#B#\<Delta> \<turnstile> Suc k' : v" using g by auto
      then show ?thesis using kp_c by auto
    next
      assume "\<exists> \<Delta>'. \<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>' \<and> \<Delta>=\<Delta>'@?vp#\<Gamma>2"
      then obtain \<Delta>' where g1: "\<Gamma>1=\<Gamma>@(A\<squnion>B)#\<Delta>'" and d: "\<Delta>=\<Delta>'@?vp#\<Gamma>2" by blast
      have "\<Gamma>1 @ v1 # v2 # \<Gamma>2 = \<Gamma> @ (A \<squnion> B) # \<Delta>' @ v1 # v2 # \<Gamma>2" using g1 d by simp 
      with union_L.IH[of \<Gamma> A B "\<Delta>' @ v1 # v2 # \<Gamma>2"] obtain k' where
        kp: "(\<Gamma> @ A # B # \<Delta>') @ v1 # v2 # \<Gamma>2 \<turnstile> k' : v" and kp_c: "k' < c" by auto
      then have "(\<Gamma> @ A # B # \<Delta>') @ ?vp # \<Gamma>2 \<turnstile> Suc k' : v" by blast 
      then show ?thesis using kp_c d by auto
    qed
  qed
next
  case (le_nat n c)
  then have "False"
    by (metis append_eq_Cons_conv append_is_Nil_conv list.inject list.simps(3) val.simps(7))
  then show ?case ..
next
  case (le_arrow \<Gamma>' v1 c v2)
  have "False" using le_arrow(1) le_arrow(5) apply simp apply (erule_tac x="A\<squnion>B" in allE) by blast      
  then show ?case ..
qed
 
lemma union_Le: "\<lbrakk> \<Gamma>@(A\<squnion>B)#\<Delta> \<turnstile> k : C  \<rbrakk> \<Longrightarrow> \<exists>k'. \<Gamma>@A#B#\<Delta> \<turnstile> k' : C \<and> k' < k"
  using union_Le_aux by blast

lemma append_eq3_aux: "v # ys = xs' @ v' # ys' \<Longrightarrow>
       (\<exists>ls. xs' = v # ls \<and> ys = ls @ v' # ys') \<or>
       xs' = [] \<and> v = v' \<and> ys = ys'"
  apply (induction xs' arbitrary: v ys v' ys')
  apply force
  apply auto
  done

lemma cons_append_eq3_elim: "\<lbrakk> v # ys = xs' @ v' # ys';
       \<And>ls. \<lbrakk>xs' = v # ls; ys = ls @ v' # ys' \<rbrakk> \<Longrightarrow> P; 
       \<lbrakk> xs' = []; v = v'; ys = ys' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using append_eq3_aux[of v ys xs' v' ys'] by blast

lemma append_eq3: "xs@v#ys = xs'@v'#ys' \<Longrightarrow>
     (\<exists>ls. xs'=xs@v#ls \<and> ys=ls@v'#ys') 
       \<or> (\<exists>ls. xs=xs'@v'#ls \<and> ys'=ls@v#ys)
       \<or> (xs = xs' \<and> v = v' \<and> ys = ys')"
  apply (induction xs arbitrary: v v' ys xs' ys')    
   apply simp using append_eq3_aux 
  apply (metis Cons_eq_append_conv)
     apply (case_tac xs') apply force apply simp
  done

lemma append_eq3_elim: "\<lbrakk> xs@v#ys = xs'@v'#ys'; 
     \<And>ls. \<lbrakk> xs'=xs@v#ls; ys=ls@v'#ys' \<rbrakk> \<Longrightarrow> P; 
     \<And>ls. \<lbrakk>xs=xs'@v'#ls; ys'=ls@v#ys \<rbrakk> \<Longrightarrow> P;
           \<lbrakk>xs = xs'; v = v'; ys = ys' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using append_eq3 by (metis (full_types))
    

lemma co: "\<forall> \<Delta> A \<Sigma> c C. m = (size A, c) \<longrightarrow>
            \<Delta> @ A # A # \<Sigma> \<turnstile> c : C \<longrightarrow> (\<exists>c'. \<Delta> @ A # \<Sigma> \<turnstile> c' : C)"
proof (induction m rule: wf_induct[of "less_than <*lex*> less_than"])
  case 1
  then show ?case by auto
next
  case (2 m)
  then show ?case
  proof clarify
    fix \<Delta> and A::val and \<Sigma> c C assume m: "m = (size A, c)" and
        c: "\<Delta> @ A # A # \<Sigma> \<turnstile> c : C"
    from c show "\<exists>c'. \<Delta> @ A # \<Sigma> \<turnstile> c' : C "
    proof (* case wk_nat *)
      fix \<Gamma>1 \<Gamma>2 ca v n
      let ?v = "VNat n"
      assume eq: "\<Delta> @ A # A # \<Sigma> = \<Gamma>1 @ ?v # \<Gamma>2" and c_ca: "c = Suc ca" and c_v: "C = v"
        and ca: "\<Gamma>1 @ \<Gamma>2 \<turnstile> ca : v"
      have p1: "perm (\<Delta> @ A # A # \<Sigma>) (\<Gamma>1 @ ?v # \<Gamma>2)" using eq by auto        
      from eq show ?thesis
      proof (rule append_eq3_elim)
        fix \<Delta>' assume g1: "\<Gamma>1 = \<Delta> @ A # \<Delta>'" and eq2: "A # \<Sigma> = \<Delta>' @ ?v # \<Gamma>2"
        from eq2 show ?thesis
        proof (rule cons_append_eq3_elim)
          fix \<Delta>'' assume dp: "\<Delta>' = A # \<Delta>''" and s: "\<Sigma> = \<Delta>'' @ ?v # \<Gamma>2"
          have "\<Delta>@A#A#\<Delta>''@\<Gamma>2 \<turnstile> ca : C" using ca c_v dp s g1 by simp
          then obtain cb where "\<Delta>@A#\<Delta>''@\<Gamma>2 \<turnstile> cb : C" using 2 m c_ca 
              apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force by blast
          then have "(\<Delta>@A#\<Delta>'')@\<Gamma>2 \<turnstile> cb : C" by simp
          then have "(\<Delta>@A#\<Delta>'')@ ?v # \<Gamma>2 \<turnstile> Suc cb : C" by blast
          then show ?thesis using dp eq2 by auto
        next
          assume dp: "\<Delta>' = []" and a: "A = ?v" and s: "\<Sigma> = \<Gamma>2" 
          from ca dp s g1 c_v have "\<Delta> @ A # \<Sigma> \<turnstile> ca : C" by simp
          then show ?thesis by blast
        qed
      next
        fix \<Delta>' assume d: "\<Delta> = \<Gamma>1 @ ?v # \<Delta>'" and g2: "\<Gamma>2 = \<Delta>' @ A # A # \<Sigma>"
        have "(\<Gamma>1 @ \<Delta>') @ A # A # \<Sigma> \<turnstile> ca : C" using ca c_v d g2 by simp
        then obtain cb where "(\<Gamma>1 @ \<Delta>') @ A # \<Sigma> \<turnstile> cb : C" using 2 m c_ca
          apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force by blast
        then have "\<Gamma>1 @ (\<Delta>' @ A # \<Sigma>) \<turnstile> cb : C" by simp
        then have "\<Gamma>1 @ ?v # (\<Delta>' @ A # \<Sigma>) \<turnstile> Suc cb : C" by blast
        then show ?thesis using d by auto
      next
        assume d: "\<Delta> = \<Gamma>1" and a: "A = ?v" and eq2: "A # \<Sigma> = \<Gamma>2"
        then show ?thesis using ca c_v by blast
      qed
        
    next (* case wk_fun *)
      fix \<Gamma>1 \<Gamma>2 ca v v1 v2
      let ?v = "v1\<mapsto>v2"
      assume eq: "\<Delta> @ A # A # \<Sigma> = \<Gamma>1 @ ?v # \<Gamma>2" and c_ca: "c = Suc ca" and c_v: "C = v"
        and ca: "\<Gamma>1 @ \<Gamma>2 \<turnstile> ca : v"
      from eq show ?thesis
      proof (rule append_eq3_elim)
        fix \<Delta>' assume g1: "\<Gamma>1 = \<Delta> @ A # \<Delta>'" and eq2: "A # \<Sigma> = \<Delta>' @ ?v # \<Gamma>2"
        from eq2 show ?thesis
        proof (rule cons_append_eq3_elim)
          fix \<Delta>'' assume dp: "\<Delta>' = A # \<Delta>''" and s: "\<Sigma> = \<Delta>'' @ ?v # \<Gamma>2"
          have "\<Delta>@A#A#\<Delta>''@\<Gamma>2 \<turnstile> ca : C" using ca c_v dp s g1 by simp
          then obtain cb where "\<Delta>@A#\<Delta>''@\<Gamma>2 \<turnstile> cb : C" using 2 m c_ca 
              apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force by blast
          then have "(\<Delta>@A#\<Delta>'')@\<Gamma>2 \<turnstile> cb : C" by simp
          then have "(\<Delta>@A#\<Delta>'')@ ?v # \<Gamma>2 \<turnstile> Suc cb : C" by blast
          then show ?thesis using dp eq2 by auto
        next
          assume dp: "\<Delta>' = []" and a: "A = ?v" and s: "\<Sigma> = \<Gamma>2" 
          from ca dp s g1 c_v have "\<Delta> @ A # \<Sigma> \<turnstile> ca : C" by simp
          then show ?thesis by blast
        qed
      next
        fix \<Delta>' assume d: "\<Delta> = \<Gamma>1 @ ?v # \<Delta>'" and g2: "\<Gamma>2 = \<Delta>' @ A # A # \<Sigma>"
        have "(\<Gamma>1 @ \<Delta>') @ A # A # \<Sigma> \<turnstile> ca : C" using ca c_v d g2 by simp
        then obtain cb where "(\<Gamma>1 @ \<Delta>') @ A # \<Sigma> \<turnstile> cb : C" using 2 m c_ca
          apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force by blast
        then have "\<Gamma>1 @ (\<Delta>' @ A # \<Sigma>) \<turnstile> cb : C" by simp
        then have "\<Gamma>1 @ ?v # (\<Delta>' @ A # \<Sigma>) \<turnstile> Suc cb : C" by blast
        then show ?thesis using d by auto
      next
        assume d: "\<Delta> = \<Gamma>1" and a: "A = ?v" and eq2: "A # \<Sigma> = \<Gamma>2"
        then show ?thesis using ca c_v by blast
      qed
        
    next (* case union_R *)
      fix \<Gamma> ca v1 v2 assume g: "\<Delta> @ A # A # \<Sigma> = \<Gamma>" and c_ca: "c = Suc ca" and
        c_v12: "C = v1 \<squnion> v2" and ca_v1: "\<Gamma> \<turnstile> ca : v1" and ca_v2: "\<Gamma> \<turnstile> ca : v2" 
      obtain cb where cb_v1: "\<Delta>@A#\<Sigma> \<turnstile> cb : v1"  using 2 m c_ca ca_v1 g
        apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force by blast
      obtain cd where cd_v2: "\<Delta>@A#\<Sigma> \<turnstile> cd : v2"  using 2 m c_ca ca_v2 g
        apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force by blast
      have "\<Delta>@A#\<Sigma> \<turnstile> Suc (max cb cd) : v1 \<squnion> v2" using cb_v1 cd_v2 using weaken_size by auto
      then show ?thesis using c_v12 by blast
    
    next (* case union_L *)
      fix \<Gamma>1 v1 v2 \<Gamma>2 ca v
      assume eq: "\<Delta> @ A # A # \<Sigma> = \<Gamma>1 @ (v1 \<squnion> v2) # \<Gamma>2" and c_ca: "c = Suc ca" and
        c_v: "C = v" and ca: "\<Gamma>1 @ v1 # v2 # \<Gamma>2 \<turnstile> ca : v" 
      from eq show ?thesis
      proof (rule append_eq3_elim)
        fix \<Delta>' assume  g1: "\<Gamma>1 = \<Delta> @ A # \<Delta>'" and as: "A # \<Sigma> = \<Delta>' @ (v1 \<squnion> v2) # \<Gamma>2"
        show ?thesis
        proof (cases \<Delta>')
          case Nil
          from Nil as have a: "A = v1\<squnion>v2" by simp
          have ca2: "\<Delta> @ (v1\<squnion>v2) # v1 # v2 # \<Sigma> \<turnstile> ca : C" using g1 c_v ca as Nil by simp
          then obtain cb where cb: "\<Delta> @ v1 # v2 # v1 # v2 # \<Sigma> \<turnstile> cb : C" and cb_ca: "cb < ca" 
            using union_Le[of \<Delta> v1 v2 "v1 # v2 # \<Sigma>" ca C] by blast
          have "perm (\<Delta> @ v1 # v2 # v1 # v2 # \<Sigma>) (\<Delta> @ v1 # v1 # v2 # v2 # \<Sigma>)" 
            unfolding perm_def apply auto done
          then have "\<Delta> @ v1 # v1 # v2 # v2 # \<Sigma> \<turnstile> cb : C" using ex cb by auto
          then obtain cc where "\<Delta> @ v1 # v2 # v2 # \<Sigma> \<turnstile> cc : C" using 2 m a
            apply (erule_tac x="(size v1, cb)" in allE) apply (erule impE) apply force by blast
          then have "(\<Delta> @ [v1]) @ v2 # v2 # \<Sigma> \<turnstile> cc : C" by simp
          then obtain cd where "(\<Delta> @ [v1]) @ v2 # \<Sigma> \<turnstile> cd : C" using 2 m a
            apply (erule_tac x="(size v2, cc)" in allE) apply (erule impE) apply force apply blast done
          then show ?thesis using a by auto
        next
          case (Cons a \<Delta>'')
          then have ca2: "\<Delta> @ A # A # \<Delta>'' @ v1 # v2 # \<Gamma>2 \<turnstile> ca : C" using g1 c_v ca as by simp
          then obtain cb where "\<Delta> @ A # \<Delta>'' @ v1 # v2 # \<Gamma>2 \<turnstile> cb : C" using 2 m c_ca
            apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force apply blast done
          then have "(\<Delta> @ A # \<Delta>'') @ v1 # v2 # \<Gamma>2 \<turnstile> cb : C" by simp
          then have "(\<Delta> @ A # \<Delta>'') @ (v1 \<squnion> v2) # \<Gamma>2 \<turnstile> Suc cb : C" by blast
          then show ?thesis using Cons as by auto
        qed          
      next
        fix \<Delta>' assume d: "\<Delta> = \<Gamma>1 @ (v1 \<squnion> v2) # \<Delta>'" and g2: "\<Gamma>2 = \<Delta>' @ A # A # \<Sigma>" 
        have "(\<Gamma>1 @ v1 # v2 # \<Delta>') @ A # A # \<Sigma> \<turnstile> ca : C" using ca c_v d g2 by simp 
        then obtain cb where "(\<Gamma>1 @ v1 # v2 # \<Delta>') @ A # \<Sigma> \<turnstile> cb : C" using 2 m c_ca
          apply (erule_tac x="(size A, ca)" in allE) apply (erule impE) apply force by blast
        then have "\<Gamma>1 @ v1 # v2 # \<Delta>' @ A # \<Sigma> \<turnstile> cb : C" by simp
        then have "\<Gamma>1 @ (v1 \<squnion> v2) # \<Delta>' @ A # \<Sigma> \<turnstile> Suc cb : C" by blast          
        then show ?thesis using d by auto
      next
        assume d: "\<Delta> = \<Gamma>1" and a: "A = (v1\<squnion>v2)" and as: "A#\<Sigma> = \<Gamma>2"
        from ca d a as have "(\<Gamma>1 @ [v1, v2]) @ (v1\<squnion>v2) # \<Sigma> \<turnstile> ca : v" by auto
        then obtain cb where "(\<Gamma>1 @ [v1, v2]) @ v1 # v2 # \<Sigma> \<turnstile> cb : v" 
          using union_Le[of "(\<Gamma>1@ [v1, v2])" v1 v2 \<Sigma> ca v] by blast
        then have cb: "\<Gamma>1 @ [v1, v2, v1, v2] @ \<Sigma> \<turnstile> cb : v" by simp
        have "perm (\<Gamma>1 @ [v1, v2, v1, v2] @ \<Sigma>)
                   (\<Gamma>1 @ [v1, v1, v2, v2] @ \<Sigma>)" unfolding perm_def by auto
        then obtain cc where "\<Gamma>1 @ [v1, v1, v2, v2] @ \<Sigma> \<turnstile> cc : v" 
          using ex cb by blast
        then have "\<Gamma>1 @ v1 # v1 # [v2, v2] @ \<Sigma> \<turnstile> cc : v" by simp
        then obtain cd where "\<Gamma>1 @ v1 # [v2, v2] @ \<Sigma> \<turnstile> cd : v" 
          using 2 m d a as apply (erule_tac x="(size v1, cc)" in allE)
          apply (erule impE) apply force apply blast done
        then have "(\<Gamma>1 @ [v1]) @ v2 # v2 # \<Sigma> \<turnstile> cd : v" by simp
        then obtain ce where "(\<Gamma>1 @ [v1]) @ v2 # \<Sigma> \<turnstile> ce : v"
          using 2 m d a as apply (erule_tac x="(size v2, cd)" in allE)
          apply (erule impE) apply force apply blast done
        then have "\<Gamma>1 @ v1 # v2 # \<Sigma> \<turnstile> ce : v" by simp
        then have "\<Gamma>1 @ (v1 \<squnion> v2) # \<Sigma> \<turnstile> Suc ce : v" by blast
        then show ?thesis using d a as c_v by auto
      qed
        
    next (* case le_nat *)
      fix n ca assume "\<Delta> @ A # A # \<Sigma> = [VNat n]"
      then have "False" by simp
      then show ?thesis ..

    next (* case le_arrow *)
      fix \<Gamma> v1 ca v2 assume g: "\<Delta> @ A # A # \<Sigma> = \<Gamma>" and c_ca: "c = Suc ca" and
        c_v12: "C = v1 \<mapsto> v2" and afg: "all_funs \<Gamma>" and
        ca_v1: "\<forall>v v'. v \<mapsto> v' \<in> set \<Gamma> \<longrightarrow> [v1] \<turnstile> ca : v" and
        ca_v2: "map cod \<Gamma> \<turnstile> ca : v2"
      let ?G = "\<Delta> @ A # \<Sigma>"
      obtain A1 A2 where a: "A = A1\<mapsto>A2" using g afg apply (case_tac A) by auto
      have "map cod \<Gamma> = (map cod \<Delta>) @ A2 # A2 # (map cod \<Sigma>)" using g ca_v2 a by auto
      then have "(map cod \<Delta>) @ A2 # A2 # (map cod \<Sigma>) \<turnstile> ca : v2" using ca_v2 by simp
      then obtain cb where "(map cod \<Delta>) @ A2 # (map cod \<Sigma>) \<turnstile> cb : v2" using 2 m a
          apply (erule_tac x="(size A2, ca)" in allE) apply (erule impE) apply force by blast
      then have cb_v2: "map cod ?G \<turnstile> cb : v2" using a by simp
      have ca_v1: "\<forall>v v'. v \<mapsto> v' \<in> set ?G \<longrightarrow> [v1] \<turnstile> ca : v" 
        using ca_v1 g apply clarify 
        apply (subgoal_tac "v \<mapsto> v' \<in> set (\<Delta> @ A # A # \<Sigma>)") prefer 2 apply force by blast 
      have "all_funs ?G" using afg g by auto
      then have "?G \<turnstile> Suc (max ca cb) : v1 \<mapsto> v2" using cb_v2 ca_v1 
          le_arrow[of "?G" v1 "max ca cb" v2] weaken_size 
        by (metis (no_types, lifting) max.cobounded2 max_def)
      then show ?thesis using c_v12 by blast
    qed      
  qed
qed

lemma co_gen: "\<Delta> @ \<Gamma> @ \<Gamma> @ \<Sigma> \<turnstile> c : B \<Longrightarrow> \<exists>c'. \<Delta> @ \<Gamma> @ \<Sigma> \<turnstile> c' : B"
proof (induction \<Gamma> arbitrary: \<Delta> c)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  have "perm (\<Delta> @ (a # \<Gamma>) @ (a # \<Gamma>) @ \<Sigma>)
             (\<Delta> @ a # a # \<Gamma> @ \<Gamma> @ \<Sigma>)" unfolding perm_def by auto
  then obtain c' where "\<Delta> @ a # a # \<Gamma> @ \<Gamma> @ \<Sigma> \<turnstile> c' : B" using Cons.prems ex by blast
  then obtain c'' where "\<Delta> @ a # \<Gamma> @ \<Gamma> @ \<Sigma> \<turnstile> c'' : B" using co by blast
  then have "(\<Delta> @ [a]) @ \<Gamma> @ \<Gamma> @ \<Sigma> \<turnstile> c'' : B" by simp
  then obtain c3 where "(\<Delta> @ [a]) @ \<Gamma> @ \<Sigma> \<turnstile> c3 : B" 
    using Cons.IH[of "\<Delta>@[a]"] by blast 
  then show ?case by auto
qed

abbreviation cut_IH :: "nat \<times> nat \<times> nat \<Rightarrow> bool" where
  "cut_IH m \<equiv> \<forall>y. (y, m) \<in> less_than <*lex*> less_than <*lex*> less_than \<longrightarrow>
      (\<forall>\<Gamma> A \<Delta> \<Sigma> C c1 c2. y = (size A, c1, c2) \<longrightarrow> \<Gamma> \<turnstile> c1 : A \<longrightarrow>
          \<Delta> @ A # \<Sigma> \<turnstile> c2 : C \<longrightarrow> (\<exists>c3. \<Delta> @ \<Gamma> @ \<Sigma> \<turnstile> c3 : C))"   
  
lemma cut_any_wk: fixes \<Gamma>1 \<Gamma>2 c v'
  assumes c1: "\<Gamma> \<turnstile> c1 : A" and IH: "cut_IH m" and m: "m = (size A, c1, c2)" and
          1: "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ v' # \<Gamma>2 " and c2_c: "c2 = Suc c" and
          c: "\<Gamma>1 @ \<Gamma>2 \<turnstile> c : C" 
  shows "\<exists>c3. \<Delta>@\<Gamma>@\<Sigma> \<turnstile> c3 : C"
proof -
  let ?v = "v'"
  from 1 append_eq3[of \<Delta> A \<Sigma> \<Gamma>1 "?v" \<Gamma>2]
  have "(\<exists>ls. \<Gamma>1 = \<Delta> @ A # ls \<and> \<Sigma> = ls @ ?v # \<Gamma>2) \<or>
            (\<exists>ls. \<Delta> = \<Gamma>1 @ ?v # ls \<and> \<Gamma>2 = ls @ A # \<Sigma>) \<or>
             \<Delta> = \<Gamma>1 \<and> A = ?v \<and> \<Sigma> = \<Gamma>2 " by blast
  moreover { assume "\<exists>ls. \<Gamma>1 = \<Delta> @ A # ls \<and> \<Sigma> = ls @ ?v # \<Gamma>2"
    then obtain \<Delta>' where g1: "\<Gamma>1 = \<Delta> @ A # \<Delta>'" and s: "\<Sigma> = \<Delta>' @ ?v # \<Gamma>2" by blast
    with c have "\<Delta>@A#(\<Delta>'@\<Gamma>2) \<turnstile> c : C" by auto
    then obtain c' where cp: "\<Delta>@\<Gamma>@\<Delta>'@\<Gamma>2 \<turnstile> c' : C" using c1 c IH 
      apply (erule_tac x="(size A, c1, c)" in allE) apply (erule impE) 
       apply (simp add: c2_c less_eq m) apply blast done
    then
    have ?thesis using wk_gen[of "\<Delta>@\<Gamma>@\<Delta>'" \<Gamma>2 c' C] s by auto }
  moreover { assume "\<exists>ls. \<Delta> = \<Gamma>1 @ ?v # ls \<and> \<Gamma>2 = ls @ A # \<Sigma>"
    then obtain \<Delta>' where d: "\<Delta> = \<Gamma>1 @ ?v # \<Delta>'" and g2: "\<Gamma>2 = \<Delta>' @ A # \<Sigma>" by blast
    with c have "(\<Gamma>1 @ \<Delta>') @ A # \<Sigma> \<turnstile> c : C" by simp
    then obtain c' where cp: "(\<Gamma>1@\<Delta>')@\<Gamma>@\<Sigma> \<turnstile> c' : C" using c1 IH 
      apply (erule_tac x="(size A, c1, c)" in allE)  apply (erule impE) 
       apply (simp add: c2_c less_eq m) apply blast done 
    then have ?thesis using wk_gen[of \<Gamma>1 "\<Delta>'@\<Gamma>@\<Sigma>" c' C] d g2 by auto
  }
  moreover { assume das: "\<Delta> = \<Gamma>1 \<and> A = ?v \<and> \<Sigma> = \<Gamma>2"
    then have c_2: "\<Delta>@\<Sigma> \<turnstile> c : C" using c by simp
    then have ?thesis using weaken by blast }
  ultimately show ?thesis by blast
qed
  
lemma cut_any_union_R:
  fixes \<Gamma>' \<Gamma>'' c2' v1' v2' m assumes 2: "cut_IH m" and m: "m = (size A, c1, c2)" and
    c1p_v12: "\<Gamma>' \<turnstile> c1 : A" and
    gpp: "\<Delta> @ A # \<Sigma> = \<Gamma>''" and c2_c2p: "c2 = Suc c2'" and
    c_v12p: "C = v1' \<squnion> v2'" and
    c2p_v1p: "\<Gamma>'' \<turnstile> c2' : v1'" and c2p_v2p: "\<Gamma>'' \<turnstile> c2' : v2'" 
  shows "\<exists>c3. \<Delta>@\<Gamma>'@\<Sigma> \<turnstile> c3 : C"
proof -
  have "\<Delta> @ A # \<Sigma> \<turnstile> c2' : v1'" using gpp c2p_v1p by simp
  then obtain c3 where c3: "\<Delta> @ \<Gamma>' @ \<Sigma> \<turnstile> c3 : v1'" using c1p_v12 2 m c2_c2p
    apply (erule_tac x="(size A, c1, c2')" in allE) apply (erule impE) apply force apply blast done
  have "\<Delta> @ A # \<Sigma> \<turnstile> c2' : v2'" using gpp c2p_v2p by simp
  then obtain c4 where c4: "\<Delta> @ \<Gamma>' @ \<Sigma> \<turnstile> c4 : v2'" using c1p_v12 2 m c2_c2p
    apply (erule_tac x="(size A, c1, c2')" in allE) apply (erule impE) apply force apply blast done
  have "\<Delta> @ \<Gamma>' @ \<Sigma> \<turnstile> Suc (max c3 c4) : v1' \<squnion> v2'" using c3 c4 weaken_size by auto
  then show ?thesis using c_v12p by auto
qed 

lemma cut_any_union_L_part_1:
  fixes \<Gamma>' \<Gamma>1 v1' v2' \<Gamma>2 c2' v \<Delta>'
  assumes 2: "cut_IH m" and m: "m = (size A, c1, c2)" and
    c1p_v12: "\<Gamma>' \<turnstile> c1 : A" and
  eq:"\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1' \<squnion> v2') # \<Gamma>2" and 
  c2_c2p: "c2 = Suc c2'" and c2p_v: "\<Gamma>1 @ v1' # v2' # \<Gamma>2 \<turnstile> c2' : C" and
  g1: "\<Gamma>1 = \<Delta> @ A # \<Delta>'" and s: "\<Sigma> = \<Delta>' @ (v1' \<squnion> v2') # \<Gamma>2"
shows "\<exists>c3. \<Delta>@\<Gamma>'@\<Sigma> \<turnstile> c3 : C"
proof -
  have "\<Delta> @ A # (\<Delta>' @ v1' # v2' # \<Gamma>2) \<turnstile> c2' : C" using c2p_v g1 by simp
  then obtain c3 where "\<Delta> @ \<Gamma>' @ (\<Delta>' @ v1' # v2' # \<Gamma>2) \<turnstile> c3 : C" using c1p_v12 2 m c2_c2p
    apply (erule_tac x="(size A, c1, c2')" in allE) apply (erule impE) apply force apply blast done
  then have "(\<Delta> @ \<Gamma>' @ \<Delta>') @ v1' # v2' # \<Gamma>2 \<turnstile> c3 : C" by simp
  then have "(\<Delta> @ \<Gamma>' @ \<Delta>') @ (v1' \<squnion> v2') # \<Gamma>2 \<turnstile> Suc c3 : C" by blast
  then show ?thesis using s by auto
qed
          
lemma cut_any_union_L_part_2:
  fixes \<Gamma>' \<Gamma>1 v1' v2' \<Gamma>2 c2' v \<Sigma>'
  assumes 2: "cut_IH m" and m: "m = (size A, c1, c2)" and
    c1p_v12: "\<Gamma>' \<turnstile> c1 : A" and eq:"\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1' \<squnion> v2') # \<Gamma>2" and 
  c2_c2p: "c2 = Suc c2'" and c_v: "C = v" and c2p_v: "\<Gamma>1 @ v1' # v2' # \<Gamma>2 \<turnstile> c2' : v" and
  d: "\<Delta> = \<Gamma>1 @ (v1' \<squnion> v2') # \<Sigma>'" and g2: "\<Gamma>2 = \<Sigma>' @ A # \<Sigma>"
shows "\<exists>c3. \<Delta>@\<Gamma>'@\<Sigma> \<turnstile> c3 : C"
proof -
  have "(\<Gamma>1 @ v1' # v2' # \<Sigma>') @ A # \<Sigma> \<turnstile> c2' : C" using d g2 c_v c2p_v by simp 
  then obtain c3 where "(\<Gamma>1 @ v1' # v2' # \<Sigma>') @ \<Gamma>' @ \<Sigma> \<turnstile> c3 : C" using c1p_v12 2 m c2_c2p
    apply (erule_tac x="(size A, c1, c2')" in allE) apply (erule impE) apply force apply blast done
  then have "\<Gamma>1 @ v1' # v2' # (\<Sigma>' @ \<Gamma>' @ \<Sigma>) \<turnstile> c3 : C" by simp
  then have "\<Gamma>1 @ (v1' \<squnion> v2') # (\<Sigma>' @ \<Gamma>' @ \<Sigma>) \<turnstile> Suc c3 : C" by blast
  then show ?thesis using d g2 by auto
qed
  
lemma ex_larger: "\<exists>c. (\<forall>v v'. v \<mapsto> v' \<in> set G \<longrightarrow> f (v,v') \<le> (c::nat))"  
  apply (induction G)
   apply force
  apply clarify
  apply (case_tac a) apply simp apply blast defer apply simp apply blast apply simp
  apply (rule_tac x="max c (f (x21,x22))" in exI) apply clarify
  apply (rule conjI) apply (rule impI) apply force apply force
  done

lemma cut: "\<forall>\<Gamma> A \<Delta> \<Sigma> C c1 c2. m = (size A, c1, c2) \<longrightarrow>
   \<Gamma> \<turnstile> c1 : A \<longrightarrow> \<Delta>@A#\<Sigma> \<turnstile> c2 : C \<longrightarrow> (\<exists>c3. \<Delta>@\<Gamma>@\<Sigma> \<turnstile> c3 : C)" (is "?P m")
proof (induction m rule: wf_induct[of "less_than <*lex*> (less_than <*lex*> less_than)"])
  case 1
  then show ?case by auto
next
  case (2 m)
  show ?case 
  proof clarify
    fix \<Gamma> A \<Delta> \<Sigma> C c1 c2
    assume m: "m = (size A, c1, c2)" and c1: "\<Gamma> \<turnstile> c1 : A" and
      c2: "\<Delta> @ A # \<Sigma> \<turnstile> c2 : C"
    from c1 show "\<exists>c3. \<Delta> @ \<Gamma> @ \<Sigma> \<turnstile> c3 : C"
    proof (* case c1 is wk_nat *)
      fix \<Gamma>1 \<Gamma>2 c v n
      assume g: "\<Gamma> = \<Gamma>1 @ VNat n # \<Gamma>2" and c1_c: "c1 = Suc c" and
        a_v: "A = v" and c_v: "\<Gamma>1 @ \<Gamma>2 \<turnstile> c : v"
      then have "\<Gamma>1 @ \<Gamma>2 \<turnstile> c : A" by simp
      then obtain c' where "\<Delta>@(\<Gamma>1@\<Gamma>2)@\<Sigma> \<turnstile> c' : C" using 2 c1_c m c_v c2
        apply (erule_tac x="(size A, c, c2)" in allE) apply (erule impE) apply force
          apply blast done
      then have "(\<Delta>@\<Gamma>1)@(\<Gamma>2@\<Sigma>) \<turnstile> c' : C" by simp
      then show ?thesis using g wk_nat[of "\<Delta>@\<Gamma>1" "\<Gamma>2@\<Sigma>"] by auto
          
    next (* case c1 is wk_fun *)
      fix \<Gamma>1 \<Gamma>2 c1' v v1 v2 assume g: "\<Gamma> = \<Gamma>1 @ (v1 \<mapsto> v2) # \<Gamma>2" and
        c1_c1p: "c1 = Suc c1'" and A_v: "A = v" and c: "\<Gamma>1 @ \<Gamma>2 \<turnstile> c1' : v"
      then have "\<Gamma>1 @ \<Gamma>2 \<turnstile> c1' : A" by simp
      then obtain c' where "\<Delta>@(\<Gamma>1@\<Gamma>2)@\<Sigma> \<turnstile> c' : C" using 2 c1_c1p m c2
        apply (erule_tac x="(size A, c1', c2)" in allE) apply (erule impE) apply force apply blast done
      then have "(\<Delta>@\<Gamma>1)@(\<Gamma>2@\<Sigma>) \<turnstile> c' : C" by simp
      then show ?thesis using g wk_fun[of "\<Delta>@\<Gamma>1" "\<Gamma>2@\<Sigma>" c' C v1 v2] by auto
          
    next (* case c1 is union_R *)
      fix \<Gamma>' c1' v1 v2 assume g_gp: "\<Gamma> = \<Gamma>'" and c1_c1p: "c1 = Suc c1'" and 
        a: "A = v1 \<squnion> v2" and c1p_v1: "\<Gamma>' \<turnstile> c1' : v1" and c1p_v2: "\<Gamma>' \<turnstile> c1' : v2" 
      have c1p_v12: "\<Gamma>' \<turnstile> c1 : A" using c1p_v1 c1p_v2 a c1_c1p by blast
      
      show ?thesis using c2
      proof (* case c2 is wk_nat *)
        fix \<Gamma>1 \<Gamma>2 c v n assume eq: "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ VNat n # \<Gamma>2" and 
          c2_c: "c2 = Suc c" and c_v: "C = v" and c: "\<Gamma>1 @ \<Gamma>2 \<turnstile> c : v"
        then show ?thesis using  c1p_v12 2 m g_gp 
            cut_any_wk[of \<Gamma>' c1 A m c2 \<Delta> \<Sigma> \<Gamma>1] by blast
            
      next (* case c2 is wk_fun *)
        fix \<Gamma>1 \<Gamma>2 c v v1 v2 assume eq: "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1 \<mapsto> v2) # \<Gamma>2" and c2_c: "c2 = Suc c"
          and c_v: "C = v" and c: "\<Gamma>1 @ \<Gamma>2 \<turnstile> c : v"
        then show ?thesis using  c1p_v12 2 m g_gp 
            cut_any_wk[of \<Gamma>' c1 A m c2 \<Delta> \<Sigma> \<Gamma>1] by blast

      next (* case c2 is union_R *)
        fix \<Gamma>'' c2' v1' v2' assume gpp: "\<Delta> @ A # \<Sigma> = \<Gamma>''" and c2_c2p: "c2 = Suc c2'" and
          c_v12p: "C = v1' \<squnion> v2'" and c2p_v1p: "\<Gamma>'' \<turnstile> c2' : v1'" and c2p_v2p: "\<Gamma>'' \<turnstile> c2' : v2'" 
        then show ?thesis using 2 m g_gp c1p_v12 cut_any_union_R by blast            

      next (* case c2 is union_L *)
        fix \<Gamma>1 v1' v2' \<Gamma>2 c2' v assume eq:"\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1' \<squnion> v2') # \<Gamma>2" and 
          c2_c2p: "c2 = Suc c2'" and c_v: "C = v" and c2p_v: "\<Gamma>1 @ v1' # v2' # \<Gamma>2 \<turnstile> c2' : v"
        show ?thesis using eq
        proof (rule append_eq3_elim)
          fix \<Delta>' assume g1: "\<Gamma>1 = \<Delta> @ A # \<Delta>'" and s: "\<Sigma> = \<Delta>' @ (v1' \<squnion> v2') # \<Gamma>2"
          then show ?thesis using 2 m c1p_v12 eq c2_c2p c_v c2p_v g_gp
              cut_any_union_L_part_1[of m A c1 c2 \<Gamma>' \<Delta> \<Sigma> \<Gamma>1 v1' v2'] by blast
        next
          fix \<Sigma>' assume d: "\<Delta> = \<Gamma>1 @ (v1' \<squnion> v2') # \<Sigma>'" and g2: "\<Gamma>2 = \<Sigma>' @ A # \<Sigma>"
          then show ?thesis using 2 m c1p_v12 eq c2_c2p c_v c2p_v g_gp
              cut_any_union_L_part_2[of m A c1 c2 \<Gamma>' \<Delta> \<Sigma> \<Gamma>1 v1' v2'] by blast
        next
          assume d: "\<Delta> = \<Gamma>1" and a2: "A = v1' \<squnion> v2'" and s: "\<Sigma> = \<Gamma>2"
          have "\<Delta> @ v1' # v2' # \<Sigma> \<turnstile> c2' : C" using c2p_v d s c_v by simp
          then obtain c3 where c3: "\<Delta> @ \<Gamma>' @ v2' # \<Sigma> \<turnstile> c3 : C" using c1p_v1 2 m c1_c1p c2_c2p a a2
            apply (erule_tac x="(size v1', c1', c2')" in allE) apply (erule impE) 
             apply force apply blast done
          then have "(\<Delta> @ \<Gamma>') @ v2' # \<Sigma> \<turnstile> c3 : C" by simp
          then obtain c4 where c4: "(\<Delta> @ \<Gamma>') @ \<Gamma>' @ \<Sigma> \<turnstile> c4 : C" using c1p_v2 2 m c1_c1p c2_c2p a a2
            apply (erule_tac x="(size v2', c1', c3)" in allE) apply (erule impE) 
             apply force apply blast done
          then obtain c5 where "\<Delta> @ \<Gamma>' @ \<Sigma> \<turnstile> c5 : C" using co_gen[of \<Delta> \<Gamma>' \<Sigma>] by auto 
          then show ?thesis using g_gp by blast
        qed
          
      next (* case c2 is le_nat *)
        fix n c2' assume g: "\<Delta> @ A # \<Sigma> = [VNat n]" and c2_c2p: "c2 = c2'" and
          c_n: "C = VNat n" 
        have d: "\<Delta>=[]" using g apply (cases \<Delta>) by auto
        have "A = VNat n" using g d by simp
        then have "False" using a by simp then show ?thesis ..
            
      next (* case c2 is le_arrow *)
        fix \<Gamma>'' v1 c2' v2 assume gpp: "\<Delta> @ A # \<Sigma> = \<Gamma>''" and af_gp: "all_funs \<Gamma>''" 
        have "False" using af_gp a gpp by auto
        then show ?thesis ..
      qed

    next (* case c1 is union_L *)
      fix \<Gamma>1 v1 v2 \<Gamma>2 c1' v assume g: "\<Gamma> = \<Gamma>1 @ (v1 \<squnion> v2) # \<Gamma>2" and 
       c1_c: "c1 = Suc c1'" and A_v: "A = v" and c1p_v: "\<Gamma>1 @ v1 # v2 # \<Gamma>2 \<turnstile> c1' : v" 
      obtain c3 where "\<Delta>@(\<Gamma>1@v1#v2#\<Gamma>2)@\<Sigma> \<turnstile> c3 : C" using c1p_v c2 2 m c1_c g A_v
        apply (erule_tac x="(size A, c1', c2)" in allE) apply (erule impE) apply force by blast
      then have "(\<Delta>@\<Gamma>1)@v1#v2#(\<Gamma>2@\<Sigma>) \<turnstile> c3 : C" by simp
      then have "(\<Delta>@\<Gamma>1)@(v1\<squnion>v2)#(\<Gamma>2@\<Sigma>) \<turnstile> Suc c3 : C" by (rule union_L)
      then show ?thesis using g by auto
          
    next (* case c1 is le_nat *)
      fix n c1' assume g: "\<Gamma> = [VNat n]" and c1_c1p: "c1 = c1'" and a: "A = VNat n"
      then have c1p: "\<Gamma> \<turnstile> c1' : A" by blast
      show ?thesis using c2
      proof (* case c2 is wk_nat *)
        fix \<Gamma>1 \<Gamma>2 c2' v n assume eq: "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ VNat n # \<Gamma>2" and
          c2_c2p: "c2 = Suc c2'" and c_v: "C = v" and c2p_v: "\<Gamma>1 @ \<Gamma>2 \<turnstile> c2' : v"         
        then show ?thesis using g c1_c1p a cut_any_wk by auto
      next (* case c2 is wk_fun *)
        fix \<Gamma>1 \<Gamma>2 c v v1 v2 assume "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1 \<mapsto> v2) # \<Gamma>2" and 
          "c2 = Suc c" and "C = v" and "\<Gamma>1 @ \<Gamma>2 \<turnstile> c : v"
        then show ?thesis using g c1_c1p a cut_any_wk by auto
      next (* case c2 is union_R *)
        fix \<Gamma>' c v1 v2 assume "\<Delta> @ A # \<Sigma> = \<Gamma>'" and "c2 = Suc c" and "C = v1 \<squnion> v2" and
          "\<Gamma>' \<turnstile> c : v1" and "\<Gamma>' \<turnstile> c : v2"
        then show ?thesis using 2 m g c1p a cut_any_union_R by blast
      next (* case c2 is union_L *)
        fix \<Gamma>1 v1 v2 \<Gamma>2 c2' v assume eq: "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1 \<squnion> v2) # \<Gamma>2" and
          c2_c2p: "c2 = Suc c2'" and c_v: "C = v" and c2p_v: "\<Gamma>1 @ v1 # v2 # \<Gamma>2 \<turnstile> c2' : v"
        show ?thesis using eq
        proof (rule append_eq_elim)
          show "A \<noteq> v1 \<squnion> v2" using a by simp
        next
          fix ls assume "\<Gamma>1 = \<Delta> @ A # ls" and "\<Sigma> = ls @ (v1 \<squnion> v2) # \<Gamma>2"
          then show ?thesis using 2 m c1p eq c2_c2p c_v c2p_v c1_c1p
              cut_any_union_L_part_1[of m A c1 c2 \<Gamma> \<Delta> \<Sigma>] by blast 
        next
          fix ls assume "\<Delta> = \<Gamma>1 @ (v1 \<squnion> v2) # ls" and "\<Gamma>2 = ls @ A # \<Sigma>"
          then show ?thesis using 2 m c1p eq c2_c2p c_v c2p_v c1_c1p
              cut_any_union_L_part_2[of m A c1 c2 \<Gamma> \<Delta> \<Sigma>] by blast 
        qed
      next (* case c2 is le_nat *)
        fix n' c2' assume "\<Delta> @ A # \<Sigma> = [VNat n']" and "c2 = c2'" and "C = VNat n'" 
        then show ?thesis using a g by auto 
            
      next (* case c2 is le_arrow *)
        fix \<Gamma>' v1 c v2 assume "\<Delta> @ A # \<Sigma> = \<Gamma>'" and "all_funs \<Gamma>'"
        then have "False" using a by auto
        then show ?thesis ..
      qed        
          
    next (* case c1 is le_arrow *)
      fix \<Gamma>' A' c1' B assume g_gp: "\<Gamma> = \<Gamma>'" and c1_c1p: "c1 = Suc c1'" and 
        a: "A = A' \<mapsto> B" and af_gp: "all_funs \<Gamma>'" and 
        v1_c: "\<forall>v v'. v \<mapsto> v' \<in> set \<Gamma>' \<longrightarrow> [A'] \<turnstile> c1' : v" and
        c_B: "map cod \<Gamma>' \<turnstile> c1' : B"
      then have c1: "\<Gamma>' \<turnstile> c1 : A" by blast
      show ?thesis using c2
      proof (* c2 is wk_nat *)
        fix \<Gamma>1 \<Gamma>2 c2' v n assume "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ VNat n # \<Gamma>2" and "c2 = Suc c2'" and
          "C = v" and "\<Gamma>1 @ \<Gamma>2 \<turnstile> c2' : v" 
        then show ?thesis using 2 m c1 g_gp cut_any_wk[of \<Gamma>' c1 A m c2 \<Delta> \<Sigma> \<Gamma>1] by blast
          
      next (* c2 is wk_fun *)
        fix \<Gamma>1 \<Gamma>2 c v v1 v2 assume "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1 \<mapsto> v2) # \<Gamma>2" and "c2 = Suc c"
          and "C = v" and "\<Gamma>1 @ \<Gamma>2 \<turnstile> c : v"
        then show ?thesis using 2 m c1 g_gp cut_any_wk[of \<Gamma>' c1 A m c2 \<Delta> \<Sigma> \<Gamma>1] by blast

      next (* c2 is union_R *)
        fix \<Gamma>' c v1 v2 assume "\<Delta> @ A # \<Sigma> = \<Gamma>'" and "c2 = Suc c" and "C = v1 \<squnion> v2" and
          "\<Gamma>' \<turnstile> c : v1" and "\<Gamma>' \<turnstile> c : v2" 
        then show ?thesis using 2 m g_gp c1 cut_any_union_R[of m] by blast

      next (* c2 is union_L *)
        fix \<Gamma>1 v1 v2 \<Gamma>2 c2' v assume eq: "\<Delta> @ A # \<Sigma> = \<Gamma>1 @ (v1 \<squnion> v2) # \<Gamma>2" and 
          c2_c2p: "c2 = Suc c2'" and c_v: "C = v" and c2p: "\<Gamma>1 @ v1 # v2 # \<Gamma>2 \<turnstile> c2' : v"
        show ?thesis using eq
        proof (rule append_eq_elim)
          show "A \<noteq> v1 \<squnion> v2" using a by simp
        next
          fix ls assume "\<Gamma>1 = \<Delta> @ A # ls" and "\<Sigma> = ls @ (v1 \<squnion> v2) # \<Gamma>2"
          then show ?thesis using 2 m c1 eq c2_c2p c_v c2p c1_c1p g_gp
              cut_any_union_L_part_1[of m A c1 c2 \<Gamma> \<Delta> \<Sigma>] by blast
        next
          fix ls assume "\<Delta> = \<Gamma>1 @ (v1 \<squnion> v2) # ls" and "\<Gamma>2 = ls @ A # \<Sigma>"
          then show ?thesis using 2 m c1 eq c2_c2p c_v c2p c1_c1p g_gp
              cut_any_union_L_part_2[of m A c1 c2 \<Gamma> \<Delta> \<Sigma>] by blast
        qed
          
      next (* c2 is le_nat *)
        fix n c assume "\<Delta> @ A # \<Sigma> = [VNat n]"
        then have "False" using a apply (cases \<Delta>) apply auto done
        then show ?thesis ..
            
      next (* c2 is le_arrow *)
        fix \<Gamma>'' C' c2' D assume gpp: "\<Delta> @ A # \<Sigma> = \<Gamma>''" and c2_c2p: "c2 = Suc c2'" and 
          c_v12: "C = C' \<mapsto> D" and af_gpp: "all_funs \<Gamma>''" and 
          v1_c2p: "\<forall>v v'. v \<mapsto> v' \<in> set \<Gamma>'' \<longrightarrow> [C'] \<turnstile> c2' : v" and
          c2p_v2: "map cod \<Gamma>'' \<turnstile> c2' : D" 
        let ?G = "\<Delta> @ \<Gamma> @ \<Sigma>" 

        have c1_v2: "map cod \<Gamma> \<turnstile> c1' : B" using c_B g_gp by simp
        have c2p_v2p: "(map cod \<Delta>) @ B # (map cod \<Sigma>) \<turnstile> c2' : D" using c2p_v2 gpp a by auto
        obtain c3 where dgs_d_c3: "map cod ?G \<turnstile> c3 : D"
          using c2p_v2p gpp c1_v2 2 m c2_c2p g_gp a 
          apply (erule_tac x="(size B, c1', c2')" in allE) apply (erule impE) apply force
            apply simp by blast

        have af_dgs: "all_funs ?G" using af_gpp af_gp g_gp gpp by auto
        let ?cp = "max c1' (max c2' c3)"
        have c_dgs_aux: "\<forall>v v'. v \<mapsto> v' \<in> set ?G \<longrightarrow> (\<exists>c. [C'] \<turnstile> c : v)"
          apply clarify apply simp apply (erule disjE) defer apply (erule disjE) defer defer
        proof -
          fix v v' assume "v \<mapsto> v' \<in> set \<Delta>" 
          then have "[C'] \<turnstile> c2' : v" using v1_c2p gpp a by (erule_tac x=v in allE) auto
          then show "\<exists>c. [C'] \<turnstile> c : v" by blast
        next
          fix v v' assume vvp_g: "v \<mapsto> v' \<in> set \<Gamma>" 
          have c_a: "[C'] \<turnstile> ?cp : A'" using v1_c2p gpp a weaken_size[of "[C']" c2' A' ?cp] by force
          have a_v: "[A'] \<turnstile> ?cp : v"
            using vvp_g v1_c g_gp weaken_size[of "[A']" c1' v ?cp] max.cobounded1 by blast
          obtain c where "[C'] \<turnstile> c : v" using c_a a_v 2 m a
            apply (erule_tac x="(size A', ?cp, ?cp)" in allE) apply (erule impE) apply force 
              apply (erule_tac x="[C']" in allE)
              apply (erule_tac x="A'" in allE)
              apply (erule_tac x="[]" in allE)
            apply auto done
          then show "\<exists>c. [C'] \<turnstile> c : v" by blast
        next
          fix v v' assume "v \<mapsto> v' \<in> set \<Sigma>" 
          then have "[C'] \<turnstile> c2' : v" using v1_c2p gpp a by (erule_tac x=v in allE) auto
          then show "\<exists>c. [C'] \<turnstile> c : v" by blast
        qed
        (* The main work is done, but we still have to get the counters to line up. *)
        let ?Q = "\<lambda>vv c. fst vv \<mapsto> snd vv \<in> set ?G \<longrightarrow> [C'] \<turnstile> c : fst vv"
        have "\<forall>vv.\<exists>c. ?Q vv c" using c_dgs_aux by auto
        then have "\<exists>f. \<forall>vv. ?Q vv (f vv)" by (rule choice)
        then obtain f where c_dgs_f: "\<forall>v v'. v \<mapsto> v' \<in> set ?G \<longrightarrow> [C'] \<turnstile> f (v,v') : v" by auto
        obtain c' where cp:"\<forall>v v'. v \<mapsto> v' \<in> set ?G \<longrightarrow> f (v,v') \<le> c'" using ex_larger by blast
        have c_dgs_aux2: "\<forall>v v'. v \<mapsto> v' \<in> set ?G \<longrightarrow> [C'] \<turnstile> c' : v"
          using cp c_dgs_f weaken_size by blast
        let ?c = "max c' c3" 
        have c_dgs: "\<forall>v v'. v \<mapsto> v' \<in> set ?G \<longrightarrow> [C'] \<turnstile> ?c : v"   
          using c_dgs_aux2 apply clarify apply (erule_tac x=v in allE)
          apply (erule_tac x=v' in allE) apply (erule impE) apply blast
            using weaken_size apply auto done
        have dgs_d: "map cod ?G \<turnstile> ?c : D" using dgs_d_c3 weaken_size apply auto done
        show ?thesis using c_dgs dgs_d af_dgs c_v12 le_arrow[of ?G C' ?c D]
          by (meson max.cobounded2 weaken_size)          
      qed        
    qed
  qed
qed

section "Inversion Lemmas"

lemma d_empty_inv_aux: "\<lbrakk> \<Gamma> \<turnstile> c : v; \<Gamma>=[] \<rbrakk> \<Longrightarrow> False"
  by (induction \<Gamma> c v rule: deduce_le.induct) auto

lemma d_empty_elim[elim!]: "\<lbrakk> [] \<turnstile> c : v \<rbrakk> \<Longrightarrow> P"
  using d_empty_inv_aux by blast

fun atoms :: "val \<Rightarrow> val set" where
  "atoms (VNat n) = {VNat n}" |
  "atoms (v\<mapsto>v') = {v\<mapsto>v'}" |
  atoms_union: "atoms (v\<squnion>v') = atoms v \<union> atoms v'"  

lemma d_nat_inv: "\<lbrakk> \<Gamma> \<turnstile> c : v; v = VNat n \<rbrakk> \<Longrightarrow> VNat n \<in> (\<Union>v\<in>set \<Gamma>. atoms v)"
  by (induction \<Gamma> c v arbitrary: n rule: deduce_le.induct) auto 

lemma d_arrow_inv: "\<lbrakk> \<Gamma> \<turnstile> c : v; v = v1\<mapsto>v2 \<rbrakk> \<Longrightarrow>
   \<exists> \<Gamma>' c'. set \<Gamma>' \<subseteq> (\<Union>v\<in>set \<Gamma>. atoms v) \<and> all_funs \<Gamma>' 
       \<and> (\<forall> v v'. v\<mapsto>v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> c' : v)
       \<and> map cod \<Gamma>' \<turnstile> c' : v2"
proof (induction \<Gamma> c v arbitrary: v1 v2 rule: deduce_le.induct)
  case (wk_nat \<Gamma>1 \<Gamma>2 c v n)
  then obtain \<Gamma>' c' where "set \<Gamma>' \<subseteq> (\<Union>a\<in>set (\<Gamma>1 @ \<Gamma>2). atoms a)" and "all_funs \<Gamma>'" and
       "(\<forall>v v'. v \<mapsto> v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> c' : v)" and "map cod \<Gamma>' \<turnstile> c' : v2" by blast
  then show ?case by auto
next
  case (wk_fun \<Gamma>1 \<Gamma>2 c v v1 v2)
  then obtain \<Gamma>' c' where "set \<Gamma>' \<subseteq> (\<Union>a\<in>set (\<Gamma>1 @ \<Gamma>2). atoms a)" and "all_funs \<Gamma>'" and
       "(\<forall>v v'. v \<mapsto> v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> c' : v)" and "map cod \<Gamma>' \<turnstile> c' : v2" by blast
  then show ?case by auto
next
  case (union_R \<Gamma> c v1 v2)
  then have "False" by auto
  then show ?case ..
next
  case (union_L \<Gamma>1 u1 u2 \<Gamma>2 c v)
  then obtain \<Gamma>' c' where "set \<Gamma>' \<subseteq> (\<Union>a\<in>set (\<Gamma>1 @ u1 # u2 # \<Gamma>2). atoms a)" and "all_funs \<Gamma>'" and
       "(\<forall>v v'. v \<mapsto> v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> c' : v)" and "map cod \<Gamma>' \<turnstile> c' : v2" by blast
  then show ?case by auto
next
  case (le_nat n c)
  then have "False" by auto
  then show ?case ..
next
  case (le_arrow \<Gamma> v1' c v2')
  then show ?case apply (rule_tac x=\<Gamma> in exI) apply (rule_tac x=c in exI)
    apply (rule conjI) apply (rule subsetI) apply simp 
     apply (subgoal_tac "is_fun x") prefer 2 apply blast apply (rule_tac x=x in bexI) 
      apply (case_tac x) apply force apply force apply force apply blast
      apply (rule conjI) apply blast apply (rule conjI) apply blast apply blast done
qed
  
definition ctx_atoms :: "val list \<Rightarrow> val set" where
  "ctx_atoms \<Gamma> \<equiv> \<Union>a\<in>set \<Gamma>. atoms a" 
  
lemma d_nat_atoms_L_inv: "\<lbrakk> \<Gamma> \<turnstile> c : v; (\<forall>v. v \<in> ctx_atoms \<Gamma> \<longrightarrow> v = VNat n);
                         v' \<in> atoms v \<rbrakk> \<Longrightarrow> v' = VNat n"
proof (induction \<Gamma> c v arbitrary: n v' rule: deduce_le.induct)
  case (wk_nat \<Gamma>1 \<Gamma>2 c v n)
  then show ?case unfolding ctx_atoms_def 
    by (metis UN_E UN_I Un_insert_right insert_iff list.set(2) set_append)
next
  case (wk_fun \<Gamma>1 \<Gamma>2 c v v1 v2)
  then show ?case unfolding ctx_atoms_def 
    by (metis UN_E UN_I Un_insert_right insert_iff list.set(2) set_append)
next
  case (union_R \<Gamma> c v1 v2)
  then show ?case unfolding ctx_atoms_def by (metis Un_iff atoms.simps(3))
next
  case (union_L \<Gamma>1 v1 v2 \<Gamma>2 c v)
  have "ctx_atoms (\<Gamma>1 @ (v1 \<squnion> v2) # \<Gamma>2) = ctx_atoms (\<Gamma>1 @ v1 # v2 # \<Gamma>2)"
    unfolding ctx_atoms_def by auto
  then have " \<forall>v. v \<in> ctx_atoms (\<Gamma>1 @ v1 # v2 # \<Gamma>2) \<longrightarrow> v = VNat n" using union_L(3) by blast
  then show ?case using union_L.IH union_L.prems(2) by blast
next
  case (le_nat n' c)
  then show ?case unfolding ctx_atoms_def by auto 
next
  case (le_arrow \<Gamma> v1 c v2)
  have "\<Gamma> \<noteq> []" using le_arrow(2) by auto
  then have "False" using le_arrow(1) le_arrow(5) apply (case_tac \<Gamma>) apply force
    apply simp apply (case_tac a) apply force apply simp
      unfolding ctx_atoms_def apply auto done 
  then show ?case ..
qed 
  
    
section "Partial Order on Values"  
  
definition le_val :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "v1 \<sqsubseteq> v2 \<equiv> \<exists>c. [v2] \<turnstile> c : v1"

definition val_equiv :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<approx>" 55) where
  "v1 \<approx> v2 \<equiv> v1 \<sqsubseteq> v2 \<and> v2 \<sqsubseteq> v1"
  
proposition le_refl[simp]: "v \<sqsubseteq> v"
  unfolding le_val_def using ax by blast

proposition le_trans[trans]: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  unfolding le_val_def using cut 
  by (metis (full_types) append.left_neutral append_Cons)

lemma atoms_nat_deduce: "(\<forall>v. v \<in> atoms A \<longrightarrow> v = VNat n) \<Longrightarrow> \<exists>c. [VNat n] \<turnstile> c : A"     
  apply (induction A)
    apply force
   apply force
  apply (subgoal_tac "\<forall>v. v \<in> atoms A1 \<longrightarrow> v = VNat n") prefer 2 apply force
  apply (subgoal_tac "\<forall>v. v \<in> atoms A2 \<longrightarrow> v = VNat n") prefer 2 apply force
  apply simp apply clarify
  apply (rule_tac x="Suc (max c ca)" in exI) apply (rule union_R)
    apply (rule weaken_size) apply blast
  using max.cobounded1 apply blast
    apply (rule weaken_size) apply blast
  using max.cobounded2 apply blast
    done

lemma le_union_right1[intro]: assumes b_a1: "B \<sqsubseteq> A1" shows "B \<sqsubseteq> A1 \<squnion> A2"
proof -
  obtain c where "[A1] \<turnstile> c : B" using b_a1 unfolding le_val_def by auto
  then obtain c' where "[A1,A2] \<turnstile> c' : B" using wk_gen[of "[A1]" "[]" c B A2] by auto 
  then have "[A1\<squnion>A2] \<turnstile> Suc c' : B" using union_L[of "[]" A1 A2 "[]" c' B] by auto
  then show ?thesis unfolding le_val_def by blast
qed
  
lemma le_union_right2[intro]: assumes b_a2: "B \<sqsubseteq> A2" shows "B \<sqsubseteq> A1 \<squnion> A2"
proof -
  obtain c where "[A2] \<turnstile> c : B" using b_a2 unfolding le_val_def by auto
  then obtain c' where "[A1,A2] \<turnstile> c' : B" using wk_gen[of "[]" "[A2]" c B A1] by auto 
  then have "[A1\<squnion>A2] \<turnstile> Suc c' : B" using union_L[of "[]" A1 A2 "[]" c' B] by auto
  then show ?thesis unfolding le_val_def by blast
qed

lemma le_union_left[intro]: "\<lbrakk> A1 \<sqsubseteq> B; A2 \<sqsubseteq> B \<rbrakk> \<Longrightarrow> A1 \<squnion> A2 \<sqsubseteq> B"
  unfolding le_val_def apply clarify apply (rule_tac x="Suc (max c ca)" in exI)
    apply (rule union_R) using weaken_size apply auto done
     
lemma join_equiv_left:
  assumes a1: "A1 \<approx> B" and a2: "A2 \<approx> B" shows "A1 \<squnion> A2 \<approx> B"
proof -
  have "A1 \<squnion> A2 \<sqsubseteq> B"
  proof -
    have "A1 \<sqsubseteq> B" using a1 unfolding val_equiv_def by blast
    moreover have "A2 \<sqsubseteq> B" using a2 unfolding val_equiv_def by blast
    ultimately show ?thesis by blast
  qed    
  moreover have "B \<sqsubseteq> A1 \<squnion> A2" 
  proof -
    have "B \<sqsubseteq> A1" using a1 unfolding val_equiv_def by blast
    then show ?thesis by blast
  qed
  ultimately show ?thesis unfolding val_equiv_def by blast
qed
      
lemma atoms_nat_eq_nat: "(\<forall>v. v \<in> atoms A \<longrightarrow> v = VNat n) \<Longrightarrow> A \<approx> VNat n"
  apply (induction A)
  apply (simp add: val_equiv_def le_val_def)
   apply (simp add: val_equiv_def le_val_def) apply force
  apply simp
    
  apply (simp add: val_equiv_def le_val_def) 
  
  
    
  
  unfolding val_equiv_def le_val_def apply (rule conjI)
  using atoms_nat_deduce apply blast
    
  oops
  
  
lemma d_nat_any_inv: "\<lbrakk> \<Gamma> \<turnstile> c : v; \<Gamma> = [VNat n] \<rbrakk> \<Longrightarrow> v \<approx> VNat n"
  apply (induction \<Gamma> c v arbitrary: n rule: deduce_le.induct)
       apply (case_tac \<Gamma>1) apply force apply force
      apply (case_tac \<Gamma>1) apply force apply force
     apply (subgoal_tac "v1 \<approx> VNat n") prefer 2 apply blast    
     apply (subgoal_tac "v2 \<approx> VNat n") prefer 2 apply blast
     apply (simp add: val_equiv_def le_val_def)
     apply (rule conjI) apply (subgoal_tac "[VNat n] \<turnstile> Suc c : v1 \<squnion> v2") prefer 2 apply blast
      apply blast 
     apply (subgoal_tac "\<exists>c. [v1] \<turnstile> c : VNat n") prefer 2 apply blast apply clarify
    apply (subgoal_tac "\<exists>c. [v2] \<turnstile> c : VNat n") prefer 2 apply blast apply clarify
    oops
    
(*
section "Regular Values"  
  
datatype val2 = V2Nat nat | V2Fun func and
  func = End val2 val2 | Insert val2 val2 func
  
fun v2v :: "val2  \<Rightarrow> val" and f2v :: "func \<Rightarrow> val" where
  "v2v (V2Nat n) = VNat n" |
  "v2v (V2Fun f) = f2v f" |
  "f2v (End v v') = (v2v v) \<mapsto> (v2v v')" |
  "f2v (Insert v v' f) = VUnion ((v2v v) \<mapsto> (v2v v')) (f2v f)" 

definition le_val :: "val2 \<Rightarrow> val2 \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "v1 \<sqsubseteq> v2 \<equiv> \<exists>c. [v2v v2] \<turnstile> c : v2v v1"

    
  
proposition le_union_right1: fixes f::func 
  assumes 1: "V2Fun f \<sqsubseteq> V2Fun f1" shows "V2Fun f \<sqsubseteq> V2Fun (f1 @ f2)"    
proof -
  let ?v1 = "v2v (V2Fun f1)" and ?v2 = "v2v (V2Fun f2)" and ?v = "v2v (V2Fun f)"
  obtain c where "[?v1] \<turnstile> c : v2v (V2Fun f)" using 1 unfolding le_val_def by blast
  then obtain c' where "[?v1]@ ?v2 #[] \<turnstile> c' : v2v (V2Fun f)"
    using wk_gen[of "[?v1]" "[]" c "?v"] by auto 
  then have "[]@?v1# ?v2 #[] \<turnstile> c' : ?v" by simp
  then have "[]@(?v1 \<squnion> ?v2) #[] \<turnstile> Suc c' : ?v" using union_L by blast
  then show ?thesis unfolding le_val_def by auto
qed

proposition le_union_right2: fixes f::func 
  assumes 1: "V2Fun f \<sqsubseteq> V2Fun f2" shows "V2Fun f \<sqsubseteq> V2Fun (f1 \<squnion> f2)"    
proof -
  let ?v1 = "v2v (V2Fun f1)" and ?v2 = "v2v (V2Fun f2)" and ?v = "v2v (V2Fun f)"
  obtain c where "[?v2] \<turnstile> c : v2v (V2Fun f)" using 1 unfolding le_val_def by blast
  then obtain c' where "[]@ ?v1 #[?v2] \<turnstile> c' : v2v (V2Fun f)"
    using wk_gen[of "[]" "[?v2]" c "?v"] by auto 
  then have "[]@?v1# ?v2 #[] \<turnstile> c' : ?v" by simp
  then have "[]@(?v1 \<squnion> ?v2) #[] \<turnstile> Suc c' : ?v" using union_L by blast
  then show ?thesis unfolding le_val_def by auto
qed

proposition le_union_left:
  assumes 1: "V2Fun f1 \<sqsubseteq> V2Fun f3" and 2: "V2Fun f2 \<sqsubseteq> V2Fun f3"
  shows "V2Fun (f1 \<squnion> f2) \<sqsubseteq> V2Fun f3"
proof -
  let ?v1 = "v2v (V2Fun f1)" and ?v2 = "v2v (V2Fun f2)" and ?v3 = "v2v (V2Fun f3)"
  obtain c1 where 3: "[?v3] \<turnstile> c1 : ?v1" using 1 unfolding le_val_def by auto
  obtain c2 where 4: "[?v3] \<turnstile> c2 : ?v2" using 2 unfolding le_val_def by auto
  have "[?v3] \<turnstile> Suc (max c1 c2) : ?v1 \<squnion> ?v2" using 3 4 weaken_size union_R by auto
  then show ?thesis unfolding le_val_def by auto    
qed

proposition le_num: "V2Nat n \<sqsubseteq> V2Nat n" unfolding le_val_def by auto

proposition le_fun: 
  assumes 1: "v3 \<sqsubseteq> v1" and 2: "v2 \<sqsubseteq> v4"
  shows "V2Fun (v1 \<mapsto> v2) \<sqsubseteq> V2Fun (v3 \<mapsto> v4)"
  sorry
    
*)
    
end