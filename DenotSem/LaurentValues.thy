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
  
(*
fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] a = 0" |
  count_cons: "count (b#ls) a = (if a = b then 1 else 0) + count ls a"
*)

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
  
lemma ex: "\<lbrakk> \<Gamma> \<turnstile> c : v; perm \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> \<exists>c'. \<Gamma>' \<turnstile> c' : v"
proof (induction \<Gamma> c v arbitrary: \<Gamma>' rule: deduce_le.induct)
  case (wk_nat \<Gamma>1 \<Gamma>2 c v n)
  from wk_nat(3) obtain \<Gamma>1' \<Gamma>2' where gp: "\<Gamma>' = \<Gamma>1'@(VNat n)#\<Gamma>2'"
    using perm_ex_append[of \<Gamma>1] by blast
  have "perm (\<Gamma>1@\<Gamma>2) (\<Gamma>1'@\<Gamma>2')" using gp perm_remove_common1 wk_nat.prems by fastforce
  then obtain c' where cp: "\<Gamma>1'@\<Gamma>2' \<turnstile> c' : v" using wk_nat.IH by blast
  then show ?case using gp  by blast
next
  case (wk_fun \<Gamma>1 \<Gamma>2 c v v1 v2)
  from wk_fun(3) obtain \<Gamma>1' \<Gamma>2' where gp: "\<Gamma>' = \<Gamma>1'@(v1 \<mapsto> v2)#\<Gamma>2'"
    using perm_ex_append[of \<Gamma>1] by blast
  have "perm (\<Gamma>1@\<Gamma>2) (\<Gamma>1'@\<Gamma>2')" using gp perm_remove_common1 wk_fun.prems by fastforce
  then obtain c' where cp: "\<Gamma>1'@\<Gamma>2' \<turnstile> c' : v" using wk_fun.IH by blast
  then show ?case using gp by blast
next
  case (union_R \<Gamma> c v1 v2)
  obtain c1 where c1: "\<Gamma>' \<turnstile> c1 : v1" using union_R.IH(1) union_R.prems by blast
  obtain c2 where c2: "\<Gamma>' \<turnstile> c2 : v2" using union_R.IH(2) union_R.prems by blast
  then show ?case using c1 c2 apply (rule_tac x="Suc (max c1 c2)" in exI) 
    by (simp add: deduce_le.union_R weaken_size)
next
  case (union_L \<Gamma>1 v1 v2 \<Gamma>2 c v)
  from union_L.prems obtain \<Gamma>1' \<Gamma>2' where gp: "\<Gamma>' = \<Gamma>1'@(v1 \<squnion> v2)#\<Gamma>2'"
    using perm_ex_append[of \<Gamma>1] by blast
  have "perm (\<Gamma>1@\<Gamma>2) (\<Gamma>1'@\<Gamma>2')" using gp perm_remove_common1 using union_L.prems by fastforce
  then have "perm (\<Gamma>1 @ [v1, v2] @ \<Gamma>2) (\<Gamma>1' @ [v1, v2] @ \<Gamma>2')" using perm_add_common by blast
  then have "perm (\<Gamma>1 @ v1 # v2 # \<Gamma>2) (\<Gamma>1' @ v1 # v2 # \<Gamma>2')" by simp    
  with union_L.IH[of "\<Gamma>1' @ v1 # v2 # \<Gamma>2'"] obtain c' where
    cp: "\<Gamma>1' @ v1 # v2 # \<Gamma>2' \<turnstile> c' : v" by blast
  then show ?case using gp by blast
next
  case (le_nat n c)
  then have gp: "\<Gamma>' = [VNat n]" by simp
  then show ?case by auto
next
  case (le_arrow \<Gamma> v1 c v2)
  have af_gp: "all_funs \<Gamma>'" using le_arrow(1) le_arrow(5) using perm_set_eq by blast
  have "perm (map cod \<Gamma>) (map cod \<Gamma>')" using le_arrow.prems by blast
  then obtain c2 where c2: "map cod \<Gamma>' \<turnstile> c2 : v2" using le_arrow.IH(2) by blast
  have c1: "\<forall> v v'. v\<mapsto>v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> c : v"
  proof clarify
    fix v v' assume vv_gp: "v\<mapsto>v' \<in> set \<Gamma>'"
    then have "v\<mapsto>v' \<in> set \<Gamma>" using le_arrow.prems perm_set_eq by blast
    then show "[v1] \<turnstile> c : v" using le_arrow.IH(1) by blast
  qed
  let ?c = "max c2 c"
  have c2_2: "map cod \<Gamma>' \<turnstile> ?c : v2" using c2 weaken_size by auto
  have c1_2: "\<forall>v v'. v\<mapsto>v' \<in> set \<Gamma>' \<longrightarrow> [v1] \<turnstile> ?c : v" using c1 weaken_size by auto    
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
    
lemma union_Le: "\<lbrakk> \<Gamma>' \<turnstile> k : C; \<Gamma>' = \<Gamma>@(A\<squnion>B)#\<Delta> \<rbrakk> \<Longrightarrow> \<exists>k'. \<Gamma>@A#B#\<Delta> \<turnstile> k' : C \<and> k' < k"
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
    

    
end