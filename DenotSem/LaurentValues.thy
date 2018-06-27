theory LaurentValues
  imports Main
begin

datatype val = VNat nat | VArrow val val (infix "\<mapsto>" 60) | VUnion val val (infix "\<squnion>" 61) | VBot
  
abbreviation fdom :: "val \<Rightarrow> val \<Rightarrow> val" where
  "fdom v \<Gamma> \<equiv> (case v of v1\<mapsto>v1' \<Rightarrow> v1 \<squnion> \<Gamma> | _ \<Rightarrow> \<Gamma>)"
abbreviation fcod :: "val \<Rightarrow> val list \<Rightarrow> val list" where
  "fcod v \<Gamma> \<equiv> (case v of v1\<mapsto>v1' \<Rightarrow> v1'#\<Gamma> | _ \<Rightarrow> \<Gamma>)"
abbreviation is_fun :: "val \<Rightarrow> bool" where
  "is_fun v \<equiv> (case v of v1\<mapsto>v2 \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation all_funs :: "val list \<Rightarrow> bool" where
  "all_funs \<Gamma> \<equiv> fold (\<lambda>v b. is_fun v \<and> b) \<Gamma> True"

definition doms :: "val list \<Rightarrow> val" where
  "doms \<Gamma> \<equiv> fold fdom \<Gamma> VBot"
definition cods :: "val list \<Rightarrow> val list" where
  "cods \<Gamma> \<equiv> fold fcod \<Gamma> []"

datatype coercion = CWkNat coercion | CWkFun coercion | CWkBot coercion 
  | CNat nat | CArrow coercion coercion
  | CUnionR coercion coercion | CUnionL coercion

inductive deduce_le :: "val list \<Rightarrow> coercion \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 56) where
  wk_nat[intro!]: "\<lbrakk> \<Gamma>=\<Gamma>1@(VNat n)#\<Gamma>2; \<Gamma>1@\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CWkNat c: v" | 
  wk_fun[intro!]: "\<lbrakk> \<Gamma>=\<Gamma>1@(v1\<mapsto>v1')#\<Gamma>2; \<Gamma>1@\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CWkFun c: v" |
  wk_bot[intro!]: "\<lbrakk> \<Gamma>=\<Gamma>1@(VBot)#\<Gamma>2; \<Gamma>1@\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CWkBot c: v" | 
  union_R[intro!]: "\<lbrakk> \<Gamma> \<turnstile> c1 : v1; \<Gamma> \<turnstile> c2 : v2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CUnionR c1 c2 : v1 \<squnion> v2" |
  union_L[intro]: "\<lbrakk> \<Gamma>=\<Gamma>1@(v1\<squnion>v2)#\<Gamma>2; \<Gamma>1@v1#v2#\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CUnionL c : v" | 
  le_nat[intro!]: "[VNat n] \<turnstile> CNat n : VNat n" |
  le_arrow[intro!]: "\<lbrakk> all_funs \<Gamma>; [v1] \<turnstile> c1 : doms \<Gamma>'; cods \<Gamma>' \<turnstile> c2 : v1'\<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> CArrow c1 c2 : v1 \<mapsto> v1'"
  
inductive_cases
   cwknat_inv[elim!]: "\<Gamma> \<turnstile> CWkNat c : v" and
   cwkfun_inv[elim!]: "\<Gamma> \<turnstile> CWkFun c : v" and
   cwkbot_inv[elim!]: "\<Gamma> \<turnstile> CWkBot c : v" and
   cunionr_inv[elim!]: "\<Gamma> \<turnstile> CUnionR c1 c2 : v" and
   cunionl_inv[elim!]: "\<Gamma> \<turnstile> CUnionL c : v" and
   cnat_inv[elim!]: "\<Gamma> \<turnstile> CNat n : v" and
   carrow_inv[elim!]: "\<Gamma> \<turnstile> CArrow c1 c2 : v"

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] a = 0" |
  "count (b#ls) a = (if a = b then Suc (count ls a) else count ls a)"

definition perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "perm \<Gamma> \<Gamma>' \<equiv> (\<forall> x. count \<Gamma> x = count \<Gamma>' x)"
  
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
  
  
    
    
end