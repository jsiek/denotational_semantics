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

datatype coercion = CWk coercion | CNat nat | CArrow coercion coercion | CUnionR coercion coercion 
  | CUnionL coercion
      
inductive deduce_le :: "val list \<Rightarrow> coercion \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 56) where
  wk[intro!]: "\<lbrakk> \<Gamma>=\<Gamma>1@(VNat n)#\<Gamma>2; \<Gamma>1@\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CWk c: v" | 
  union_R[intro!]: "\<lbrakk> \<Gamma> \<turnstile> c1 : v1; \<Gamma> \<turnstile> c2 : v2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CUnionR c1 c2 : v1 \<squnion> v2" |
  union_L[intro]: "\<lbrakk> \<Gamma>=\<Gamma>1@(v1\<squnion>v2)#\<Gamma>2; \<Gamma>1@v1#v2#\<Gamma>2 \<turnstile> c : v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> CUnionL c : v" | 
  le_nat[intro!]: "[VNat n] \<turnstile> CNat n : VNat n" |
  le_arrow[intro!]: "\<lbrakk> all_funs \<Gamma>; [v1] \<turnstile> c1 : doms \<Gamma>'; cods \<Gamma>' \<turnstile> c2 : v1'\<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> CArrow c1 c2 : v1 \<mapsto> v1'"
  
inductive_cases
   cwk_inv[elim!]: "\<Gamma> \<turnstile> CWk c : v" and
   cunionr_inv[elim!]: "\<Gamma> \<turnstile> CUnionR c1 c2 : v" and
   cunionl_inv[elim!]: "\<Gamma> \<turnstile> CUnionL c : v" and
   cnat_inv[elim!]: "\<Gamma> \<turnstile> CNat n : v" and
   carrow_inv[elim!]: "\<Gamma> \<turnstile> CArrow c1 c2 : v"

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] a = 0" |
  "count (b#ls) a = (if a = b then Suc (count ls a) else count ls a)"

definition perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "perm \<Gamma> \<Gamma>' \<equiv> (\<forall> x. count \<Gamma> x = count \<Gamma>' x)"
  
lemma count_remove1_same: "count (remove1 v ls) v = (count ls v) - 1"
  apply (induction ls) apply auto done

lemma count_remove1_diff: "v \<noteq> v' \<Longrightarrow> count (remove1 v ls) v' = count ls v'"
  apply (induction ls) apply auto done

lemma count_remove_mid_same: "count (xs@v#ys) v = 1 + count (xs@ys) v"
  apply (induction xs) by auto

lemma count_remove_mid_diff: "v \<noteq> v' \<Longrightarrow> count (xs@v#ys) v' = count (xs@ys) v'"
  apply (induction xs) by auto
    
lemma perm_remove1: "perm (\<Gamma>1@v#\<Gamma>2) \<Gamma> \<Longrightarrow> perm (\<Gamma>1@\<Gamma>2) (remove1 v \<Gamma>)"
  unfolding perm_def 
  by (metis add_diff_cancel_left' count_remove1_diff count_remove1_same 
      count_remove_mid_diff count_remove_mid_same)  
  
lemma remove1_append_notin: "v \<notin> set ys \<Longrightarrow> remove1 v (ys @ v # zs) = ys @ zs"
    
  
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
    
    
    
lemma ex: "\<lbrakk> \<Gamma> \<turnstile> c : v; perm \<Gamma> \<Gamma>' \<rbrakk> \<Longrightarrow> \<exists>c'. \<Gamma>' \<turnstile> c' : v"
  apply (induction arbitrary: \<Gamma>' rule: deduce_le.induct)
      apply (subgoal_tac "perm (\<Gamma>1@\<Gamma>2) (remove1 (VNat n) \<Gamma>')") prefer 2 
       apply (rule perm_remove1) apply force
    apply (subgoal_tac " \<exists>c'. remove1 (VNat n) \<Gamma>' \<turnstile> c' : v") prefer 2 apply blast
      apply clarify
    
    
lemma wk_gen: "\<forall> c v v' \<Gamma> \<Delta>. n = size c \<longrightarrow> \<Gamma>@\<Delta> \<turnstile> c : v \<longrightarrow> (\<exists>c'. \<Gamma>@v'#\<Delta> \<turnstile> c' : v)"
  apply (induction n rule: nat_less_induct)
  apply clarify
  apply (case_tac c)
  
    
lemma weaken: "\<lbrakk> \<Gamma> \<turnstile> c : v; fset \<Gamma> \<subseteq> fset \<Gamma>' \<rbrakk> \<Longrightarrow> \<exists>c'. \<Gamma>' \<turnstile> c' : v"
 oops
  
lemma mem_flat_union: "v \<in> fset V \<Longrightarrow>
           fset (flat v) \<subseteq> fset (ffold funion bot (flat |`| V))"
  apply (induction V arbitrary: v)
  apply force
  apply simp
  apply (erule disjE)
   apply clarify apply simp
  oops

lemma axiom: "flat v \<turnstile> v"
  apply (induction v) 
  apply force
  apply simp apply (rule le_arrow) apply blast
     unfolding doms_def apply force
     unfolding cods_def apply force       
  apply (rename_tac V)
     apply (rule le_union) apply clarify
     apply (subgoal_tac "flat v \<turnstile> v") prefer 2 apply blast
     apply simp
       
    apply (rule weaken) apply assumption apply simp 
  done
    
lemma cut: "\<lbrakk> \<Gamma> \<turnstile> v2; \<Gamma>=finsert v1 \<Gamma>2; \<Gamma>1 \<turnstile> v1 \<rbrakk> \<Longrightarrow> \<Gamma>1|\<union>|\<Gamma>2 \<turnstile> v2"    
  apply (induction \<Gamma> v2 arbitrary: v1 \<Gamma>1 \<Gamma>2 rule: deduce_le.induct)
  apply clarify apply simp apply (erule disjE) 
  
    
    
end