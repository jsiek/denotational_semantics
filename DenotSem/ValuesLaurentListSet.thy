theory ValuesLaurentListSet
  imports Main "~~/src/HOL/Library/FSet" 
begin

datatype val = VNat nat | VArrow val val (infix "\<mapsto>" 60) | VUnion val val (infix "\<squnion>" 59)
  
abbreviation is_fun :: "val \<Rightarrow> bool" where
  "is_fun v \<equiv> (case v of v1\<mapsto>v2 \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation all_funs :: "val list \<Rightarrow> bool" where
  "all_funs \<Gamma> \<equiv> fold (\<lambda>v b. is_fun v \<and> b) \<Gamma> True"

fun dom :: "val \<Rightarrow> val" where
  "dom (v\<mapsto>v') = v" 
  
fun cod :: "val \<Rightarrow> val" where
  "cod (v\<mapsto>v') = v'"

datatype coercion = CWkNat coercion | CWkFun coercion 
  | CNat nat | CArrow coercion coercion
  | CUnionR coercion | CUnionL coercion | CNil | CCons coercion coercion

inductive deduce_le :: "val list \<Rightarrow> coercion \<Rightarrow> val list \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 56) where
  empty_R[intro!]: "xs \<turnstile> CNil : []" |
  cons_R[intro!]: "\<lbrakk> v \<in> set vs; remove1 v vs \<noteq> []; xs \<turnstile> c1 : [v]; xs \<turnstile> c2 : remove1 v vs \<rbrakk> 
    \<Longrightarrow> xs \<turnstile> CCons c1 c2 : vs" |
  wk_nat[intro!]: "\<lbrakk> VNat n \<in> set xs; remove1 (VNat n) xs \<turnstile> c : [v] \<rbrakk> \<Longrightarrow> xs \<turnstile> CWkNat c : [v]" | 
  wk_fun[intro!]: "\<lbrakk> v1\<mapsto>v1' \<in> set xs; remove1 (v1\<mapsto>v1') xs \<turnstile> c : [v] \<rbrakk> \<Longrightarrow> xs \<turnstile> CWkFun c : [v]" |
    union_R[intro!]: "\<lbrakk> xs \<turnstile> c : v1#v2#(remove1 (v1\<squnion>v2) ys) \<rbrakk> \<Longrightarrow> xs \<turnstile> CUnionR c : [v1\<squnion>v2]" |
    union_L[intro]: "\<lbrakk> v1#v2#(remove1 (v1\<squnion>v2) xs) \<turnstile> c : ys \<rbrakk> \<Longrightarrow> xs \<turnstile> CUnionL c : [v1\<squnion>v2]" | 
  le_nat[intro!]: "[VNat n] \<turnstile> CNat n : [VNat n]" |
  le_arrow[intro!]: "\<lbrakk> all_funs xs; [v1] \<turnstile> c1 : map dom xs; map cod xs \<turnstile> c2 : [v1'] \<rbrakk>
    \<Longrightarrow> xs \<turnstile> CArrow c1 c2 : [v1 \<mapsto> v1']"

inductive_cases
   cwknat_inv[elim!]: "xs \<turnstile> CWkNat c : ys" and
   cwkfun_inv[elim!]: "xs \<turnstile> CWkFun c : ys" and
   cunionr_inv[elim!]: "xs \<turnstile> CUnionR c : ys" and
   cunionl_inv[elim!]: "xs \<turnstile> CUnionL c : ys" and
   cnat_inv[elim!]: "xs \<turnstile> CNat n : ys" and
   carrow_inv[elim!]: "xs \<turnstile> CArrow c1 c2 : ys" and
   cnil_inv[elim!]: "xs \<turnstile> CNil : ys" and
   ccons_inv[elim!]: "xs \<turnstile> CCons c1 c2 : ys"
  
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

lemma perm_remove1[intro!]: "perm xs ys \<Longrightarrow> perm (remove1 v xs) (remove1 v ys)"
  unfolding perm_def apply clarify apply (erule_tac x=x in allE)
  apply (case_tac "x=v") apply simp apply simp done
  
lemma perm_cons[intro!]: "perm xs ys \<Longrightarrow> perm (a#xs) (a#ys)"
  unfolding perm_def apply clarify apply (erule_tac x=x in allE) by simp

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

lemma all_zero_empty: "\<forall>x. count ys x = 0 \<Longrightarrow> ys = []"
  apply (induction ys)
  apply force
  apply simp apply (erule_tac x=a in allE) apply simp
  done
    
lemma perm_cons_remove1: "perm (a # xs) ys \<Longrightarrow> perm xs (remove1 a ys)"
  unfolding perm_def apply clarify apply (erule_tac x=x in allE) apply simp
    apply (case_tac "x=a") apply auto done
    
lemma perm_eq_len: "perm xs ys \<Longrightarrow> length xs = length ys"
  apply (induction xs arbitrary: ys)
   apply (simp add: perm_def)
  apply simp
  apply (subgoal_tac "set (a#xs) = set ys") prefer 2 apply (rule perm_set_eq) apply blast
    
  apply (subgoal_tac "perm xs (remove1 a ys)") 
   apply (subgoal_tac "length xs = length (remove1 a ys)") prefer 2 apply blast
  apply (metis One_nat_def Suc_pred length_pos_if_in_set length_remove1 list.set_intros(1))
  apply (rule perm_cons_remove1) apply blast
  done
    
lemma perm_single[simp]: "perm [x] ys \<Longrightarrow> ys = [x]"
  apply (subgoal_tac "set [x] = set ys")
   apply (subgoal_tac "length [x] = length ys")
  apply (metis length_0_conv length_Cons length_Suc_conv the_elem_set)
  using perm_eq_len apply blast    
  using perm_set_eq by blast

  
    
lemma perm_map[intro]: "perm xs ys \<Longrightarrow> perm (map f xs) (map f ys)"
  unfolding perm_def apply clarify sorry

lemma perm_all_funs[simp]: "perm \<Gamma> \<Gamma>' \<Longrightarrow> (all_funs \<Gamma>) = (all_funs \<Gamma>')"
  sorry
    
lemma ex: "\<lbrakk> xs \<turnstile> c : ys; perm xs xs' \<rbrakk> \<Longrightarrow> \<exists>c' ys'. xs' \<turnstile> c' : ys' \<and> perm ys ys'"
  apply (induction arbitrary: xs' rule: deduce_le.induct)
    (*
    -- "case wk_nat" 
    apply (subgoal_tac "perm (remove1 (VNat n) \<Gamma>) (remove1 (VNat n) \<Gamma>')") prefer 2 apply force
       apply (subgoal_tac "\<exists>c'. remove1 (VNat n) \<Gamma>' \<turnstile> c' : v") prefer 2 apply blast apply clarify
    apply (rule_tac x="CWkNat c'" in exI)
       apply (rule wk_nat)
        apply (subgoal_tac "set \<Gamma> = set \<Gamma>'") prefer 2 apply (rule perm_set_eq) apply assumption
        apply blast apply assumption
   -- "case wk_fun"
    apply (subgoal_tac "perm (remove1 (v1 \<mapsto> v1') \<Gamma>) (remove1 (v1 \<mapsto> v1') \<Gamma>')") prefer 2 apply force
       apply (subgoal_tac "\<exists>c'. remove1 (v1 \<mapsto> v1') \<Gamma>' \<turnstile> c' : v") prefer 2 apply blast apply clarify
    apply (rule_tac x="CWkFun c'" in exI)
       apply (rule wk_fun)
        apply (subgoal_tac "set \<Gamma> = set \<Gamma>'") prefer 2 apply (rule perm_set_eq) apply assumption
        apply blast apply assumption
   -- "case union_R"
     apply force
   -- "case union_L"
    apply (subgoal_tac "perm (v1 # v2 # remove1 (v1 \<squnion> v2) \<Gamma>) (v1#v2#remove1 (v1 \<squnion> v2) \<Gamma>')")
     prefer 2 apply force
    apply (subgoal_tac "\<exists>c'. v1#v2#remove1 (v1 \<squnion> v2) \<Gamma>' \<turnstile> c' : v") prefer 2 apply blast apply clarify
    apply (rule_tac x="CUnionL c'" in exI) apply (rule union_L) 
     apply (subgoal_tac "set \<Gamma> = set \<Gamma>'") prefer 2 using perm_set_eq apply blast
     apply blast apply assumption
   -- "case le_nat"
   apply (rule_tac x="CNat n" in exI)
   apply (subgoal_tac "\<Gamma>' = [VNat n]") apply force apply force
   -- "case le_arrow"
   apply (subgoal_tac "perm [v1] [v1]")
   apply (subgoal_tac "\<exists>c'. [v1] \<turnstile> c' : doms \<Gamma>") prefer 2 apply blast apply (erule exE)
    apply (subgoal_tac "perm (cods \<Gamma>) (cods \<Gamma>')") prefer 2 apply (rule perm_cods) apply blast
    apply (subgoal_tac "\<exists>c'. cods \<Gamma>' \<turnstile> c' : v1'") prefer 2 apply blast apply (erule exE)
   apply (rule_tac x="CArrow c' c'a" in exI) apply (rule le_arrow) apply force
    
    defer *)
  oops
    
end