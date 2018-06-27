theory LaurentValues
  imports Main "~~/src/HOL/Library/FSet" 
begin

datatype val = VNat nat | VArrow val val (infix "\<mapsto>" 60) | VUnion "val fset" ("\<Squnion>" 1000)

primrec flat :: "val \<Rightarrow> val fset" where
  "flat (VNat n) = {| VNat n|}" |
  "flat (v\<mapsto>v') = {|v\<mapsto>v'|}" |
  "flat (\<Squnion>V) = ffold funion bot (fimage flat V)"
  
interpretation funion_commute: comp_fun_commute "funion"
  unfolding comp_fun_commute_def by auto

abbreviation fdom :: "val \<Rightarrow> val fset \<Rightarrow> val fset" where
  "fdom v \<Gamma> \<equiv> (case v of v1\<mapsto>v1' \<Rightarrow> finsert v1 \<Gamma> | _ \<Rightarrow> \<Gamma>)"
abbreviation fcod :: "val \<Rightarrow> val fset \<Rightarrow> val fset" where
  "fcod v \<Gamma> \<equiv> (case v of v1\<mapsto>v1' \<Rightarrow> (flat v1') |\<union>| \<Gamma> | _ \<Rightarrow> \<Gamma>)"

interpretation fdom_commute: comp_fun_commute "fdom"
  unfolding comp_fun_commute_def apply clarify apply (rule ext) apply simp
  apply (case_tac y) apply auto apply (case_tac x, auto)+ done

interpretation fcod_commute: comp_fun_commute "fcod"
  unfolding comp_fun_commute_def apply clarify apply (rule ext) apply simp
  apply (case_tac y) apply auto apply (case_tac x, auto)+ done
    
definition doms :: "val fset \<Rightarrow> val fset" where
  "doms \<Gamma> \<equiv> ffold fdom bot \<Gamma>"
definition cods :: "val fset \<Rightarrow> val fset" where
  "cods \<Gamma> \<equiv> ffold fcod bot \<Gamma>"
  
inductive deduce_le :: "val fset \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _" [55,55] 56) where
  le_nat[intro!]: "VNat n \<in> fset \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> VNat n" |
  le_union[intro!]: "\<lbrakk> \<forall>v. v \<in> fset V \<longrightarrow> \<Gamma> \<turnstile> v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<Squnion>V" |
  le_arrow[intro!]: "\<lbrakk>fset \<Gamma>'\<subseteq>fset \<Gamma>; flat v1 \<turnstile> \<Squnion>(doms \<Gamma>'); cods \<Gamma>' \<turnstile> v1'\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> v1 \<mapsto> v1'"
  
inductive_cases le_nat_inv: "\<Gamma> \<turnstile> VNat n"
  
lemma weaken: "\<lbrakk> \<Gamma> \<turnstile> v; fset \<Gamma> \<subseteq> fset \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> v"
  apply (induction arbitrary: \<Gamma>' rule: deduce_le.induct)
     apply force
    apply force
   apply (subgoal_tac "fset \<Gamma>' \<subseteq> fset \<Gamma>''") apply blast apply blast   
  done
  
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