theory SemValues
  imports Main
begin
  
datatype val = VNat nat | VFun "(val \<times> val) list"

  
section "Intersection Types and Semantic Subtyping"  
  
datatype ty = TNat nat | TArrow ty ty (infix "\<rightarrow>" 65) | TInter ty ty (infix "\<sqinter>" 64) | TBot ("\<bottom>")

fun M :: "ty \<Rightarrow> val set" where
  "M (TNat n) = {VNat n}" |
  "M (T1\<rightarrow>T2) = {VFun f'|f'. \<forall>v v'. (v,v') \<in> set f' \<longrightarrow> v \<in> M T1 \<longrightarrow> v' \<in> M T2}" |
  "M (T1\<sqinter>T2) =  M T1 \<inter> M T2" |
  "M \<bottom> = {}"

definition subtype :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "<:" 60) where
  "T1 <: T2 \<equiv> M T1 \<subseteq> M T2"
  
lemma sub_arrow[intro!]: fixes A::ty and C::ty shows "\<lbrakk> C <: A; B <: D \<rbrakk> \<Longrightarrow> A \<rightarrow> B <: C \<rightarrow> D"
  unfolding subtype_def apply simp apply clarify apply (rule_tac x=f' in exI) apply auto done
  
lemma sub_dist[intro!]: "(A\<rightarrow>B)\<sqinter>(A\<rightarrow>C) <: A\<rightarrow>(B\<sqinter>C)"
  unfolding subtype_def apply simp apply clarify apply (rule_tac x=f'a in exI) by auto

lemma sub_inter_lb1[intro!]: fixes A::ty shows "A \<sqinter> B <: A"
  unfolding subtype_def by auto
    
lemma sub_inter_lb2[intro!]: fixes A::ty shows "A \<sqinter> B <: B"
  unfolding subtype_def by auto
    
lemma sub_inter_glb[intro!]: "\<lbrakk> C <: A; C <: B \<rbrakk> \<Longrightarrow> C <: A \<sqinter> B"
  unfolding subtype_def by auto 
    
lemma sub_refl[intro!]: "A <: A"
  unfolding subtype_def by blast

lemma sub_trans[trans]: "\<lbrakk> A <: B; B <: C \<rbrakk> \<Longrightarrow> A <: C"
  unfolding subtype_def by blast
    
fun inters :: "ty list \<Rightarrow> ty" ("\<Sqinter>") where 
  "\<Sqinter> [] = \<bottom>" |
  "\<Sqinter> (A#ls) = A \<sqinter> (\<Sqinter> ls)"  

definition arrows2ty :: "(ty\<times>ty) list \<Rightarrow> ty" where
  "arrows2ty ls \<equiv> \<Sqinter> (map (\<lambda>(A,B). A\<rightarrow>B) ls)"
declare arrows2ty_def[simp]
    
lemma sub_any_bot_empty: "A <: \<bottom> \<Longrightarrow> M A = {}"
  unfolding subtype_def by auto

lemma fun_inhabit: "\<exists> v. v \<in> M (A\<rightarrow>B)"
  apply simp apply (rule_tac x="[]" in exI) apply auto done

lemma fun_non_empty: "M (A\<rightarrow>B) \<noteq> {}"
  apply simp apply (rule_tac x="[]" in exI) apply auto done

lemma sub_fun_bot_inv[elim!]: "A \<rightarrow> B <: \<bottom> \<Longrightarrow> P"
  apply (subgoal_tac "M (A \<rightarrow> B) = {}") prefer 2
   apply (rule sub_any_bot_empty) apply blast
    using fun_non_empty apply blast done
    
lemma sub_any_inter_inv[elim!]: "\<lbrakk> A <: B \<sqinter> C; \<lbrakk> A <: B ; A <: C \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding subtype_def by auto

    
lemma sub_fun_fun_inv_aux: "\<lbrakk> A\<rightarrow>B <: C \<rightarrow> D; M A \<noteq> {} \<rbrakk> \<Longrightarrow> C <: A \<and> B <: D"
  unfolding subtype_def apply simp apply (rule conjI)
   apply clarify 
   apply (case_tac "x \<in> M A") apply force
    sorry

lemma sub_fun_fun_inv[elim!]: "\<lbrakk> A\<rightarrow>B <: C \<rightarrow> D; \<lbrakk> C <: A; B <: D \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding subtype_def 
  apply (subgoal_tac "M (A\<rightarrow>B) \<noteq> {}") prefer 2 using fun_non_empty apply blast    
  sorry
    
lemma arrow_subtyping: "\<lbrakk> A\<rightarrow>B <: arrows2ty C  \<rbrakk> \<Longrightarrow> 
    \<exists> J. set J \<subseteq> set C \<and> (\<forall>Ai Bi. (Ai,Bi) \<in> set J \<longrightarrow> A <: Ai) \<and> \<Sqinter>(map snd J) <: B"
  apply (induction C)
  apply force
  apply (case_tac a) apply (rename_tac a C Ai Bi) apply simp apply clarify
  
    
    
section "Value Ordering via Subtyping"
    
function val2ty :: "val \<Rightarrow> ty" and fun2ty :: "(val \<times> val) list \<Rightarrow> ty" where
  "val2ty (VNat n) = TNat n" |
  "val2ty (VFun f) = fun2ty f" |
  "fun2ty [] = TBot" |
  "fun2ty ((v,v')#f) = (val2ty v)\<rightarrow>(val2ty v') \<sqinter> (fun2ty f)" 
  by pat_completeness auto
termination by size_change
    
definition le_val :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 60) where
  "v \<sqsubseteq> v' \<equiv> (val2ty v') <: (val2ty v)"

lemma le_refl[intro!]: "v \<sqsubseteq> v"
  unfolding le_val_def by blast
  
lemma le_trans[trans]: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  unfolding le_val_def using sub_trans by blast


  
end
