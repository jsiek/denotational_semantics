theory Values
  imports Main
begin

section "Values"

datatype val = VNat nat | VFun "(val \<times> val) list"
  
type_synonym func = "(val \<times> val) list" 
  
fun join_val :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 80) where
  "(VNat n1) \<squnion> (VNat n2) = (if n1 = n2 then Some (VNat n1) else None)" |
  "(VFun f1) \<squnion> (VFun f2) = Some (VFun (f1@f2))"
  
fun join_val_list :: "val list \<Rightarrow> val option" ("\<Squnion>" 1000) where
  "join_val_list [] = None" |
  "join_val_list (v#vs) = (case \<Squnion>vs of None \<Rightarrow> None | Some v' \<Rightarrow> v \<squnion> v')" 

inductive val_le :: "nat \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _ \<sqsubseteq> _" [55,55,55] 56) and
  fun_le :: "nat \<Rightarrow> func \<Rightarrow> func \<Rightarrow> bool" ("_ \<turnstile> _ \<sqsubseteq> _" [55,55,55] 56) where
  le_vnat[intro!]: "k \<turnstile> VNat n \<sqsubseteq> VNat n" |
  le_vfun[intro!]: "k \<turnstile> f1 \<sqsubseteq> f2 \<Longrightarrow> Suc k \<turnstile> VFun f1 \<sqsubseteq> VFun f2" |
  em_fun[intro!]: "k \<turnstile> [] \<sqsubseteq> f2" | 
  wk_fun: "k \<turnstile> f1 \<sqsubseteq> f21 @ f22  \<Longrightarrow> Suc k \<turnstile> f1 \<sqsubseteq> f21 @ (v,v') # f22" |
  app_R: "\<lbrakk> k \<turnstile>  f1 \<sqsubseteq> f3; k \<turnstile> f2 \<sqsubseteq> f3  \<rbrakk> \<Longrightarrow> Suc k \<turnstile> f1 @ f2 \<sqsubseteq> f3" |
  arrow_le: "\<lbrakk> \<Squnion>(map fst f1) = Some ds1; \<Squnion>(map fst f2) = Some ds2; 
               \<Squnion>(map snd f1) = Some cs1; \<Squnion>(map snd f2) = Some cs2;
               k \<turnstile> ds2 \<sqsubseteq> ds1; k \<turnstile> cs1 \<sqsubseteq> cs2 \<rbrakk> \<Longrightarrow> Suc k \<turnstile> f1 \<sqsubseteq> f2"

inductive_cases val_le_0[elim!]: "0 \<turnstile> (v1::val) \<sqsubseteq> v2" and
  fun_le_0[elim!]: "0 \<turnstile> (f1::func) \<sqsubseteq> f2" and
  val_le_inv: "k \<turnstile> (v1::val) \<sqsubseteq> v2" and
  vfun_le_inv[elim!]: "k \<turnstile> VFun f1 \<sqsubseteq> VFun f2" and
  fun_le_inv: "k \<turnstile> (f1::func) \<sqsubseteq> f2"
    
lemma weaken_size:  
  "(\<forall> v1 v2. k \<turnstile> (v1::val) \<sqsubseteq> v2 \<longrightarrow> (\<forall>k'. k \<le> k' \<longrightarrow> k' \<turnstile> v1 \<sqsubseteq> v2)) \<and>
   (\<forall> f1 f2. k \<turnstile> (f1::func) \<sqsubseteq> f2 \<longrightarrow> (\<forall>k'. k \<le> k' \<longrightarrow> k' \<turnstile> f1 \<sqsubseteq> f2))"
  apply (induction k)
   apply blast
  apply (rule conjI)
   apply clarify apply (erule val_le_inv) apply blast
   apply (case_tac k') apply force apply blast
  apply clarify apply (case_tac k') apply force apply clarify
  apply (erule fun_le_inv) apply blast
    apply simp apply (rule wk_fun) apply force
    apply simp apply (rule app_R) apply force apply force
  apply (rule arrow_le) apply blast+
  done

    
(*
function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
  "vsize (VNat n) = 1" |
  "vsize (VFun t) = Suc (fsize t)" |
  "fsize [] = 0" |
  "fsize ((v,v')#f) = Suc (vsize v + vsize v' + fsize f)"
  by pat_completeness auto
  termination by size_change
*)
(*  
function val2ty :: "val \<Rightarrow> ty" and fun2ty :: "func \<Rightarrow> ty" where
  "val2ty (VNat n) = TNat n" |
  "val2ty (VFun f) = fun2ty f" |
  "fun2ty [] = undefined" |
  "fun2ty ((v,v')#f) = ((val2ty v) \<rightarrow> (val2ty v')) \<sqinter> fun2ty f"
  by pat_completeness auto
  termination by size_change
 *)
  
  
end