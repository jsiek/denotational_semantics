theory Values
  imports Main IntersectionTypes
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
  fun_le_inv: "k \<turnstile> (f1::func) \<sqsubseteq> f2" and
  nat_fun_le_inv[elim!]: "k \<turnstile> VNat n \<sqsubseteq> VFun f" and
  fun_nat_le_inv[elim!]: "k \<turnstile> VFun f \<sqsubseteq> VNat n"
    
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

lemma weaken: "c \<turnstile> f1 \<sqsubseteq> f2@f3 \<Longrightarrow> (\<exists>c'. c' \<turnstile> f1 \<sqsubseteq> f2@f@f3)"
  apply (induction f arbitrary: c f1 f2 f3)
   apply force
  apply (subgoal_tac "\<exists>c'. c' \<turnstile> f1 \<sqsubseteq> f2 @ (f @ f3)") prefer 2 apply force
  apply clarify
  apply (subgoal_tac "Suc c' \<turnstile> f1 \<sqsubseteq> f2 @ (a, b) # (f @ f3)")
    prefer 2 apply (rule wk_fun) apply blast
  apply auto
  done
    
thm val.induct
    
lemma fun_cons_le:
  fixes v1::val and v1'::val and f1::func 
  assumes v21: "k \<turnstile> v2 \<sqsubseteq> v1" and v12: "k \<turnstile> v1' \<sqsubseteq> v2'" and f12: "k \<turnstile> f1 \<sqsubseteq> f2"
  shows "k \<turnstile> (v1,v1')#f1 \<sqsubseteq> (v2,v2')#f2"
  sorry
    
(* todo:
lemma ax 
 
*)
lemma ax_fun: fixes f::func
  assumes IH: "\<forall>v v'. (v,v') \<in> set f \<longrightarrow> (\<exists>k. k \<turnstile> v \<sqsubseteq> v) \<and> (\<exists>k. k \<turnstile> v' \<sqsubseteq> v')"
  shows "\<exists>k. k \<turnstile> f \<sqsubseteq> f" using IH
proof (induction f)
  case Nil
  then show ?case by blast
next
  case (Cons a f)
  obtain k where ff: "k \<turnstile> f \<sqsubseteq> f" using Cons by auto
  obtain v v' where a: "a = (v,v')" by (cases a) auto
  obtain k1 where 1: "k1 \<turnstile> v \<sqsubseteq> v" using Cons(2) a by auto
  obtain k2 where 2: "k2 \<turnstile> v' \<sqsubseteq> v'" using Cons(2) a by auto
  let ?k = "max k (max k1 k2)"
  have "k \<le> ?k" by auto
  then have 3: "?k \<turnstile> f \<sqsubseteq> f" using ff weaken_size by blast    
  have "k1 \<le> ?k" by auto
  then have 4: "?k \<turnstile> v \<sqsubseteq> v" using 1 weaken_size by blast
  
      
  show ?case sorry
qed
  
  
lemma ax: fixes v::val shows "\<exists>k. k \<turnstile> v \<sqsubseteq> v"
proof (induction v)
  case (VNat x)
  then show ?case by blast
next
  case (VFun f)
  have IH: "\<forall>v v'. (v,v') \<in> set f \<longrightarrow> (\<exists>k. k \<turnstile> v \<sqsubseteq> v) \<and> (\<exists>k. k \<turnstile> v' \<sqsubseteq> v')"
    using VFun by auto
  
  have "k \<turnstile> f \<sqsubseteq> f" sorry  
  then show "\<exists>k. k \<turnstile> VFun f \<sqsubseteq> VFun f" by blast
qed
   
  
(*
function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
  "vsize (VNat n) = 1" |
  "vsize (VFun t) = Suc (fsize t)" |
  "fsize [] = 0" |
  "fsize ((v,v')#f) = Suc (vsize v + vsize v' + fsize f)"
  by pat_completeness auto
  termination by size_change
*)
 
fun inter :: "ty list \<Rightarrow> ty" where
  "inter [] = \<top>" |
  "inter (A#AS) = A \<sqinter> inter AS"  

function val2ty :: "val \<Rightarrow> ty" and fun2tys :: "func \<Rightarrow> ty list" where
  "val2ty (VNat n) = TNat n" |
  "val2ty (VFun f) = inter (fun2tys f)" |
  "fun2tys [] = []" |
  "fun2tys ((v,v')#f) = ((val2ty v) \<rightarrow> (val2ty v')) # fun2tys f"
  by pat_completeness auto
  termination by size_change

lemma val_le_sound: fixes v::val and v'::val and f::func and f'::func 
  shows 
  "(k1 \<turnstile> v \<sqsubseteq> v' \<longrightarrow> (\<exists>c. [val2ty v] \<turnstile> c : val2ty v'))
    \<and> (k2 \<turnstile> f \<sqsubseteq> f' \<longrightarrow> (\<forall>v v'. (v,v') \<in> set f' \<longrightarrow> 
            (\<exists>c. fun2tys f \<turnstile> c : (val2ty v) \<rightarrow> (val2ty v'))))"
  apply (induction rule: val_le_fun_le.induct)
       apply force
  sorry    
  
end