theory Values
imports Main "~~/src/HOL/Library/FSet" 
begin

datatype val = VNat nat | VFun "(val \<times> val) fset"

fun val_join :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then VNat n1 else undefined)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = (VFun (f1 |\<union>| f2))" |
  "v1 \<squnion> v2 = undefined" 

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) and
    fun_le :: "(val \<times> val) fset \<Rightarrow> (val \<times> val) fset \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) and
    fun_in :: "val \<times> val \<Rightarrow> (val \<times> val) fset \<Rightarrow> bool" ("_ in _" [56,56] 55)
    where
  vnat_le[intro!]: "(VNat n) \<sqsubseteq> (VNat n)" |
  vfun_le[intro!]: "t1 \<sqsubseteq> t2 \<Longrightarrow> (VFun t1) \<sqsubseteq> (VFun t2)" |
  empty_le[intro!]: "{||} \<sqsubseteq> t2" |
  ins_le[intro!]: "\<lbrakk> p in t2; t1 \<sqsubseteq> t2 \<rbrakk> \<Longrightarrow> finsert p t1 \<sqsubseteq> t2" |
  fun_in_ax[intro!]: "p |\<in>| t \<Longrightarrow> p in t" |
  fun_in_sub: "\<lbrakk> (v1,v1') in t; v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> (v2,v2') in t" | 
  fun_in_union: "\<lbrakk> (v1,v1') in t; (v2,v2') in t; v \<sqsubseteq> v1 \<squnion> v2; v1' \<squnion> v2' \<sqsubseteq> v' \<rbrakk>
                   \<Longrightarrow> (v,v') in t"
inductive_cases 
  le_fun_fun_inv[elim!]: "VFun t1 \<sqsubseteq> VFun t2" and
  le_fun_nat_inv[elim!]: "VFun t2 \<sqsubseteq> VNat x1" and
  le_any_nat_inv[elim!]: "v \<sqsubseteq> VNat n" and
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v" and
  le_fun_any_inv[elim!]: "VFun t \<sqsubseteq> v" and
  le_any_fun_inv[elim!]: "v \<sqsubseteq> VFun t" and
  le_ins_fun_inv[elim!]: "finsert (a, b) t1 \<sqsubseteq> t2"
  
section "Size of Values"  
  
fun vadd :: "(val \<times> nat) \<times> (val \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "vadd ((_,v),(_,u)) r = v + u + r"
  
primrec vsize :: "val \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + ffold vadd 0
                            (fimage (map_prod (\<lambda> v. (v,vsize v)) (\<lambda> v. (v,vsize v))) t)"

abbreviation vprod_size :: "val \<times> val \<Rightarrow> (val \<times> nat) \<times> (val \<times> nat)" where
  "vprod_size \<equiv> map_prod (\<lambda> v. (v,vsize v)) (\<lambda> v. (v,vsize v))"

abbreviation fsize :: "(val \<times> val) fset \<Rightarrow> nat" where
  "fsize t \<equiv> 1 + ffold vadd 0 (fimage vprod_size t)"

abbreviation psize :: "val \<times> val \<Rightarrow> nat" where
  "psize \<equiv> \<lambda> (v1, v2). vsize v1 + vsize v2"
  
interpretation vadd_vprod: comp_fun_commute "vadd \<circ> vprod_size"
  unfolding comp_fun_commute_def by auto  

lemma vprod_size_inj: "inj_on vprod_size (fset A)"
  unfolding inj_on_def by auto
  
lemma fsize_def2: "fsize t = 1 + ffold (vadd \<circ> vprod_size) 0 t"
  using vprod_size_inj[of t] ffold_fimage[of vprod_size t vadd 0] by simp
    
lemma fsize_finsert_in[simp]:
  assumes v12_t: "(v1,v2) |\<in>| t" shows "fsize (finsert (v1,v2) t) = fsize t"
proof -
  from v12_t have "finsert (v1,v2) t = t" by auto 
  from this show ?thesis by simp
qed
 
lemma fsize_finsert_notin[simp]: 
  assumes v12_t: "(v1,v2) |\<notin>| t"
  shows "fsize (finsert (v1,v2) t) = vsize v1 + vsize v2 + fsize t"
proof -
  let ?f = "vadd \<circ> vprod_size"
  have "fsize (finsert (v1,v2) t) = 1 + ffold ?f 0 (finsert (v1,v2) t)"
    using fsize_def2[of "finsert (v1,v2) t"] by simp
  also from v12_t have "... = 1 + ?f (v1,v2) (ffold ?f 0 t)" by auto
  finally have "fsize (finsert (v1,v2) t) = 1 + ?f (v1,v2) (ffold ?f 0 t)" .
  from this show ?thesis using fsize_def2[of t] by simp
qed

lemma val_size_mem: assumes v12_t: "(v1,v2) |\<in>| t" shows "vsize v1 + vsize v2 < fsize t"
  using v12_t apply (induction t arbitrary: v1 v2)
   apply force
  apply (subgoal_tac "x |\<notin>| t") prefer 2 apply force 
  apply (case_tac x)
  apply (subgoal_tac "fsize (finsert (a,b) t) = vsize a + vsize b + fsize t")
   prefer 2 apply (rule fsize_finsert_notin) apply force
  apply force 
  done
    
lemma val_size_mem_l: assumes v12_t: "(v1,v2) |\<in>| t" shows "vsize v1 < fsize t"
  using v12_t val_size_mem[of v1 v2 t] by arith 

lemma val_size_mem_r: assumes v12_t: "(v1,v2) |\<in>| t" shows "vsize v2 < fsize t"
  using v12_t val_size_mem[of v1 v2 t] by arith

lemma psize_mem: assumes p_t: "p |\<in>| t" shows "psize p < fsize t"
  using p_t val_size_mem apply (case_tac p) apply simp done
    
section "Joins and Meets"
  
abbreviation val_lub :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "val_lub v v1 v2 \<equiv> v1 \<sqsubseteq> v \<and> v2 \<sqsubseteq> v \<and> (\<forall> v'. v1 \<sqsubseteq> v' \<and> v2 \<sqsubseteq> v' \<longrightarrow> v \<sqsubseteq> v')"

abbreviation val_glb :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "val_glb v v1 v2 \<equiv> v \<sqsubseteq> v1 \<and> v \<sqsubseteq> v2 \<and> (\<forall> v'. v' \<sqsubseteq> v1 \<and> v' \<sqsubseteq> v2 \<longrightarrow> v' \<sqsubseteq> v)"

lemma fun_le_union1: "t1 \<sqsubseteq> t1 |\<union>| t2"
  apply (induction t1 arbitrary: t2)
   apply force
  apply clarify
  apply (rule ins_le) apply force
  apply (subgoal_tac "t1 \<sqsubseteq> t1 |\<union>| finsert (a,b) t2") prefer 2 apply blast
  apply force
  done
  
lemma fun_le_union2: "t1 \<sqsubseteq> t2 |\<union>| t1"
  apply (induction t1 arbitrary: t2)
   apply force
  apply clarify
  apply (rule ins_le) apply force
  apply (subgoal_tac "t1 \<sqsubseteq> finsert (a,b) t2 |\<union>| t1") prefer 2 apply blast
  apply force
  done
    
lemma fun_union_le: fixes t1::"(val \<times> val) fset" and t1'::"(val \<times> val) fset"
  assumes t1_t2: "t1 \<sqsubseteq> t2" and t1p_t2: "t1' \<sqsubseteq> t2" shows "t1 |\<union>| t1' \<sqsubseteq> t2"    
  using t1_t2 t1p_t2 apply (induction t1 arbitrary: t1' t2)
   apply force
  apply simp apply clarify apply (rule ins_le) defer
    
    
    
lemma join_lub: fixes v1::val and v2::val 
  assumes n: "n = vsize v1 + vsize v2" 
  and ub1: "v1 \<sqsubseteq> v" and ub2: "v2 \<sqsubseteq> v"
  shows "val_lub (v1 \<squnion> v2) v1 v2"
  using n ub1 ub2 apply (induction n arbitrary: v1 v2 v rule: nat_less_induct)
  apply (case_tac v1)
   apply (case_tac v2) apply force apply force
  apply (case_tac v2) apply force
  apply clarify apply (rule conjI) apply (simp only: vfun_join)
   apply clarify apply (rule fun_le_union1)
  apply (rule conjI) apply (simp only: vfun_join)
   apply clarify apply (rule fun_le_union2)
  apply clarify apply (simp only: vfun_join)
  apply clarify
    
    
    
end