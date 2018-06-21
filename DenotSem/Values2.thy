theory Values2
imports Main
begin

datatype val = VNat nat | VFun "(val \<times> val) list" 
type_synonym entry = "val \<times> val" 
type_synonym func = "entry list"  

abbreviation make_entry :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<mapsto>" 70) where
  "v \<mapsto> v' \<equiv> VFun [(v,v')]"
abbreviation bottom_fun :: "val" ("\<bottom>" 100) where
  "bottom_fun \<equiv> VFun []"

fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = (if f1 = f2 then Some (VFun f1) else Some (VFun (f1 @ f2)))" |
  "v1 \<squnion> v2 = None"

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" |
  le_bot[intro!]: "\<bottom> \<sqsubseteq> VFun f" |
  le_app_R1[intro!]: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f2; f1 \<noteq> []; f3 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_app_R2[intro!]: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; f1 \<noteq> []; f2 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_app_L[intro!]: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3; f1 \<noteq> []; f2 \<noteq> [] \<rbrakk>
                     \<Longrightarrow> VFun (f1@f2) \<sqsubseteq> VFun f3" |
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" |
  le_distr[intro!]: "\<lbrakk> va \<squnion> vb = Some vab; v2 \<sqsubseteq> v1;  v1' \<sqsubseteq> vab;
                vab \<noteq> va; vab \<noteq> vb \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> VFun [(v2,va),(v2,vb)]" 

inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_any_bot_inv: "v \<sqsubseteq> \<bottom>" and 
  le_fun_fun_inv: "VFun f1 \<sqsubseteq> VFun f2" and
  le_arrow_arrow_inv: "v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'"

lemma le_cons_R1: assumes f1_b: "VFun f1 \<sqsubseteq> VFun [b]" and f1_ne: "f1\<noteq>[]" and f2_ne: "f2 \<noteq> []"
  shows "VFun f1 \<sqsubseteq> VFun (b#f2)" 
proof -
  have "VFun f1 \<sqsubseteq> VFun ([b]@f2)" using f1_b f1_ne f2_ne by (rule le_app_R1) 
  then show ?thesis by simp
qed

lemma le_cons_R2: assumes f1_f2: "VFun f1 \<sqsubseteq> VFun f2" and f1_ne: "f1 \<noteq> []"
  shows "VFun f1 \<sqsubseteq> VFun (b#f2)" 
proof -
  have "VFun f1 \<sqsubseteq> VFun ([b]@f2)" using f1_f2 f1_ne by (rule le_app_R2) auto
  then show ?thesis by simp
qed
    
lemma le_cons_L: assumes a_f3: "VFun [a] \<sqsubseteq> VFun f3" and f2_f3: "VFun f2 \<sqsubseteq> VFun f3"
  and f2_ne: "f2 \<noteq> []" shows "VFun (a#f2) \<sqsubseteq> VFun f3"
proof -
  have "VFun ([a]@f2) \<sqsubseteq> VFun f3" using a_f3 f2_f3 f2_ne le_app_L by blast
  then show ?thesis by simp
qed

section "Value Size"
  
function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + fsize t" |
"fsize [] = 0" |
"fsize ((v,v')#t) = vsize v + vsize v' + fsize t"
  by pat_completeness auto
termination vsize by size_change

lemma vsize_pos[simp]: "0 < vsize v"
  apply (case_tac v) apply auto done
    
lemma fsize_append[simp]: "fsize (f1@f2) = fsize f1 + fsize f2"
  apply (induction f1 arbitrary: f2)
   apply force
  apply simp apply (case_tac a) apply simp 
  done
    
lemma fsize_append_right: "f3 \<noteq> [] \<Longrightarrow> fsize f2 < fsize (f2 @ f3)"
  apply (induction f2)
  apply simp apply (case_tac f3) apply force apply force
  apply force
  done

lemma fsize_append_left: "f2 \<noteq> [] \<Longrightarrow> fsize f3 < fsize (f2 @ f3)"
  apply (induction f2) apply simp apply (case_tac f2) apply force apply force done
    
lemma size_fun_mem: "(v,v') \<in> set f \<Longrightarrow> vsize v + vsize v' \<le> fsize f"
  by (induction f) auto 
  
lemma size_fun_mem2: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; (v1,v1') \<noteq> (v2,v2') \<rbrakk>
  \<Longrightarrow> vsize v1 + vsize v1' + vsize v2 + vsize v2' \<le> fsize f"
  apply (induction f arbitrary: v1 v1' v2 v2')
   apply force
   apply simp apply (erule disjE) 
   apply (erule disjE)
    apply clarify
    apply (erule impE) apply simp apply blast
   apply clarify apply (case_tac "a = v2") apply simp
    using size_fun_mem apply force
     apply simp using size_fun_mem apply force
    apply clarify apply (erule disjE) apply clarify
    defer
    apply fastforce
  proof -
    fix a :: val and b :: val and fa :: "(val \<times> val) list" and v1a :: val and v1'a :: val and v2a :: val and v2'a :: val
    assume "(v1a, v1'a) \<in> set fa"
    then have "vsize v1a + vsize v1'a \<le> fsize fa"
      by (meson size_fun_mem)
    then show "vsize v1a + vsize v1'a + vsize a + vsize b \<le> fsize ((a, b) # fa)"
      by auto
  qed 
    
lemma vsize_join: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> vsize v12 \<le> vsize v1 + vsize v2"
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force apply (case_tac v2) apply force apply simp
   apply (case_tac "x2 = x2a") apply force apply force
  done
    

lemma size_fun_mem_join_fst: assumes v11_f: "(v1,v1') \<in> set f" and v22_f: "(v2,v2') \<in> set f"
  and v123: "v1 \<squnion> v2 = Some v3" shows "vsize v3 \<le> (fsize f)"
proof (cases "v1 = v2")
  case True
  have 1: "vsize v1 + vsize v1' \<le> fsize f" using size_fun_mem v11_f by blast
  have 2: "v3 = v1" using v123 True by (case_tac v1) auto
  show ?thesis using 1 2 by simp
next
  case False
  have 1: "vsize v1 + vsize v1' + vsize v2 + vsize v2' \<le> fsize f"
    using size_fun_mem2 False v11_f v22_f by blast
  have 2: "vsize v3 \<le> vsize v1 + vsize v2" using vsize_join v123 by blast
  show ?thesis using 1 2 by simp
qed

  
lemma size_fun_mem_join: assumes v11_f: "(v1,v1') \<in> set f" and v22_f: "(v2,v2') \<in> set f"
  and v123: "v1' \<squnion> v2' = Some v3" shows "vsize v3 \<le> (fsize f)"
proof (cases "v1' = v2'")
  case True
  have 1: "vsize v1 + vsize v1' \<le> fsize f" using size_fun_mem v11_f by blast
  have 2: "v3 = v1'" using v123 True by (case_tac v1') auto
  show ?thesis using 1 2 by simp
next
  case False
  have 1: "vsize v1 + vsize v1' + vsize v2 + vsize v2' \<le> fsize f"
    using size_fun_mem2 False v11_f v22_f by blast
  have 2: "vsize v3 \<le> vsize v1' + vsize v2'" using vsize_join v123 by blast
  show ?thesis using 1 2 by simp
qed
  
section "Reflexivity"
  
lemma nat_less_IH[elim!]: "\<lbrakk> \<forall>m<k. \<forall>x. m = S x \<longrightarrow> P x; S a < k \<rbrakk> \<Longrightarrow> P a"
 by blast
  
proposition le_refl_aux: "n = vsize v \<Longrightarrow> v \<sqsubseteq> v"
proof (induction n arbitrary: v rule: nat_less_induct)
  case (1 k)
  show ?case
  proof (cases v)
    case (VNat n)
    have "VNat n \<sqsubseteq> VNat n" by blast
    then show ?thesis using VNat by simp
  next
    case (VFun f)
    show ?thesis
    proof (cases f)
      case Nil
      have "VFun [] \<sqsubseteq> VFun []" by blast
      then show ?thesis using Nil VFun by simp
    next
      case (Cons a f')
      obtain v v' where a: "a = (v,v')" by (cases a) auto
      have 2: "v\<mapsto>v' \<sqsubseteq> v\<mapsto>v'" apply (rule le_arrow) using 1 Cons a VFun by auto
      have 3: "VFun f' \<sqsubseteq> VFun f'" using 1 Cons VFun a by auto
      have "VFun ((v,v')#f') \<sqsubseteq> VFun ((v,v')#f')"
      proof (cases "f' = []")
        case True
        then show ?thesis using 2 by simp
      next
        case False
        have 4: "v\<mapsto>v' \<sqsubseteq> VFun ((v,v')#f')" using 2 apply (rule le_cons_R1) using False by auto
        have 5: "VFun f' \<sqsubseteq> VFun ((v,v')#f')" using 3 apply (rule le_cons_R2) using False by simp
        show ?thesis using 4 5 apply (rule le_cons_L) using False by simp
      qed
      then show ?thesis using Cons VFun a by simp
    qed
  qed
qed

proposition le_refl[intro!]: "v \<sqsubseteq> v"
  using le_refl_aux by blast

section "Inversion Lemmas"
  
lemma le_bot_inv_aux: fixes v1::val and f1::func
  assumes v12: "v1 \<sqsubseteq> v2" and v2b: "v2 = \<bottom>" shows "v1 = \<bottom>"
  using v12 v2b by (induction rule: val_le.induct) auto
      
lemma le_bot_inv[elim!]: "\<lbrakk> f \<sqsubseteq> \<bottom>; f = \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_bot_inv_aux by auto      
    
lemma le_any_nat_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v' = VNat n\<rbrakk> \<Longrightarrow> v = VNat n"
  by (induction rule: val_le.induct) auto
    
proposition le_any_nat_inv[elim!]: "\<lbrakk> v \<sqsubseteq> VNat n; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_any_nat_inv_aux[of v "VNat n" n] by auto
  
lemma le_nat_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VNat n\<rbrakk> \<Longrightarrow> v' = VNat n"
  by (induction arbitrary: n rule: val_le.induct) auto
    
proposition le_nat_any_inv[elim!]: "\<lbrakk> VNat n \<sqsubseteq> v; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_nat_any_inv_aux[of "VNat n" v n] by auto    

lemma le_fun_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VFun f \<rbrakk> \<Longrightarrow> \<exists> f'. v' = VFun f'"
  by (induction arbitrary: f rule: val_le.induct) auto
  
proposition le_fun_any_inv: "\<lbrakk> VFun f \<sqsubseteq> v; \<And>f'. v = VFun f' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_fun_any_inv_aux by blast
    
section "Generalized Introduction Rules"

lemma le_fun_elt: assumes v12: "v1\<mapsto>v1' \<sqsubseteq> v2\<mapsto>v2'" and v2f: "(v2,v2') \<in> set f2"
  shows "v1\<mapsto>v1' \<sqsubseteq> VFun f2" using v12 v2f
proof (induction f2)
  case Nil
  then have "False" by simp
  then show ?case ..
next
  case (Cons a f2)
  obtain v v' where a: "a = (v,v')" by (cases a) auto
  have "(v2,v2') = (v,v') \<or> (v2,v2') \<in> set f2" using Cons a by auto 
  then show ?case
  proof
    assume v2v: "(v2,v2') = (v,v')"
    show ?thesis sorry
  next
    assume v2f2: "(v2,v2') \<in> set f2"
    show ?thesis sorry
  qed
qed  

  
lemma le_fun_subset: fixes f1::func and f2::func 
  assumes ae: "\<forall> v1 v1'. (v1,v1') \<in> set f1 \<Longrightarrow> \<exists> v2 v2'. (v2,v2') \<in> set f2"
  shows "VFun f1 \<sqsubseteq> VFun f2"
proof (induction f1)
  case Nil
  show "\<bottom> \<sqsubseteq> VFun f2" by blast
next
  case (Cons a f1')
  obtain v v' where a: "a = (v,v')" by (cases a) auto
  
  show ?case sorry
qed  
    
    
end