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

fun join_list :: "val list \<Rightarrow> val option" ("\<Squnion>") where
  "\<Squnion> [] = None" |
  "\<Squnion> [v] = Some v" |
  "\<Squnion> (v#ls) = (case \<Squnion>ls of
                None \<Rightarrow> None
              | Some v' \<Rightarrow> v \<squnion> v')"

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" |
  le_bot[intro!]: "\<bottom> \<sqsubseteq> VFun f" |
  le_app_R1[intro!]: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f2; f1 \<noteq> []; f3 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_app_R2[intro!]: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; f1 \<noteq> []; f2 \<noteq> [] \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun (f2@f3)" |
  le_app_L[intro!]: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3; f1 \<noteq> []; f2 \<noteq> [] \<rbrakk>
                     \<Longrightarrow> VFun (f1@f2) \<sqsubseteq> VFun f3" |
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" |
(*  le_distr[intro!]: "\<lbrakk> va \<squnion> vb = Some vab; v2 \<sqsubseteq> v1;  v1' \<sqsubseteq> vab;
                vab \<noteq> va; vab \<noteq> vb \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> VFun [(v2,va),(v2,vb)]" 
*)
  le_distr[intro!]: "\<lbrakk> va \<squnion> vb = Some vab; v1\<mapsto>va \<sqsubseteq> VFun f2; v1\<mapsto>vb \<sqsubseteq> VFun f2 \<rbrakk>
                     \<Longrightarrow> v1\<mapsto>vab \<sqsubseteq> VFun f2"

inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_any_bot_inv: "v \<sqsubseteq> \<bottom>" and 
  le_fun_fun_inv: "VFun f1 \<sqsubseteq> VFun f2" and
  le_arrow_arrow_inv: "v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" and
  le_fun_arrow_inv: "VFun f1 \<sqsubseteq> v2 \<mapsto> v2'" and
  le_arrow_fun_inv: "v1 \<mapsto> v1' \<sqsubseteq> VFun f2"
  
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

section "Value Size and Induction"
  
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

lemma non_empty_pos_fsize[intro!]: "f \<noteq> [] \<Longrightarrow> 0 < fsize f"
    by (case_tac f) auto

lemma nat_less_IH[elim!]: "\<lbrakk> \<forall>m<k. \<forall>x. m = S x \<longrightarrow> P x; S a < k \<rbrakk> \<Longrightarrow> P a"
 by blast

lemma nat_less_IH3[elim!]: "\<lbrakk> \<forall>m<k. \<forall>x y z. m = S x y z \<longrightarrow> P x y z; S a b c < k \<rbrakk> \<Longrightarrow> P a b c"
  by blast
   

section "Reflexivity"  
  
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

section "Introduction Rules for Join"
    
proposition le_join_left: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v1 \<sqsubseteq> v12" (* incl_L *)
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force
  apply (case_tac v2) apply force
  apply simp
  apply (case_tac "x2 = x2a") apply force 
  apply simp
  apply clarify
    apply (case_tac x2a) apply simp apply blast
  apply (case_tac x2) apply simp apply blast
  apply (rule le_app_R1) apply blast apply blast apply blast
  done

proposition le_join_right: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v2 \<sqsubseteq> v12" (* incl_R *) 
    apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force
  apply (case_tac v2) apply force
  apply simp
  apply (case_tac "x2 = x2a") apply force
  apply simp
  apply clarify
  apply (case_tac x2)
   apply force
    apply (case_tac x2a) apply force
   apply (rule le_app_R2) apply auto
  done

proposition le_left_join: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" (* glb *)
  apply (case_tac v1) apply (case_tac v2) apply simp
  apply (case_tac "x1 = x1a") apply force apply force
  apply force
  apply (case_tac v2) apply force
  apply simp
  apply (case_tac "x2 = x2a") apply force
  apply simp
  apply clarify
  apply (case_tac v3) apply simp 
   apply force
  apply clarify
  apply (case_tac x2) apply force
  apply (case_tac x2a) apply force
  apply (rule le_app_L)
     apply force
    apply force
  apply blast
  apply blast
  done
    
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

lemma le_arrow_inv_aux: "\<lbrakk> v1 \<sqsubseteq> v2; v1 = v1a \<mapsto> v1b; v2 = v2a \<mapsto> v2b \<rbrakk> \<Longrightarrow> v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v2b"
proof (induction v1 v2 arbitrary: v1a v1b v2a v2b rule: val_le.induct)
  case (le_nat n)
  then show ?case by auto
next
  case (le_bot f)
  then show ?case by auto
next
  case (le_app_R1 f1 f2 f3)
  then show ?case by (case_tac f2) auto
next
  case (le_app_R2 f1 f3 f2)
  then show ?case by (case_tac f2) auto
next
  case (le_app_L f1 f3 f2)
  then show ?case apply (case_tac f1) apply force apply (case_tac f2) apply auto done
next
  case (le_arrow v2 v1 v1' v2')
  have "v2 \<sqsubseteq> v1 \<and> v1' \<sqsubseteq> v2'" using le_arrow by blast
  then show "v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v2b" using le_arrow by simp
next
  case (le_distr va vb vab v1 f2 v1a v1b v2a v2b)
  have 1: "v2a \<sqsubseteq> v1a" using le_distr by auto
  have 2: "va \<sqsubseteq> v2b" using le_distr by auto
  have 3: "vb \<sqsubseteq> v2b" using le_distr by auto
  have 4: "v1b \<sqsubseteq> v2b" using 2 3 le_distr(1) le_distr(6)
    by (metis Pair_inject le_left_join list.inject val.inject(2))    
  show "v2a \<sqsubseteq> v1a \<and> v1b \<sqsubseteq> v2b" using 1 4 by blast
qed
    
lemma le_arrow_inv[elim!]: "\<lbrakk> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'; \<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_arrow_inv_aux by blast 
    
section "More Introduction Rules"

lemma le_fun_elt: assumes v12: "v1\<mapsto>v1' \<sqsubseteq> v2\<mapsto>v2'" and v2f: "(v2,v2') \<in> set f2"
  shows "v1\<mapsto>v1' \<sqsubseteq> VFun f2" using v12 v2f
proof (induction f2)
  case Nil
  then have "False" by simp
  then show ?case ..
next
  case (Cons a f2)
  obtain v v' where a: "a = (v,v')" by (cases a) auto
  show ?case
  proof (cases f2)
    case Nil
    then show ?thesis using Cons a by auto
  next
    case (Cons b f2')
    have "(v2,v2') = (v,v') \<or> (v2,v2') \<in> set f2" using a using Cons.prems(2) by auto
    then show ?thesis
    proof
      assume "(v2,v2') = (v,v')"
      then have "v1 \<mapsto> v1' \<sqsubseteq> v \<mapsto> v'" using v12 by auto
      then show ?thesis using a Cons apply simp apply (rule le_cons_R1) by auto
    next
      assume "(v2,v2') \<in> set f2"
      then have "v1 \<mapsto> v1' \<sqsubseteq> VFun f2" using Cons.IH v12 by auto
      then show ?thesis by (rule le_cons_R2) simp
    qed
  qed   
qed
  
lemma le_fun_subset: fixes f1::func and f2::func 
  assumes ae: "\<forall> v1 v1'. (v1,v1') \<in> set f1 \<longrightarrow> (\<exists> v2 v2'. (v2,v2') \<in> set f2 \<and> v1\<mapsto>v1'\<sqsubseteq>v2\<mapsto>v2')"
  shows "VFun f1 \<sqsubseteq> VFun f2" using ae
proof (induction f1)
  case Nil
  show "\<bottom> \<sqsubseteq> VFun f2" by blast
next
  case (Cons a f1')
  obtain v1 v1' where a: "a = (v1,v1')" by (cases a) auto
  have v11_f1: "(v1,v1') \<in> set (a#f1')" using a by simp
  obtain v2 v2' where v22_f2: "(v2,v2') \<in> set f2" and v11_v22: "v1\<mapsto>v1'\<sqsubseteq>v2\<mapsto>v2'"
    using v11_f1 Cons(2) by blast
  have 1: "v1\<mapsto>v1' \<sqsubseteq> VFun f2" using v11_v22 v22_f2 by (rule le_fun_elt)
  have 2: "VFun f1' \<sqsubseteq> VFun f2" by (simp add: Cons.IH Cons.prems)
  show ?case
  proof (cases f1')
    case Nil
    then show ?thesis using a 1 by auto
  next
    case (Cons a list)
    then show ?thesis using 1 2 a apply simp apply (rule le_cons_L) by auto
  qed
qed  

lemma le_fun_subset_eq: fixes f1::func and f2::func 
  assumes f1_f2: "set f1 \<subseteq> set f2" shows "VFun f1 \<sqsubseteq> VFun f2"
proof -
  have ae: "\<forall> v1 v1'. (v1,v1') \<in> set f1 \<longrightarrow> (\<exists> v2 v2'. (v2,v2') \<in> set f2 \<and> v1\<mapsto>v1'\<sqsubseteq>v2\<mapsto>v2')"
    using f1_f2 le_refl apply auto done
  then show ?thesis using le_fun_subset by blast
qed
  
proposition le_distr_trad1: fixes v1::val assumes v12: "v1 \<squnion> v2 = Some v12" 
  shows "v \<mapsto> v12 \<sqsubseteq> VFun [(v,v1),(v,v2)]"
  using v12 by (metis Values2.le_refl le_cons_R1 le_cons_R2 le_distr not_Cons_self)
    
proposition le_distr_trad2: fixes v1::val assumes v12: "v1 \<squnion> v2 = Some v12" 
  shows "VFun [(v,v1),(v,v2)] \<sqsubseteq> v \<mapsto> v12"
  using v12 by (metis Values2.le_refl le_arrow le_cons_L le_join_left le_join_right)

proposition mon: fixes v1::val and v2::val and v1'::val and v2'::val and v12::val 
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'" and
    v12: "v1 \<squnion> v2 = Some v12" and v12p: "v1' \<squnion> v2' = Some v12'"
  shows "v12 \<sqsubseteq> v12'"
  using 1 2 v12 v12p
  apply (case_tac v1) apply (case_tac v2) apply force apply force apply (case_tac v2)
   apply force apply simp
  apply (case_tac "x2=x2a") apply simp apply clarify 
   apply (case_tac v1') apply force apply (case_tac v2') apply force    
   apply simp apply (case_tac "x2b=x2c") apply force apply simp
   apply (case_tac v12') apply force apply simp
   apply clarify apply (metis le_app_R1 le_app_R2 val_le.le_bot)
  apply simp apply (case_tac v1') apply force apply (case_tac v2') apply force
  apply (case_tac v12') apply simp apply (case_tac "x2b=x2c") apply force
   apply force apply simp apply clarify
  apply (case_tac "x2b=x2c") apply simp
  apply (meson Values2.vfun_join le_left_join)
  apply simp apply clarify 
  by (metis (no_types, lifting) append_Nil2 le_app_L le_app_R1 le_app_R2 self_append_conv2)    

lemma upper_bound_join: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> \<exists> v12. v1 \<squnion> v2 = Some v12"
  apply (case_tac v1) apply (case_tac v2) apply auto apply (case_tac v2) by auto

lemma upper_bound_join_list: "\<lbrakk> (\<forall> v. v \<in> set L \<longrightarrow> v \<sqsubseteq> u); L \<noteq> [] \<rbrakk> \<Longrightarrow>
    \<exists>vj. \<Squnion>L = Some vj \<and> vj \<sqsubseteq> u"
  apply (induction L)
  apply force
  apply (case_tac L)
   apply force
   apply simp apply clarify apply simp 
  apply (erule_tac x=a in allE) apply clarify apply simp
    apply (subgoal_tac "\<exists>vja. a \<squnion> vj = Some vja") prefer 2 apply (rule upper_bound_join)
    apply assumption apply assumption apply (erule exE)
  apply (rule_tac x=vja in exI) apply simp
  using le_left_join by blast
    
section "More Lemmas"
    
lemma append_len_geq: "f @ f' = list @ list' \<Longrightarrow> \<not> length f < length list \<Longrightarrow> \<exists>l'. f = list @ l'"
  apply (induction f arbitrary: f' list list')
  apply force
  apply simp
  apply (case_tac list)
    apply auto
  done

lemma le_left_append_elim_aux: "\<lbrakk> n = fsize f1 + fsize f2 + fsize f3; VFun (f1@f2) \<sqsubseteq> VFun f3 \<rbrakk>
  \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3"
proof (induction n arbitrary: f1 f2 f3 rule: nat_less_induct)
  case (1 n)
  show ?case
  proof (cases f1)
    case Nil
    then show ?thesis using 1(3) by auto
  next
    case (Cons a f1') 
    then obtain v v' where a: "a = (v,v')" by (cases a) auto
    then have f1: "f1 = (v,v')#f1'" using Cons by simp
    show ?thesis using 1(3)
    proof (rule le_fun_fun_inv)
      assume "f1 @ f2 = []"
      then show "VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3" by auto
    next
      fix f31 f32 assume f3: "f3 = f31 @ f32" and f12_f2: "VFun (f1 @ f2) \<sqsubseteq> VFun f31"
        and f12_ne: "f1 @ f2 \<noteq> []" and f32_ne: "f32 \<noteq> []"
      have "fsize f1 + fsize f2 + fsize f31 < n" using 1(2) f3 f32_ne by auto
      then have "VFun f1 \<sqsubseteq> VFun f31 \<and> VFun f2 \<sqsubseteq> VFun f31" using 1(1) f12_f2 by blast
      then show "VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3"
        by (metis f3 f32_ne le_app_R1 val_le.le_bot) 
    next
      fix f31 f32 assume f3: "f3 = f31@f32" and f12_f32: "VFun (f1 @ f2) \<sqsubseteq> VFun f32"
        and f12_ne: "f1@f2 \<noteq> []" and f31_ne: "f31 \<noteq> []"
      have "fsize f1 + fsize f2 + fsize f32 < n" using 1(2) f3 f31_ne by auto
      then have "VFun f1 \<sqsubseteq> VFun f32 \<and> VFun f2 \<sqsubseteq> VFun f32" using 1(1) f12_f32 by blast
      then show "VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3"
        by (metis f3 f31_ne le_app_R2 val_le.le_bot)
    next
      fix fa fb assume f12_ab: "f1 @ f2 = fa @ fb" and a3: "VFun fa \<sqsubseteq> VFun f3" 
        and b3: "VFun fb \<sqsubseteq> VFun f3" and a_ne: "fa \<noteq> []" and b_ne: "fb \<noteq> []" 
      obtain fa' where fa: "fa = (v,v')#fa'" using f1 f12_ab a_ne
         apply (case_tac fa) apply auto done
      show "VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3" 
      proof (cases "length f1' < length fa'")
        case True
          
        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry
      qed
    next
      show "VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3" sorry
    next
      show "VFun f1 \<sqsubseteq> VFun f3 \<and> VFun f2 \<sqsubseteq> VFun f3" sorry
    qed      
  qed
qed
    
    
lemma le_left_append_elim: "\<lbrakk> VFun (f1@f2) \<sqsubseteq> VFun f3;
   \<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  sorry
  
lemma le_app_app:
  assumes f2: "f2 = f2a@f2b" and f2_cd: "f2 = f2c @ f2d" and
    f2a_ne: "f2a \<noteq> []" and f2b_ne: "f2b \<noteq> []" and
    f2a_f3: "VFun f2a \<sqsubseteq> VFun f3" and f2b_f3: "VFun f2b \<sqsubseteq> VFun f3" and
    IH: "VFun (f2c' @ f2d) \<sqsubseteq> VFun f3 \<longrightarrow> VFun f2c' \<sqsubseteq> VFun f3 \<and> VFun f2d \<sqsubseteq> VFun f3"
  shows "VFun f2c \<sqsubseteq> VFun f3 \<and> VFun f2d \<sqsubseteq> VFun f3"
proof (cases "length f2a < length f2c")
  case True
  obtain f2c' where f2c: "f2c = f2a @ f2c'" using f2 f2_cd 
    by (metis True add_lessD1 append_len_geq less_imp_add_positive less_not_refl2)
  have f2cp_ne: "f2c' \<noteq> []" using f2c f2 f2_cd True by auto
  have f2b: "f2b = f2c' @ f2d" using f2c f2 f2_cd by auto
  have f2cp_f3: "VFun f2c' \<sqsubseteq> VFun f3 \<and> VFun f2d \<sqsubseteq> VFun f3" 
    using f2b f2b_f3 IH le_left_append_elim by auto 
  have f2c_f3: "VFun f2c \<sqsubseteq> VFun f3" using f2a_f3 f2cp_f3 f2c f2a_ne f2cp_ne 
    apply simp apply (rule le_app_L) by auto
  show ?thesis using f2cp_f3 f2c_f3 by blast
next
  case False
  obtain f2a' where f2a: "f2a = f2c @ f2a'" using f2 f2_cd False using append_len_geq by blast
  have f2c_f3: "VFun f2c \<sqsubseteq> VFun f3" using f2a_f3 f2a le_left_append_elim by auto
  have f2d: "f2d = f2a' @ f2b" using f2a f2 f2_cd by simp
  have f2a_f3: "VFun f2a' \<sqsubseteq> VFun f3" using f2a_f3 f2a le_left_append_elim by auto
  show ?thesis
  proof (cases "f2a' = []")
    case True
    then have "VFun f2d \<sqsubseteq> VFun f3" using f2d f2b_f3 by simp
    then show ?thesis using f2c_f3 by blast
  next
    case False
    have "VFun f2d \<sqsubseteq> VFun f3" using f2d f2a_f3 f2b_f3 False f2b_ne by auto
    then show ?thesis using f2c_f3 by blast
  qed
qed

section "Beta Sound, aka Arrow Subtping"

lemma join_list_cons_none: "\<lbrakk> \<Squnion>ls = None; ls \<noteq> [] \<rbrakk> \<Longrightarrow> \<Squnion>(a#ls) = None" 
  apply (case_tac ls) apply auto done
  
fun eq :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<approx>" 55) where
  "VNat n1 \<approx> VNat n2 = (n1 = n2)" |
  "VFun f1 \<approx> VFun f2 = (set f1 = set f2)" |
  "v1 \<approx> v2 = False"

lemma eq_trans[trans]: "\<lbrakk> A \<approx> B; B \<approx> C \<rbrakk> \<Longrightarrow> A \<approx> C"
  apply (case_tac A) apply (case_tac B) apply force apply force
  apply (case_tac B) apply force apply simp
    apply (case_tac C) apply force apply force
  done
    
lemma join_assoc: "\<lbrakk> A \<squnion> B = Some AB; AB \<squnion> C = Some ABC \<rbrakk> \<Longrightarrow>
  \<exists> BC ABC'. B \<squnion> C = Some BC  \<and> A \<squnion> BC = Some ABC' \<and> ABC \<approx> ABC'"
  apply (case_tac A)
   apply (case_tac B)
    apply simp apply (case_tac "x1=x1a") apply simp apply clarify
     apply (case_tac C) apply simp apply (case_tac "x1a=x1b") apply force apply force
     apply simp apply (case_tac "x1=x1a") apply force apply force apply force
  apply simp apply (case_tac B) apply force apply simp apply (case_tac "x2=x2a") apply simp
   apply clarify apply simp apply (case_tac C) apply force apply simp
   apply (case_tac "x2a = x2") apply force apply simp apply clarify apply simp
  apply (case_tac "x2=[]") 
   apply simp apply clarify apply (case_tac C) apply force apply simp
    apply (case_tac "x2a=x2b") apply force apply force
  apply (case_tac "x2=x2a") apply force apply simp
  apply clarify apply (case_tac C) apply force apply simp
  apply (case_tac "x2@x2a = x2b") apply simp apply clarify
   apply (case_tac "x2@x2a = []") apply force apply simp
   apply (rule impI) apply (rule conjI) apply (rule impI) 
    apply (metis set_append sup.right_idem sup_left_idem)
  apply blast
  apply simp apply (case_tac "x2b = []") apply force apply force
  done
    
lemma join_list_append:
  "\<lbrakk> \<Squnion> f1 = Some A; \<Squnion> f2 = Some B; A \<squnion> B = Some C \<rbrakk> \<Longrightarrow>
    \<exists> C'. \<Squnion> (f1@f2) = Some C' \<and> C' \<approx> C" 
proof (induction f1 arbitrary: A B f2 C)
  case Nil
  then show ?case by force
next
  case (Cons v1 f1')
  show ?case
  proof (cases "f1' = []")
    case True
    show ?thesis
    proof (cases f2)
      case Nil
      then show ?thesis using Cons.prems(2) by auto
    next
      case (Cons v2 f2')
      then show ?thesis using Cons.prems True Cons
        apply simp apply (case_tac C) apply auto done
    qed
  next
    case False
    obtain A' where ap: "\<Squnion>f1' = Some A'" and v1_Ap_A: "v1 \<squnion> A' = Some A" using False Cons(2) 
      apply (case_tac "\<Squnion>f1'") using join_list_cons_none[of f1' v1] apply force
      by (smt join_list.elims list.distinct(1) list.inject option.simps(5))    
    from Cons have abc: "A \<squnion> B = Some C" by simp
    obtain C' D where apbc: "A' \<squnion> B = Some C'" and v1_cp_d: "v1 \<squnion> C' = Some D" and c_d: "C \<approx> D"
      using v1_Ap_A abc join_assoc[of v1 A' A B C] by blast
    from Cons(1)[of A' f2 B C'] obtain C'' where f1p_f2_cpp: "\<Squnion> (f1' @ f2) = Some C''"
      and cpp_cp: "C'' \<approx> C'" using Cons(3) ap apbc by blast 
    
    have "\<Squnion>(v1#(f1'@f2)) = Some X" using f1p_f2_cpp sorry
    show "\<exists>C'. \<Squnion> ((v1 # f1') @ f2) = Some C' \<and> C' \<approx> C" sorry
  qed
qed
  
lemma factor_aux:
    "\<lbrakk> (v1::val) \<sqsubseteq> v2; v1 = VFun f1; v2 = VFun f2; (A,B) \<in> set f1 \<rbrakk> \<Longrightarrow>
     \<exists> f2' As Bs. set f2' \<subseteq> set f2 \<and> \<Squnion> (map fst f2') = Some As \<and> \<Squnion> (map snd f2') = Some Bs
       \<and> As \<sqsubseteq> A \<and> B \<sqsubseteq> Bs" 
proof (induction arbitrary: f1 f2 A B rule: val_le.induct)
  case (le_nat n)
  then have "False" by auto
  then show ?case ..
next
  case (le_bot f)
  then have "False" by auto
  then show ?case ..
next
  case (le_app_R1 f1' f2a f2b)
  obtain f2' As Bs where f2p: "set f2' \<subseteq> set f2a" and
    As: "\<Squnion> (map fst f2') = Some As" and Bs: "\<Squnion> (map snd f2') = Some Bs" and
    As_A: "As \<sqsubseteq> A" and B_Bs: "B \<sqsubseteq> Bs" using le_app_R1 by force 
  have f2p_f2: "set f2' \<subseteq> set f2"  using f2p le_app_R1.prems(2) by auto
  then show ?case using As As_A B_Bs Bs by blast
next
  case (le_app_R2 f1' f2b f2a)
  obtain f2' As Bs where f2p: "set f2' \<subseteq> set f2b" and
    As: "\<Squnion> (map fst f2') = Some As" and Bs: "\<Squnion> (map snd f2') = Some Bs" and
    As_A: "As \<sqsubseteq> A" and B_Bs: "B \<sqsubseteq> Bs" using le_app_R2 by force
  have f2p_f2: "set f2' \<subseteq> set f2"  using f2p le_app_R2.prems(2) by auto
  then show ?case using As As_A B_Bs Bs by blast
next
  case (le_app_L f1a f2' f1b)
  have "(A,B) \<in> set f1a \<or> (A,B) \<in> set f1b" using le_app_L by auto
  then show ?case
  proof
    assume "(A,B) \<in> set f1a"
    from this obtain f As Bs where f_f2: "set f \<subseteq> set f2" and
      As: "\<Squnion>(map fst f) = Some As" and Bs: "\<Squnion>(map snd f) = Some Bs" and
      As_A: "As \<sqsubseteq> A" and B_Bs: "B \<sqsubseteq> Bs"
      using le_app_L.IH(1)[of f1a f2 A B] le_app_L(8) by blast
    show ?thesis 
      by (meson \<open>\<And>thesis. (\<And>f As Bs. \<lbrakk>set f \<subseteq> set f2; \<Squnion> (map fst f) = Some As; \<Squnion> (map snd f) = Some Bs; As \<sqsubseteq> A; B \<sqsubseteq> Bs\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
  next
    assume "(A,B) \<in> set f1b"
    from this obtain f As Bs where f_f2: "set f \<subseteq> set f2" and
      As: "\<Squnion>(map fst f) = Some As" and Bs: "\<Squnion>(map snd f) = Some Bs" and
      As_A: "As \<sqsubseteq> A" and B_Bs: "B \<sqsubseteq> Bs"
      using le_app_L.IH(2)[of f1b f2 A B] le_app_L(8) by blast
    show ?thesis 
      by (meson \<open>\<And>thesis. (\<And>f As Bs. \<lbrakk>set f \<subseteq> set f2; \<Squnion> (map fst f) = Some As; \<Squnion> (map snd f) = Some Bs; As \<sqsubseteq> A; B \<sqsubseteq> Bs\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
  qed
next
  case (le_arrow v2 v1 v1' v2')
  then show ?case apply (rule_tac x=f2 in exI) apply (rule_tac x=v2 in exI) 
      apply (rule_tac x=v2' in exI) apply auto done
next
  case (le_distr va vb vab v1 f2')
  from le_distr.IH(1)[of "[(A,va)]" f2 A va] obtain f2a As Bs where
     f2a_f2: "set f2a \<subseteq> set f2" and As: "\<Squnion> (map fst f2a) = Some As" and
     Bs: "\<Squnion> (map snd f2a) = Some Bs" and
     As_A: "As \<sqsubseteq> A" and va_Bs: "va \<sqsubseteq> Bs" using le_distr(6) le_distr(7) le_distr(8) by force
  from le_distr.IH(2)[of "[(A,vb)]" f2 A vb] obtain f2b As2 Bs2 where
     f2b_f2: "set f2b \<subseteq> set f2" and As2: "\<Squnion> (map fst f2b) = Some As2" and
     Bs2: "\<Squnion> (map snd f2b) = Some Bs2" and
     As2_A: "As2 \<sqsubseteq> A" and vb_Bs2: "vb \<sqsubseteq> Bs2" using le_distr(6) le_distr(7) le_distr(8) by force
  
      
  show ?case apply (rule_tac x="f2a@f2b" in exI) 
qed
  
end