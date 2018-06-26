theory ValuesFSet
  imports Main "~~/src/HOL/Library/FSet" 
begin

datatype val = VNat nat | VFun "(val \<times> val) fset" 
type_synonym entry = "val \<times> val" 
type_synonym func = "entry fset"  

abbreviation bottom_fun :: "val" ("\<bottom>" 100) where
  "bottom_fun \<equiv> VFun {||}"

fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 |\<union>| f2))" |
  "v1 \<squnion> v2 = None"

abbreviation join_maybe :: "val \<Rightarrow> val option \<Rightarrow> val option" where  
  "join_maybe v1 mv2 \<equiv> 
    (case mv2 of
        None \<Rightarrow> None
     | Some v2 \<Rightarrow> v1 \<squnion> v2)"

definition join_val_fset :: "val \<Rightarrow> val fset \<Rightarrow> val option" (infix "\<squnion>" 55) where
  "v \<squnion> L \<equiv> ffold join_maybe (Some v) L"
  
definition join_fset :: "val fset \<Rightarrow> val option" ("\<Squnion>") where
  "\<Squnion> L \<equiv> (let v = (SOME x. x |\<in>| L) in v \<squnion> L)"  

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52)
  and fun_in :: "val \<Rightarrow> val \<Rightarrow> func \<Rightarrow> bool"  ("_\<mapsto>_ \<sqsubseteq> _" [54,54,54] 55) where
  le_nat[intro!]: "VNat n \<sqsubseteq> VNat n" |
  le_fun: "\<lbrakk> \<forall> v v'. (v,v') \<in> fset f1 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f2 \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2" |
  le_arrow: "\<lbrakk> (v2, v2') \<in> fset f; v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> f" |
  le_distr: "\<lbrakk> va \<squnion> vb = Some vab; v\<mapsto>va \<sqsubseteq> f; v\<mapsto>vb \<sqsubseteq> f \<rbrakk> \<Longrightarrow> v\<mapsto>vab \<sqsubseteq> f"

inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n" and
  le_any_nat_inv[elim!]: "v \<sqsubseteq> VNat n" and 
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v" and
  le_any_bot_inv: "v \<sqsubseteq> \<bottom>" and 
  le_fun_fun_inv: "VFun f1 \<sqsubseteq> VFun f2" and
  le_fun_any_inv: "VFun f \<sqsubseteq> v" and
  le_arrow_fun_inv: "v \<mapsto> v' \<sqsubseteq> f" 

lemma le_bot: "\<bottom> \<sqsubseteq> VFun f"
  by (rule le_fun) auto
  
section "Value Size and Induction"
  
fun vadd :: "(val \<times> nat) \<times> (val \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "vadd ((_,v),(_,u)) r = v + u + r"
  
primrec vsize :: "val \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
vs_fun: "vsize (VFun t) = 1 + ffold vadd 0
                            (fimage (map_prod (\<lambda> v. (v,vsize v)) (\<lambda> v. (v,vsize v))) t)"

abbreviation vprod_size :: "val \<times> val \<Rightarrow> (val \<times> nat) \<times> (val \<times> nat)" where
  "vprod_size \<equiv> map_prod (\<lambda> v. (v,vsize v)) (\<lambda> v. (v,vsize v))"

definition fsize :: "func \<Rightarrow> nat" where
  "fsize t \<equiv> 1 + ffold vadd 0 (fimage vprod_size t)"

lemma vsize_fun[simp]: "vsize (VFun t) = fsize t"
  by (simp add: fsize_def)
  
declare vs_fun[simp del]
    
interpretation vadd_vprod: comp_fun_commute "vadd \<circ> vprod_size"
  unfolding comp_fun_commute_def by auto  

lemma vprod_size_inj: "inj_on vprod_size (fset A)"
  unfolding inj_on_def by auto
  
lemma fsize_def2: "fsize t = 1 + ffold (vadd \<circ> vprod_size) 0 t"
  using vprod_size_inj[of t] ffold_fimage[of vprod_size t vadd 0] fsize_def by simp

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
  also from v12_t have "... = 1 + ?f (v1,v2) (ffold ?f 0 t)" by simp
  finally have "fsize (finsert (v1,v2) t) = 1 + ?f (v1,v2) (ffold ?f 0 t)" .
  from this show ?thesis using fsize_def2[of t] by simp
qed
  
lemma size_fun_mem[simp]: "(v,v') \<in> fset f \<Longrightarrow> vsize v + vsize v' \<le> fsize f"
  by (induction f) auto
    
lemma size_fun_mem2: "\<lbrakk> (v1,v1') \<in> fset f; (v2,v2') \<in> fset f; (v1,v1') \<noteq> (v2,v2') \<rbrakk>
  \<Longrightarrow> vsize v1 + vsize v1' + vsize v2 + vsize v2' \<le> fsize f"
  by (induction f) auto
    
lemma fsize_pos[simp]: "0 < fsize f"
  by (simp add: fsize_def)
    
lemma vsize_pos[simp]: "0 < vsize v"
  by (case_tac v) auto
    
lemma fsize_union[simp]: "fsize (x1 |\<union>| x2) \<le> fsize x1 + fsize x2"
proof (induction x1)
  case empty
  then show ?case by auto
next
  case (insert x x1')
  obtain v1 v2 where x: "x=(v1,v2)" by (cases x) auto    
  show ?case
  proof (cases "(v1,v2) |\<in>| x2")
    case True
    then have "fsize (finsert (v1,v2) x1'|\<union>|x2) = fsize (x1'|\<union>|x2)" by auto
    also have "... \<le> fsize x1' + fsize x2" using insert(2) by blast
    also have "... \<le> fsize (finsert (v1,v2) x1') + fsize x2" using insert(1) x by auto
    finally show ?thesis using x by simp
  next
    case False
    then have "(v1,v2) |\<notin>| (x1'|\<union>|x2)" using insert(1) x by blast
    then have "fsize (finsert (v1,v2) x1'|\<union>|x2) = vsize v1 + vsize v2 + fsize (x1'|\<union>|x2)"
      by simp 
    then show ?thesis using insert x by auto
  qed
qed
    
lemma vsize_join: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> vsize v12 \<le> vsize v1 + vsize v2"
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force apply (case_tac v2) apply force apply (case_tac v12)
   apply force apply force
  done
    
    
(*
function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + fsize t" |
"fsize [] = 0" |
"fsize ((v,v')#t) = vsize v + vsize v' + fsize t"
  by pat_completeness auto
termination vsize by size_change


    
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
   
*)

section "Reflexivity"  

proposition le_refl[intro!]: "v \<sqsubseteq> v"
  apply (induction v)
   apply force
  apply (rule le_fun)
   apply clarify
  apply (rule le_arrow) apply assumption apply auto   
  done

section "Introduction Rules for Join"
    
proposition le_join_left: fixes v2::val shows "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v1 \<sqsubseteq> v12" (* incl_L *)
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force
  apply (case_tac v2) apply force
  apply simp apply clarify apply (rule le_fun) apply clarify
    apply (rule le_arrow) apply auto
  done
    
proposition le_join_right: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v2 \<sqsubseteq> v12" (* incl_R *) 
    apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force
  apply (case_tac v2) apply force
  apply simp apply clarify apply (rule le_fun) apply clarify 
  apply (rule le_arrow) apply auto
    done

 proposition le_left_join: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" (* glb *)
  apply (case_tac v1) apply (case_tac v2) apply simp
  apply (case_tac "x1 = x1a") apply force apply force
  apply force
  apply (case_tac v2) apply force
   apply (case_tac v3) apply force
   apply (rename_tac f1 f2 f3)
   apply simp apply clarify apply (rule le_fun) apply clarify
     apply (subgoal_tac "(v,v') \<in> fset f1 \<or> (v,v') \<in> fset f2") prefer 2 apply force
     apply (erule disjE) 
    using le_fun_fun_inv apply auto done

section "Inversion Lemmas"
     
lemma le_bot_inv_aux: "(v1 \<sqsubseteq> v2 \<longrightarrow> v2 = \<bottom> \<longrightarrow> v1 = \<bottom>) \<and> (v\<mapsto>v' \<sqsubseteq> f \<longrightarrow> f \<noteq> {||})"
  apply (induction rule: val_le_fun_in.induct)   
  apply force
  apply simp apply (rule impI) apply (rule classical)
    apply (subgoal_tac "\<exists> v v'. (v,v') |\<in>| f1") prefer 2 apply auto[1]
    apply (erule exE)+ apply (erule_tac x=v in allE)apply (erule_tac x=v' in allE)
    apply (erule impE) apply (simp add: fmember.rep_eq) apply blast
  apply force 
  apply force
  done

lemma le_bot_inv[elim!]: "\<lbrakk> v \<sqsubseteq> \<bottom>; v = \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_bot_inv_aux by auto      

proposition le_fun_any_inv2: "\<lbrakk> VFun f \<sqsubseteq> v; \<And>f'. v = VFun f' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
   apply (erule le_fun_any_inv) apply auto done

section "More Introduction Rules"

lemma le_fun_subset_eq: fixes f1::func and f2::func 
  assumes f1_f2: "fset f1 \<subseteq> fset f2" shows "VFun f1 \<sqsubseteq> VFun f2"
proof
  show "\<forall>v v'. (v, v') \<in> fset f1 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f2 "
  proof clarify
    fix v v' assume "(v,v') \<in> fset f1"
    then have "(v,v') \<in> fset f2" using f1_f2 by blast
    then show "v\<mapsto>v' \<sqsubseteq> f2" by (rule le_arrow) auto
  qed
qed
  
proposition le_distr_trad1: fixes v2:: val assumes v12: "v1 \<squnion> v2 = Some v12" 
  shows "v \<mapsto> v12 \<sqsubseteq> {|(v,v1),(v,v2)|}"
  using v12 apply (rule le_distr) apply (rule le_arrow) defer apply (rule le_refl)
  apply (rule le_refl) apply (rule le_arrow) defer apply (rule le_refl) apply (rule le_refl)
  apply auto
  done
    
proposition le_distr_trad2: fixes v2::val assumes v12: "v1 \<squnion> v2 = Some v12" 
  shows "VFun {|(v,v1),(v,v2)|} \<sqsubseteq> VFun {|(v, v12)|}"
  apply (rule le_fun) apply clarify
  apply simp apply (erule disjE) apply clarify apply (rule le_arrow) apply force
    apply blast using v12 using le_join_left apply blast
  apply clarify apply (rule le_arrow) apply force apply blast
    using v12 using le_join_right apply blast
  done

lemma subset_fun_in_aux: "(v1\<sqsubseteq>v2 \<longrightarrow> True) 
    \<and> (v\<mapsto>v' \<sqsubseteq> f1 \<longrightarrow> (\<forall>f2. fset f1 \<subseteq> fset f2 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f2))"
  apply (induction rule: val_le_fun_in.induct)
      apply blast
     apply blast
  using le_arrow apply blast
  using le_distr apply blast
  done

lemma subset_fun_in: "\<lbrakk> v\<mapsto>v' \<sqsubseteq> f1; fset f1 \<subseteq> fset f2 \<rbrakk> \<Longrightarrow> v\<mapsto>v' \<sqsubseteq> f2"
  using subset_fun_in_aux by blast
  
proposition mon: fixes v1::val and v2::val and v1'::val and v2'::val and v12::val 
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'" and
    v12: "v1 \<squnion> v2 = Some v12" and v12p: "v1' \<squnion> v2' = Some v12'"
  shows "v12 \<sqsubseteq> v12'"
proof (cases v1)
  case (VNat n1) then have v1: "v1 = VNat n1" by simp
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    then show ?thesis using v1 1 2 v12 v12p by auto
  next
    case (VFun f2)
    then have "False" using v12 v1 by auto
    then show ?thesis ..
  qed
next
  case (VFun f1) then have v1: "v1 = VFun f1" by simp
  obtain f1' where v1p: "v1' = VFun f1'" using v1 1 by (case_tac v1') auto
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    then have "False" using v12 v1 by auto
    then show ?thesis ..
  next
    case (VFun f2) then have v2: "v2 = VFun f2" by simp
    obtain f2' where v2p: "v2' = VFun f2'" using v2 2 by (case_tac v2') auto
    show ?thesis using v1 v2 v1p v2p v12 v12p apply simp apply clarify apply (rule le_fun)
    proof clarify
      fix v v' assume vv_f12: "(v,v') \<in> fset (f1|\<union>|f2)"
      have "(v,v') \<in> fset f1 \<or> (v,v') \<in> fset f2" using vv_f12 by auto
      then show "v \<mapsto> v' \<sqsubseteq> f1' |\<union>| f2'"
      proof
        assume vv_f1: "(v,v') \<in> fset f1"
        show ?thesis using 1 v1 v1p apply simp apply (erule le_fun_fun_inv)
        proof -
          assume "\<forall>v v'. (v, v') \<in> fset f1 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f1'"
          then have "v \<mapsto> v' \<sqsubseteq> f1'" using vv_f1 by blast
          then show "v\<mapsto>v' \<sqsubseteq> f1' |\<union>| f2'" using subset_fun_in by simp
        qed          
      next
        assume vv_f2: "(v,v') \<in> fset f2"
        show ?thesis using 2 v2 v2p apply simp apply (erule le_fun_fun_inv)
        proof -
          assume "\<forall>v v'. (v, v') \<in> fset f2 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f2'"
          then have "v \<mapsto> v' \<sqsubseteq> f2'" using vv_f2 by blast
          then show "v\<mapsto>v' \<sqsubseteq> f1' |\<union>| f2'" using subset_fun_in by simp
        qed          
      qed
    qed
  qed
qed 
    
lemma upper_bound_join: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> \<exists> v12. v1 \<squnion> v2 = Some v12"
  apply (case_tac v1) apply (case_tac v2) apply auto apply (case_tac v2) by auto

lemma join_commutes: "A \<squnion> B = Some C \<Longrightarrow> B \<squnion> A = Some C"
  apply (case_tac A) apply (case_tac B) apply simp apply (case_tac "x1=x1a") apply force
    apply force apply force apply (case_tac B) apply force apply force done
    
interpretation join_commute: comp_fun_commute "join_maybe"
  unfolding comp_fun_commute_def 
  apply auto apply (rule ext) apply simp apply (case_tac xa)
   apply force
  apply simp apply (case_tac "x \<squnion> a") apply simp
   apply (case_tac "y \<squnion> a") apply force apply simp
   apply (case_tac a) apply (case_tac x) apply simp
    apply (case_tac "x1a=x1") apply force apply simp
     apply clarify apply (case_tac y) apply simp
    apply (case_tac "x1b=x1") apply force apply force
     apply force apply simp apply clarify apply (case_tac y)
     apply simp apply (case_tac "x1a=x1") apply auto 
   apply (case_tac x) apply auto apply (case_tac y) apply auto
  apply (case_tac x) apply auto apply (case_tac a) apply auto
   apply (case_tac "x1=x1a") apply auto apply (case_tac y)
    apply auto apply (case_tac a) apply auto apply (case_tac y)
   apply auto
  done

context comp_fun_commute
begin
  
  lemma ffold_singleton[simp]: "ffold f z {|x|} = f x z"
  proof -
    have x: "x |\<notin>| bot" by simp
    have "ffold f z {|x|} = ffold f z (finsert x bot)" by simp
    also have "... = f x (ffold f z bot)" using x ffold_finsert[of x bot z] by simp
    also have "... = f x z" by simp
    finally show ?thesis by simp
  qed

end

lemma join_idem: fixes v2::val shows "v1 \<squnion> v2 = Some v3 \<Longrightarrow> v1 \<squnion> v3 = Some v3"
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1=x1a") apply force apply force
   apply force apply (case_tac v2) apply force apply force
  done
  
lemma join_val_fset_mem: "\<lbrakk> v1 |\<in>| L; v2 \<squnion> L = Some v3 \<rbrakk> \<Longrightarrow> v1 \<squnion> v3 = Some v3"
  apply (induction L arbitrary: v1 v2 v3)
  apply force
  apply simp apply (erule disjE)
   apply clarify apply (simp add: join_val_fset_def)
   apply (case_tac "ffold join_maybe (Some v2) L") 
    apply force
   apply simp
   using join_idem apply blast
   apply (simp add: join_val_fset_def)
   apply (case_tac "ffold join_maybe (Some v2) L")
   apply force
   by (metis join_commute.ffold_fun_left_comm join_commute.ffold_singleton option.simps(5))

lemma join_commutes2: "A \<squnion> B = B \<squnion> A"
  apply (case_tac A) apply (case_tac B) apply force apply force
  apply (case_tac B) apply force apply force done

lemma join_val_finsert: fixes v1::val and v2:: val and L::"val fset"
shows "\<lbrakk> v2 |\<notin>| L; v1 \<squnion> L = Some v1_L \<rbrakk> \<Longrightarrow> v1 \<squnion> (finsert v2 L) = v2 \<squnion> v1_L" 
  by (simp add: join_val_fset_def)

lemma join_val_finsert_none: "\<lbrakk> v2 |\<notin>| L; (v1 \<squnion> L) = None \<rbrakk> \<Longrightarrow> v1 \<squnion> (finsert v2 L) = None" 
  by (simp add: join_val_fset_def)
  
    
     
    
lemma join_val_fset_mem2: "\<lbrakk> v1 |\<in>| L; v1 \<squnion> L = Some v3; v2 \<squnion> L = Some v4 \<rbrakk> \<Longrightarrow> v2 \<squnion> v3 = Some v4"
  apply (induction L arbitrary: v1 v2 v3 v4)
   apply force
  apply (simp add: join_val_fset_def)
  apply (case_tac "ffold join_maybe (Some v1) L")
  apply force
  apply (erule disjE)  
   apply clarify
  apply simp 
  apply (case_tac "ffold join_maybe (Some v2) L")
  apply simp 
   apply simp 
    
    
  sorry
    
lemma join_val_finsert: fixes v1::val and v3::val and L::"val fset"
  assumes v2_L: "v2 \<squnion> L = Some v3" shows "v1 \<squnion> (finsert v2 L) = v1 \<squnion> v3"
proof (cases "v1 |\<in>| L")
  case True
  then have v13: "v1 \<squnion> v3 = Some v3" using join_val_fset_mem v2_L by simp 
  show ?thesis
  proof (cases "v2 |\<in>| L")
    case True
    then have "finsert v2 L = L" by blast        
    then show ?thesis using v2_L apply simp
        
  next
    case False
    then show ?thesis sorry
  qed
    
    apply (simp add: join_val_fset_def)
next
  case False
  then show ?thesis sorry
qed

lemma upper_bound_join_fold: "\<lbrakk> (\<forall> v. v \<in> fset L \<longrightarrow> v \<sqsubseteq> u); v \<sqsubseteq> u \<rbrakk> \<Longrightarrow>
    \<exists>vj. ffold join_maybe (Some v) L = Some vj \<and> vj \<sqsubseteq> u"
  apply (induction L)
   apply force
  apply simp apply (case_tac "L = bot") apply simp
   apply (subgoal_tac "\<exists> y. x \<squnion> v = Some y") prefer 2 apply (simp add: upper_bound_join)
   apply clarify apply (rule_tac x=y in exI) apply simp using le_left_join apply blast
   apply clarify 
  by (metis le_left_join option.simps(5) upper_bound_join)

    
lemma upper_bound_join_fset: fixes L::"val fset" 
  assumes ub: "\<forall> v. v \<in> fset L \<longrightarrow> v \<sqsubseteq> u" and L_ne: "L \<noteq> {||}"
  shows "\<exists>vj. \<Squnion>L = Some vj \<and> vj \<sqsubseteq> u"
proof -
  let ?v = "SOME x. x |\<in>| L"
  have vL: "?v |\<in>| L" using L_ne fempty_ffilter ffmember_filter someI_ex by force
  have v_u: "?v \<sqsubseteq> u" using ub notin_fset vL by fastforce
  let ?L = "L |-| {|?v|}" 
  have ub2: "\<forall> v. v \<in> fset ?L \<longrightarrow> v \<sqsubseteq> u" using ub by auto
  obtain vj where "ffold join_maybe (Some ?v) ?L = Some vj" and "vj \<sqsubseteq> u"
    using ub2 v_u upper_bound_join_fold by blast
  then show ?thesis using L_ne join_fset_def by simp 
qed
  
lemma lower_bounds_join: "\<lbrakk> va \<squnion> vb = Some vab; va \<sqsubseteq> B1; vb \<sqsubseteq> B2 \<rbrakk> \<Longrightarrow> \<exists> B12. B1 \<squnion> B2 = Some B12"
  apply (case_tac va) apply (case_tac vb) apply force
   apply force apply (case_tac vb) apply force apply simp apply (case_tac "x2=x2a") apply simp
   apply (case_tac vab) apply force apply simp apply clarify apply (case_tac B1)
    apply force apply (case_tac B2) apply force apply clarify
  apply force
  apply clarify 
  apply (erule le_fun_any_inv)
   apply simp apply clarify
   apply (erule le_fun_any_inv)
    apply force
   apply force
  apply (erule le_fun_any_inv)
    apply auto
  done
    

lemma join_mem: assumes L_y: "\<Squnion>L = Some y" and xL: "x |\<in>| L"
  shows "x \<squnion> y = Some y"
  apply (induction
    
  
lemma join_finsert[simp]: fixes L::"val fset" assumes L_y: "\<Squnion>L = Some y"
  shows "\<Squnion> (finsert x L) = x \<squnion> y"
proof (cases "x |\<in>| L")
  case True then have xL: "finsert x L = L" by blast
  
  then show ?thesis sorry
next
  case False then have xL: "x |\<notin>| L" by blast
  have L_ne: "L \<noteq> bot" using L_y apply (case_tac "L=bot") by (auto simp: join_fset_def)
  let ?v = "SOME xa. xa = x \<or> xa |\<in>| L"
  let ?v2 = "SOME x. x |\<in>| L"
  have fL_y: "ffold join_maybe (Some ?v2) (L |-| {|?v2|}) = Some y" 
    using L_y L_ne join_fset_def apply auto by metis
  have xL2: "x |\<notin>| (L |-| {|?v2|})" using xL by blast
  show ?thesis
  proof (cases "?v = x")
    case True
    then show ?thesis sorry
  next
    case False
    then have v_v2: "?v = ?v2" sorry
    have "\<Squnion>(finsert x L) = ffold join_maybe (Some ?v) (finsert x L |-| {|?v|})" 
      using L_ne apply (simp add: join_fset_def) by metis
    also have "... = join_maybe x (ffold join_maybe (Some ?v) (L |-| {|?v|}))"
      using xL2 v_v2 by (metis (no_types, lifting) False fempty_iff finsertE finsert_fminus_if join_commute.ffold_finsert)
    also have "... = x \<squnion> y" using L_y apply (simp add: join_fset_def) 
      using L_ne v_v2 by (metis (no_types, lifting) option.simps(5))
    finally show ?thesis by blast
  qed
qed

  
section "Beta Sound, aka Arrow Subtping"
  
lemma join_assoc: "\<lbrakk> A \<squnion> B = Some AB; AB \<squnion> C = Some ABC \<rbrakk> \<Longrightarrow>
  \<exists> BC. B \<squnion> C = Some BC  \<and> A \<squnion> BC = Some ABC"
  apply (case_tac A)
   apply (case_tac B)
    apply simp apply (case_tac "x1=x1a") apply simp apply clarify
     apply (case_tac C) apply simp apply (case_tac "x1a=x1b") apply force apply force
     apply simp apply (case_tac "x1=x1a") apply force apply force apply force
  apply simp apply (case_tac B) apply force apply simp apply (case_tac "x2=x2a") apply simp
   apply clarify apply simp apply (case_tac C) apply force apply simp
   apply force
    apply clarify apply (case_tac C) apply force apply force
  done

lemma join_assoc2: "\<lbrakk> B \<squnion> C = Some BC; A \<squnion> BC = Some ABC \<rbrakk> \<Longrightarrow>
  \<exists> AB. A \<squnion> B = Some AB \<and> AB \<squnion> C = Some ABC"
  apply (case_tac B) apply (case_tac C) apply auto apply (case_tac "x1=x1a") apply auto
   apply (case_tac A) apply auto apply (case_tac "x1=x1a") apply auto
  apply (case_tac C) apply auto apply (case_tac A) apply auto
  done

lemma fold_join_nat:
  "ffold join_maybe (Some (VNat n)) L = Some v \<Longrightarrow> v = VNat n"
  apply (induction L arbitrary: n v)
   apply force
  apply simp
  apply (case_tac "ffold join_maybe (Some (VNat n)) L")
  apply force
  apply simp apply (case_tac x) apply simp
    apply (case_tac a) apply simp apply (case_tac "x1=x1a") apply force apply force
   apply force apply force
  done

lemma fold_join_nat_init:
  "ffold join_maybe (Some (VNat n)) L = Some v \<Longrightarrow>
  v = VNat n \<and> (\<forall>v. v |\<in>| L \<longrightarrow> v = VNat n)"
  apply (induction L arbitrary: n v)
   apply force
  apply simp
  apply (case_tac "ffold join_maybe (Some (VNat n)) L")
  apply force
  apply simp apply (case_tac x) apply simp
    apply (case_tac a) apply simp apply (case_tac "x1=x1a") apply force apply force
   apply force apply force
  done

lemma fold_join_all_nat:
  "\<forall>v. v |\<in>| L \<longrightarrow> v = VNat n \<Longrightarrow> ffold join_maybe (Some (VNat n)) L = Some (VNat n)"
  apply (induction L arbitrary: n)
  apply force
  apply force
  done

lemma fold_join_nat_result:
  "ffold join_maybe (Some v) L = Some (VNat n) \<Longrightarrow>
   v = VNat n \<and> (\<forall>v. v |\<in>| L \<longrightarrow> v = VNat n)"
  apply (induction L)
   apply force
  apply simp
  apply (case_tac "ffold join_maybe (Some v) L")
   apply force
  apply simp
  apply (case_tac x) apply simp apply (case_tac a) apply simp
    apply (case_tac "x1=x1a") apply force apply force
   apply force
  apply (case_tac a) apply force apply force
  done
    
lemma fold_join_fun:
  "ffold join_maybe (Some (VFun f)) L = Some v \<Longrightarrow> \<exists>f'. v = VFun f' \<and> f |\<subseteq>| f'"
  apply (induction L arbitrary: f v)
  apply force
  apply simp apply (case_tac "ffold join_maybe (Some (VFun f)) L")
  apply force
  apply simp apply (case_tac a) apply force
  apply simp apply (case_tac x) apply force apply force
  done

lemma fold_join_fun_init:
  "ffold join_maybe (Some (VFun f)) L = Some v \<Longrightarrow>
   \<exists>f'. v = VFun f' \<and> fset f' = fset f \<union> \<Union>{ fset f|f. VFun f |\<in>| L}"
  apply (induction L arbitrary: f v)
  apply force
  apply (case_tac "ffold join_maybe (Some (VFun f)) L")
  apply force
  apply (case_tac a) apply force
  apply (case_tac x) apply force
  apply simp
  apply (case_tac v) apply force
  apply clarify
  apply (rule_tac x="x2a|\<union>|x2" in exI) apply simp
  apply (subgoal_tac "\<exists>f'. VFun x2 = VFun f' \<and> fset f' = fset f \<union> \<Union>{fset f |f. VFun f |\<in>| L}")
  prefer 2 apply blast
  apply blast
  done

lemma fold_join_all_fun:
  "\<forall>v. v |\<in>| L \<longrightarrow> (\<exists>f. v = VFun f) \<Longrightarrow>
   \<exists> f'. ffold join_maybe (Some (VFun f)) L = Some (VFun f') \<and>
      fset f' = fset f \<union> \<Union>{fset f|f. VFun f |\<in>| L }"
  apply (induction L)
   apply force
  apply simp apply clarify
  apply (case_tac x) apply force
  apply simp apply clarify
  apply blast
  done

lemma fold_join_fun_result:
  "ffold join_maybe (Some v) L = Some (VFun f) \<Longrightarrow>
  \<exists> f'. v = VFun f' \<and> (\<forall>v. v |\<in>| L \<longrightarrow> (\<exists>f'. v = VFun f'))
     \<and> fset f = fset f' \<union> \<Union>{fset f|f. VFun f |\<in>| L}"
  apply (induction L arbitrary: f)
  apply force
  apply simp apply (case_tac "ffold join_maybe (Some v) L")
   apply force
  apply simp apply (case_tac x) apply (case_tac a) apply simp
    apply (case_tac "x1=x1a") apply force apply force
   apply force apply simp apply (case_tac a) apply force
  apply simp apply clarify 
    apply (subgoal_tac "\<exists>f'. v = VFun f' \<and>
                  (\<forall>v. v |\<in>| L \<longrightarrow> (\<exists>f'. v = VFun f')) \<and>
                  fset x2a = fset f' \<union> \<Union>{fset f |f. VFun f |\<in>| L}") prefer 2 apply blast
  apply clarify apply auto
  done
    
lemma fold_join_union:
  assumes fl1_A: "ffold join_maybe (Some v1) L1 = Some A" and
    fl2_B: "ffold join_maybe (Some v2) L2 = Some B" and
    abc: "A \<squnion> B = Some C" and v1_L1: "v1 |\<notin>| L1|\<union>|L2" and v2_L2: "v2 |\<notin>| L1|\<union>|L2" and
    l1_l2: "L1 |\<inter>| L2 = bot"
  shows "ffold join_maybe (Some v2) ((finsert v1 L1) |\<union>| L2) = Some C" 
  using fl1_A fl2_B abc v1_L1 v2_L2 l1_l2
proof (induction L1 arbitrary: v1 v2 L2 A B C)
  case empty
  have v1: "v1 = A" using empty(1) by auto
  have A_L2: "A |\<notin>| L2" using empty(4) v1 by blast
  have "ffold join_maybe (Some v2) (finsert A L2)
          = join_maybe A (ffold join_maybe (Some v2) L2)" using A_L2 by simp
  also have "... = A \<squnion> B" using empty(2) by simp
  also have "... = Some C" using v1 empty(3) by simp
  finally show ?case using v1 by simp
next
  case (insert D L1')
  obtain E where fl1_E: "ffold join_maybe (Some v1) L1' = Some E"
    and de_a: "D \<squnion> E = Some A" using insert by (case_tac "ffold join_maybe (Some v1) L1'") auto
  obtain EB where eb: "E \<squnion> B = Some EB" and
    deb: "D \<squnion> EB = Some C" using de_a insert(5) join_assoc[of D E A B C] by blast
  have v1_l12: "v1 |\<notin>| L1' |\<union>| L2" using insert(6) by blast
  have v2_l12: "v2 |\<notin>| L1' |\<union>| L2" using insert(7) by blast
  have l1p_l2: "L1' |\<inter>| L2 = {||}" using insert.prems(6) by auto
  from insert(2)[of v1 E v2 L2 B EB] fl1_E insert(4) v1_l12 v2_l12 eb l1p_l2
  have fv1l12: "ffold join_maybe (Some v2) ((finsert v1 L1') |\<union>| L2) = Some EB" by blast
  have d_l1l2: "D |\<notin>| (finsert v1 L1') |\<union>| L2" using insert(1) insert(8) insert.prems(4) by blast
  have "ffold join_maybe (Some v2) (finsert v1 (finsert D L1') |\<union>| L2)
      = ffold join_maybe (Some v2) (finsert D ((finsert v1 L1') |\<union>| L2))"
    by (simp add: finsert_commute)
  also have "... = join_maybe D (ffold join_maybe (Some v2) ((finsert v1 L1') |\<union>| L2))"
    using d_l1l2 by simp
  also have "... = D \<squnion> EB" using fv1l12 by simp
  also have "... = Some C" using deb by simp
  finally show ?case by blast
qed    

lemma union_fold_join: 
  assumes L12_C: "ffold join_maybe (Some v) (L1|\<union>|L2) = Some C" and L12: "L1|\<inter>|L2 = bot"
  shows "\<exists> A B. ffold join_maybe (Some v) L1 = Some A 
              \<and> ffold join_maybe (Some v) L2 = Some B
              \<and> A \<squnion> B = Some C"
  using L12_C L12
  apply (induction L1 arbitrary: v L2 C)
    -- "base case" 
   apply simp apply (case_tac v) apply (case_tac C) apply simp
    apply (subgoal_tac "VNat x1a = VNat x1") prefer 2 using fold_join_nat apply blast
     apply blast
     apply (subgoal_tac "C = VNat x1") prefer 2 using fold_join_nat apply blast apply force
   apply simp
   apply (subgoal_tac "\<exists>f'. C = VFun f' \<and> x2 |\<subseteq>| f'") prefer 2 using fold_join_fun apply blast
   apply clarify apply force
    -- "induction step"
  apply (subgoal_tac "x |\<notin>| (L1|\<union>|L2)") prefer 2 apply blast
  apply simp apply (subgoal_tac "L1|\<inter>|L2 = bot") prefer 2 apply blast
  apply (case_tac "ffold join_maybe (Some v) (L1 |\<union>| L2)")
   apply force
    apply (subgoal_tac "\<exists>A. ffold join_maybe (Some v) L1 = Some A \<and>
               (\<exists>B. ffold join_maybe (Some v) L2 = Some B \<and> A \<squnion> B = Some a)") 
    prefer 2 apply blast
    apply clarify  
  apply simp
  using join_assoc2 apply blast
  done   

lemma union_nat_result: "\<Squnion>L = Some (VNat n) \<Longrightarrow> (\<forall>v. v |\<in>| L \<longrightarrow> v = VNat n)"
  apply (case_tac "L = bot") apply force apply (simp add: join_fset_def)
  using fold_join_nat_result join_fset_def
  by (metis fempty_iff finsertE fminusI)

lemma union_all_nat: assumes alln: "\<forall>v. v |\<in>| L \<longrightarrow> v = VNat n" and L_ne: "L \<noteq> bot"
  shows "\<Squnion>L = Some (VNat n)"
proof -
  let ?P = "\<lambda>x. x |\<in>| L"
  let ?v = "SOME x. x |\<in>| L" let ?L = "L |-| {|?v|}"
  obtain x where xL: "x |\<in>| L" using L_ne by blast
  have "?v |\<in>| L" using xL by (rule someI)
  then have v: "?v = VNat n" using alln by blast
  have alln2: "\<forall>v. v |\<in>| (L|-| {|VNat n|}) \<longrightarrow> v = VNat n" using alln by blast    
  have "\<Squnion>L = ffold join_maybe (Some ?v) ?L" using L_ne join_fset_def by metis
  also have "... = ffold join_maybe (Some (VNat n)) (L |-| {|VNat n|})" using v by simp
  also have "... = Some (VNat n)" using fold_join_all_nat[of "L-{|VNat n|}" n] alln2 by simp
  finally show ?thesis by blast
qed
  
abbreviation union_fun :: "val fset \<Rightarrow> func \<Rightarrow> bool" where
  "union_fun L f \<equiv> (\<forall>v. v |\<in>| L \<longrightarrow> (\<exists>f'. v = VFun f')) \<and> fset f = \<Union>{fset f'|f'. VFun f' |\<in>| L}"
  
lemma union_fun_result: assumes Lf: "\<Squnion>L = Some (VFun f)"
  shows "(\<forall>v. v |\<in>| L \<longrightarrow> (\<exists>f'. v = VFun f')) \<and> fset f = \<Union>{fset f'|f'. VFun f' |\<in>| L}"
proof (cases "L = bot")
  case True
  then show ?thesis using Lf join_fset_def by auto
next
  case False
  let ?v = "SOME x. x |\<in>| L" let ?L = "L |-| {|?v|}"
  have "\<Squnion>L = ffold join_maybe (Some ?v) (L |-| {|?v|})" using False join_fset_def by metis
  from fold_join_fun_result[of ?v ?L f] Lf this
  obtain f' where vfp: "?v = VFun f'" and
    allf: "(\<forall>v. v |\<in>| L |-| {|?v|} \<longrightarrow> (\<exists>f'. v = VFun f'))" and
    f: "fset f = fset f' \<union> \<Union>{fset f |f. VFun f |\<in>| L |-| {|?v|}}" by auto
  have 1: "(\<forall>v. v |\<in>| L \<longrightarrow> (\<exists>f'. v = VFun f'))" using vfp allf apply auto done
  have f2: "fset f = fset f' \<union> \<Union>{fset f |f. VFun f |\<in>| L |-| {|VFun f'|}}" using vfp f by simp
  have "?v |\<in>| L" using False apply (subgoal_tac "\<exists>x. x |\<in>| L") prefer 2 apply blast apply clarify
    apply (rule someI) apply blast done
  then have fpL: "VFun f' |\<in>| L" using vfp by simp
  then have 2: "fset f = \<Union>{fset f'|f'. VFun f' |\<in>| L}" using f2 by auto
  show ?thesis using 1 2 by blast
qed
        
lemma union_all_fun: assumes allf: "\<forall>v. v |\<in>| L \<longrightarrow> (\<exists>f. v = VFun f)" and L_ne: "L \<noteq> bot"
  shows "\<exists>f. \<Squnion>L = Some (VFun f) \<and> fset f = \<Union>{fset f'|f'. VFun f' |\<in>| L}"
proof -
  let ?P = "\<lambda>x. x |\<in>| L"
  let ?v = "SOME x. x |\<in>| L" let ?L = "L |-| {|?v|}"
  obtain x where xL: "x |\<in>| L" using L_ne by blast
  have vL: "?v |\<in>| L" using xL by (rule someI)
  obtain f where v: "?v = VFun f" and fL: "VFun f |\<in>| L" using allf vL by auto
  have allf2: "\<forall>v. v |\<in>| (L|-| {|VFun f|}) \<longrightarrow> (\<exists>f. v = VFun f)" using allf by blast  
  from fold_join_all_fun[of "L-{|VFun f|}" f] allf2
  obtain f' where 1: "ffold join_maybe (Some (VFun f)) (L |-| {|VFun f|}) = Some (VFun f')" and
         2: "fset f' = fset f \<union> \<Union>{fset fa |fa. VFun fa |\<in>| L |-| {|VFun f|}}" by blast
  have "\<Squnion>L = ffold join_maybe (Some ?v) ?L" using L_ne join_fset_def by metis
  also have "... = ffold join_maybe (Some (VFun f)) (L |-| {|VFun f|})" using v by simp
  also have "... = Some (VFun f')" using 1 by simp 
  finally have 3: "\<Squnion>L = Some (VFun f')" by blast
  show ?thesis apply (rule_tac x=f' in exI) apply (rule conjI) using 3 apply force
      using 2 fL apply blast done
qed
  
lemma join_fset_union: fixes L1::"val fset" and L2::"val fset"
 assumes L1_A: "\<Squnion> L1 = Some A" and L2_B: "\<Squnion> L2 = Some B" and ABC: "A \<squnion> B = Some C"
 shows "\<Squnion> (L1|\<union>|L2) = Some C"
proof (cases A)
  case (VNat n)
  have b: "B = VNat n" using ABC VNat apply (case_tac B) apply auto apply (case_tac "n=x1")
      apply auto done
  have c: "C = VNat n" using ABC VNat b apply auto done      
  have L1_n: "\<forall>v. v |\<in>| L1 \<longrightarrow> v = VNat n" using L1_A VNat union_nat_result by blast
  have L2_n: "\<forall>v. v |\<in>| L2 \<longrightarrow> v = VNat n" using L2_B b union_nat_result by blast
  have L12_n: "\<forall>v. v |\<in>| L1|\<union>|L2 \<longrightarrow> v = VNat n" using L1_n L2_n by blast
  have L12_ne: "L1|\<union>|L2 \<noteq> bot" using L1_A join_fset_def apply (case_tac "L1=bot") apply auto done
  show ?thesis using L12_n c union_all_nat L12_ne by blast
next
  case (VFun fa)
  obtain fb where b: "B = VFun fb" using ABC VFun apply (case_tac B) apply auto done
  have c: "C = VFun (fa|\<union>|fb)" using ABC VFun b apply auto done
  have L1_fa: "union_fun L1 fa" using union_fun_result L1_A VFun apply auto done 
  have L2_fb: "union_fun L2 fb" using union_fun_result L2_B b apply auto done 
  have L12_f: "union_fun (L1|\<union>|L2) (fa|\<union>|fb)" using L1_fa L2_fb by auto
  have L12_ne: "L1|\<union>|L2 \<noteq> bot" using L1_A join_fset_def apply (case_tac "L1=bot") by auto
  show ?thesis using L12_f c union_all_fun[of "L1|\<union>|L2"] L12_ne 
    by (metis (no_types, lifting) fset_inject)
qed
  
    
lemma beta_helper: "\<lbrakk> \<forall> v v'. (v,v') \<in> fset f1 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f2;
           \<Squnion>(fst|`|f1) = Some C; \<Squnion>(snd|`|f1) = Some D\<rbrakk> \<Longrightarrow>
     C \<mapsto> D \<sqsubseteq> f2"
  apply (induction f1 arbitrary: f2 C D)
  apply (simp add: join_fset_def) 
      
  sorry
    
lemma le_trans_aux:
  "(\<forall> v1 v2 v3. n = vsize v1 + vsize v2 + vsize v3 \<longrightarrow>
        v1 \<sqsubseteq> v2 \<longrightarrow> v2 \<sqsubseteq> v3 \<longrightarrow> v1 \<sqsubseteq> v3) \<and>
   (\<forall>A B f. n = vsize A + vsize B + fsize f \<longrightarrow> A\<mapsto>B \<sqsubseteq> f \<longrightarrow>
       (\<exists>f' C D. fset f' \<subseteq> fset f
               \<and> \<Squnion>(fst|`|f') = Some C \<and> \<Squnion>(snd|`|f') = Some D
               \<and> C \<sqsubseteq> A \<and> B \<sqsubseteq> D))"
proof (induction n rule: nat_less_induct)
  -- "case 1"
  case (1 n)
  show ?case apply (rule conjI) apply clarify defer apply clarify defer
  proof -
    fix v1 v2 v3
    assume n: "n = vsize v1 + vsize v2 + vsize v3" and v1_v2: "v1 \<sqsubseteq> v2" and v2_v3: "v2 \<sqsubseteq> v3"
    show "v1 \<sqsubseteq> v3"
    proof (cases v2)
      case (VNat n)
      have v1: "v1 = VNat n" using VNat v1_v2 by auto
      have v3: "v3 = VNat n" using VNat v2_v3 by auto
      show ?thesis using v1 v3 by blast
    next
      case (VFun f2) then have v2: "v2 = VFun f2" by blast
      obtain f1 where v1: "v1 = VFun f1" using VFun v1_v2 by (case_tac v1) auto
      obtain f3 where v3: "v3 = VFun f3" using VFun v2_v3 by (case_tac v3) auto
      show ?thesis using v1 v3 apply simp apply (rule le_fun) apply clarify
      proof -
        fix v v' assume vv_f1: "(v,v') \<in> fset f1"
        show "v\<mapsto>v' \<sqsubseteq> f3" using v2_v3 v2 v3 apply simp apply (erule le_fun_fun_inv)
        proof -
          assume "f2 = bot" then have "f1 = bot" using v1_v2 v1 v2 by auto
          then have "False" using vv_f1 by auto 
          then show ?thesis ..
        next
          assume all_f2_f3: "\<forall>v v'. (v, v') \<in> fset f2 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f3"
          show ?thesis using v1_v2 v1 v2 apply simp apply (erule le_fun_fun_inv)
          proof -
            assume "f1 = bot" then have "False" using vv_f1 le_bot_inv_aux by auto
            then show ?thesis ..
          next
            assume all_f1_f2: "\<forall>v v'. (v, v') \<in> fset f1 \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f2"
            have vv_f2: "v\<mapsto>v' \<sqsubseteq> f2" using all_f1_f2 vv_f1 by blast
            have s: "vsize v + vsize v' + fsize f2 < n" using 1 v1 v2 sorry
            obtain f2' C D where f2p_f2: "fset f2' \<subseteq> fset f2" and
              c: "\<Squnion>(fst|`|f2') = Some C" and d: "\<Squnion>(snd|`|f2') = Some D" and
              c_v: "C \<sqsubseteq> v" and vp_d: "v' \<sqsubseteq> D" using 1 
              apply (erule_tac x="vsize v + vsize v' + fsize f2" in allE)
              apply (erule impE) using s apply blast using vv_f2 apply blast done
            have f2p_f3:"\<forall> v v'. (v,v') \<in> fset f2' \<longrightarrow> v\<mapsto>v' \<sqsubseteq> f3" using all_f2_f3 f2p_f2 by blast
            
            show "v\<mapsto>v' \<sqsubseteq> f3" sorry
          qed
        qed          
      qed
    qed
  next
    fix A B f
    show "\<exists>f' C D. fset f' \<subseteq> fset f \<and>
          \<Squnion> (fst |`| f') = Some C \<and> \<Squnion> (snd |`| f') = Some D \<and> C \<sqsubseteq> A \<and> B \<sqsubseteq> D " sorry
  qed
qed

    
    
(*    
lemma factor_aux: "(v1 \<sqsubseteq> v2 \<longrightarrow> True)
  \<and> (A \<mapsto> B \<in> f1 \<longrightarrow> (\<forall>f2. VFun f1 \<sqsubseteq> VFun f2 \<longrightarrow>
  (\<exists> f2' C D. fset f2' \<subseteq> fset f2 \<and> \<Squnion>(fst|`|f2') = Some C \<and> \<Squnion>(snd|`|f2') = Some D
     \<and> C \<sqsubseteq> A \<and> B \<sqsubseteq> D)))"
proof (induction rule: val_le_fun_in.induct)
  case (le_nat n)
  then show ?case by blast
next
  case (le_bot f)
  then show ?case by blast
next
  case (le_fun f1 f2)
  then show ?case by blast
next
  case (le_arrow v2 v2' f1 v1 v1')
  show ?case apply clarify
    apply (erule le_fun_fun_inv) using le_arrow apply force
    apply (subgoal_tac "v2 \<mapsto> v2' \<in> f2") prefer 2 using le_arrow(1) apply blast
    apply (erule le_arrow_fun_inv)
    apply (rename_tac v3 v3')
    apply (rule_tac x="{|(v2, v2')|}" in exI)
     apply (rule conjI) apply 
      
next
  case (le_distr va vb vab v1 f2)
  then show ?case sorry
qed
  

    
lemma factor_aux2:
    "\<lbrakk> (v1::val) \<sqsubseteq> v2; v1 = VFun f1; v2 = VFun f2; (A,B) \<in> fset f1 \<rbrakk> \<Longrightarrow>
     \<exists> f2' As Bs. fset f2' \<subseteq> fset f2 \<and> \<Squnion> (map fst f2') = Some As \<and> \<Squnion> (map snd f2') = Some Bs
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

  obtain As3 where As_As2: "As \<squnion> As2 = Some As3" using upper_bound_join As_A As2_A by blast
  obtain Bs3 where Bs_Bs2: "Bs \<squnion> Bs2 = Some Bs3" using lower_bounds_join va_Bs vb_Bs2 le_distr(1) by blast

  obtain As3' where f2ab_1: "\<Squnion> (map fst f2a @ map fst f2b) = Some As3'" and as3p_as3: "As3' \<approx> As3" 
    using join_list_append[of "map fst f2a" As "map fst f2b" As2 As3] As_As2 As As2 by blast
  obtain Bs3' where f2ab_2: "\<Squnion> (map snd f2a @ map snd f2b) = Some Bs3'" and bs3p_bs3: "Bs3' \<approx> Bs3" 
    using join_list_append[of "map snd f2a" Bs "map snd f2b" Bs2 Bs3] Bs_Bs2 Bs Bs2 by blast
  
  have As3_A: "As3 \<sqsubseteq> A" using As_A As2_A As_As2 using le_left_join by blast
        
  show ?case apply (rule_tac x="f2a@f2b" in exI) apply (rule_tac x=As3' in exI)
    apply (rule_tac x=Bs3' in exI) 
    apply (rule conjI) using f2a_f2 f2b_f2 apply force
    apply (rule conjI) using f2ab_1 apply simp
    apply (rule conjI) using f2ab_2 apply simp
    apply (rule conjI) 
    sorry
qed
  
lemma decomp_union_list: "set x = set f1 \<union> set f2 \<Longrightarrow>
 \<exists> x1 x2. x = x1@x2 \<and> set x1 = set f1 \<and> set x2 = set f2" 
  oops
    
lemma subset_sub: "\<lbrakk> set f' \<subseteq> set f; VFun f \<sqsubseteq> B \<rbrakk> \<Longrightarrow> VFun f' \<sqsubseteq> B"
  apply (induction f arbitrary: B f')
   apply force
  apply simp
    apply (case_tac B) apply force apply clarify
    apply (subgoal_tac "VFun ([(a,b)]@f) \<sqsubseteq> VFun x2") prefer 2 apply force
    apply (subgoal_tac "VFun [(a,b)] \<sqsubseteq> VFun x2 \<and> VFun f \<sqsubseteq> VFun x2") prefer 2
    apply (rule le_left_append_elim) apply blast apply blast
  apply clarify  
  apply (subgoal_tac "set (removeAll (a,b) f') = set f' - {(a,b)}") prefer 2 
   apply (rule set_removeAll) 
    apply (subgoal_tac "set (removeAll(a,b) f') \<subseteq> set f") prefer 2 apply blast
    apply (subgoal_tac "VFun (removeAll(a,b) f') \<sqsubseteq> VFun x2") prefer 2 apply blast    
(*  apply (induction A' B arbitrary: f f' rule: val_le.induct)
  apply force 
  apply force
  apply simp apply (subgoal_tac "VFun f \<sqsubseteq> VFun f2") prefer 2 apply blast  
    apply (case_tac f) apply force
    apply (rule le_app_R1) apply blast apply blast apply blast
  apply simp apply (subgoal_tac "VFun f \<sqsubseteq> VFun f3") prefer 2 apply blast  
    apply (case_tac f) apply force
    apply (rule le_app_R2) apply blast apply blast apply blast
  apply simp apply (subgoal_tac "VFun f1 \<sqsubseteq> VFun f3") prefer 2 apply blast
    apply (subgoal_tac "VFun f2 \<sqsubseteq> VFun f3") prefer 2 apply blast
    apply clarify
*)    oops
    
lemma eq_sub: "\<lbrakk> A' \<sqsubseteq> B; A \<approx> A'  \<rbrakk> \<Longrightarrow> A \<sqsubseteq> B"
(*  apply (induction A' B arbitrary: A rule: val_le.induct)
  apply (case_tac A) apply force apply force    
  apply (case_tac A) apply force apply force
  apply (case_tac A) apply force apply simp apply clarify
    apply (subgoal_tac "VFun x2 \<sqsubseteq> VFun f1") prefer 2 apply (simp add: le_fun_subset_eq) 
    apply (metis eq.elims(3) le_app_R1 set_empty val.inject(2) val.simps(4))
  apply (case_tac A) apply force apply force   
  apply (case_tac A) apply force apply simp apply clarify
    apply (subgoal_tac "VFun (f1@f3) \<sqsubseteq> VFun f3") prefer 2 
    apply (subgoal_tac "VFun f1 \<sqsubseteq> VFun f3") prefer 2 apply force
    apply (subgoal_tac "VFun f2 \<sqsubseteq> VFun f3") prefer 2 apply force
    apply blast 
*)  
 oops   
 
*)
end