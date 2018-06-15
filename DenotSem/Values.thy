theory Values
imports Main
begin

datatype val = VNat nat | VFun "(val \<times> val) list" 
type_synonym entry = "val \<times> val" 
type_synonym func = "entry list"  
abbreviation make_entry :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<mapsto>" 70) where
  "v \<mapsto> v' \<equiv> VFun [(v,v')]"
abbreviation bottom_fun :: "val" ("\<bottom>" 100) where
  "bottom_fun \<equiv> VFun []"

function vsize :: "val \<Rightarrow> nat" and fsize :: "func \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + fsize t" |
"fsize [] = 0" |
"fsize ((v,v')#t) = 1 + vsize v + vsize v' + fsize t"
  by pat_completeness auto
termination vsize by size_change

lemma fsize_append[simp]: "fsize (f1@f2) = fsize f1 + fsize f2"
  apply (induction f1 arbitrary: f2)
   apply force
  apply simp apply (case_tac a) apply simp 
  done

lemma size_fun_mem: "(v,v') \<in> set f \<Longrightarrow> vsize v + vsize v' < fsize f"
  by (induction f) auto  
  
lemma size_fun_mem2: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; (v1,v1') \<noteq> (v2,v2') \<rbrakk>
  \<Longrightarrow> vsize v1 + vsize v1' + vsize v2 + vsize v2' < fsize f"
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
    then have "vsize v1a + vsize v1'a < fsize fa"
      by (meson size_fun_mem)
    then show "vsize v1a + vsize v1'a + vsize a + vsize b < fsize ((a, b) # fa)"
      by auto
qed 
      
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = (if f1 = f2 then Some (VFun f1) else Some (VFun (f1 @ f2)))" |
  "v1 \<squnion> v2 = None"
  
lemma size_fun_mem_join_fst: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; v1 \<squnion> v2 = Some v3 \<rbrakk>
   \<Longrightarrow> vsize v3 < Suc (fsize f)"
  apply (case_tac "v1 = v2")
   apply simp apply (case_tac v1) apply (case_tac v2) apply simp
     apply clarify using size_fun_mem apply force
    apply clarify apply simp using size_fun_mem apply force
  apply (case_tac v1) apply (case_tac v2) apply simp apply force
  apply (case_tac v2) apply force
  apply simp using size_fun_mem2 apply force
  done
    
lemma size_fun_mem_join: "\<lbrakk> (v1,v1') \<in> set f; (v2,v2') \<in> set f; v1' \<squnion> v2' = Some v3' \<rbrakk>
   \<Longrightarrow> vsize v3' < Suc (fsize f)"
  apply (case_tac "v1' = v2'")
   apply simp apply (case_tac v1') apply (case_tac v2') apply simp
     apply clarify using size_fun_mem apply force
    apply clarify apply simp using size_fun_mem apply force
  apply (case_tac v1') apply (case_tac v2') apply simp apply force
  apply (case_tac v2') apply force
  apply simp using size_fun_mem2 apply force
  done
  
fun env_join :: "val list \<Rightarrow> val list \<Rightarrow> (val list) option" (infix "\<squnion>" 56) where
  "env_join [] [] = Some []" |
  "env_join (v#\<rho>) (v'#\<rho>') = 
      (case v \<squnion> v' of
         None \<Rightarrow> None
      | Some v'' \<Rightarrow> 
           (case \<rho>\<squnion>\<rho>' of
             None \<Rightarrow> None
           | Some \<rho>'' \<Rightarrow> Some (v''#\<rho>'')))" 

  (* Adapted from BCD and EHR subtyping (Lambda Calculus with Types 2013) *) 
inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) 
    where
  le_refl[intro!]: "v \<sqsubseteq> v" | 
  le_trans[trans]: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3" |
  le_bot[intro!]: "\<bottom> \<sqsubseteq> VFun f" |
  le_fun_append_left: "VFun f1 \<sqsubseteq> VFun (f1@f2)" |
  le_fun_append_right: "VFun f2 \<sqsubseteq> VFun (f1@f2)" |
  le_fun_left_join: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3 \<rbrakk> \<Longrightarrow> VFun (f1@f2) \<sqsubseteq> VFun f3" |
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" |
  le_distr: "(v1::val) \<squnion> v2 = Some v12 \<Longrightarrow> v\<mapsto>v12 \<sqsubseteq> VFun [(v,v1), (v,v2)]"

inductive_cases 
  le_nat_nat_inv[elim!]: "VNat n1 \<sqsubseteq> VNat n2" and
  le_nat_fun_inv[elim!]: "VNat n \<sqsubseteq> VFun f" and
  le_fun_nat_inv[elim!]: "VFun f \<sqsubseteq> VNat n"
(* and
  le_fun_fun_inv[elim!]: "VFun f1 \<sqsubseteq> VFun f2" and
  
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v1" and
  le_any_fun_inv[elim!]: "v \<sqsubseteq> VFun f" and
  le_fun_any_inv[elim!]: "VFun f \<sqsubseteq> v" and
  le_cons_left_inv: " (a # f2) \<sqsubseteq>  f3" and
  le_single_left_inv: "[a] \<sqsubseteq> f" and
  le_single_cons_right_inv: "[a] \<sqsubseteq> (b#f)" and
  le_cons_left_single_inv: "a#f \<sqsubseteq> [b]" and
  le_single_both_inv: "[a] \<sqsubseteq> [b]" and
  le_cons_right_inv: "f1 \<sqsubseteq> (a#f2)" and
  le_cons_cons_inv: "a#f1 \<sqsubseteq> (b#f2)" and
  le_bot_right_inv: "v \<sqsubseteq> \<bottom>"
*)
  
proposition le_join_left: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v1 \<sqsubseteq> v12" (* incl_L *)
  apply (case_tac v1) apply (case_tac v2) apply simp
    apply (case_tac "x1 = x1a") apply force apply force
   apply force
  apply (case_tac v2) apply force
  apply simp
  apply (case_tac "x2 = x2a") apply force
  apply simp
  apply clarify
  apply (rule le_fun_append_left)
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
  apply (rule le_fun_append_right)
  done   
    
lemma le_bot_inv_aux: fixes v1::val and f1::func
  assumes v12: "v1 \<sqsubseteq> v2" and v2b: "v2 = \<bottom>"
  shows "v1 = \<bottom>"
  using v12 v2b by (induction rule: val_le.induct) auto
      

lemma le_bot_inv[elim!]: "\<lbrakk> f \<sqsubseteq> \<bottom>; f = \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_bot_inv_aux by auto      
    
lemma le_any_nat_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v' = VNat n\<rbrakk> \<Longrightarrow> v = VNat n"
  by (induction rule: val_le.induct) auto
    
proposition le_any_nat_inv[elim!]: "\<lbrakk> v \<sqsubseteq> VNat n; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_any_nat_inv_aux[of v "VNat n" n] apply auto done
  
lemma le_nat_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VNat n\<rbrakk> \<Longrightarrow> v' = VNat n"
  by (induction arbitrary: n rule: val_le.induct) auto
    
proposition le_nat_any_inv[elim!]: "\<lbrakk> VNat n \<sqsubseteq> v; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_nat_any_inv_aux[of "VNat n" v n] apply auto done    

lemma le_fun_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VFun f \<rbrakk> \<Longrightarrow> \<exists> f'. v' = VFun f'"
  by (induction arbitrary: f rule: val_le.induct) auto
  
proposition le_fun_any_inv: "\<lbrakk> VFun f \<sqsubseteq> v; \<And>f'. v = VFun f' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_fun_any_inv_aux by blast

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
  by (simp add: le_fun_left_join)
 
proposition mon: fixes v1::val and v2::val and v1'::val and v2'::val and v12::val 
  assumes 1: "v1 \<sqsubseteq> v1'" and 2: "v2 \<sqsubseteq> v2'" and
    v12: "v1 \<squnion> v2 = Some v12" and v12p: "v1' \<squnion> v2' = Some v12'"
  shows "v12 \<sqsubseteq> v12'"
proof -
  have 3: "v1' \<sqsubseteq> v12'" using le_join_left v12p by blast
  have 4: "v2' \<sqsubseteq> v12'" using le_join_right v12p by blast
  have 5: "v1 \<sqsubseteq> v12'" using 1 3 le_trans by blast
  have 6: "v2 \<sqsubseteq> v12'" using 2 4 le_trans by blast
  show "v12 \<sqsubseteq> v12'" using 5 6 le_left_join v12 by blast
qed

lemma le_fun_append_left_sub: assumes f1_f1p: "VFun f1 \<sqsubseteq> VFun f1'" shows "VFun f1 \<sqsubseteq> VFun (f1'@f2)"
proof -
  have "VFun f1' \<sqsubseteq> VFun (f1'@f2)" using le_fun_append_left by blast
  then show ?thesis using f1_f1p le_trans by blast
qed

lemma le_fun_append_right_sub: assumes f1_f1p: "VFun f2 \<sqsubseteq> VFun f2'" shows "VFun f2 \<sqsubseteq> VFun (f1@f2')"
proof -
  have "VFun f2' \<sqsubseteq> VFun (f1@f2')" using le_fun_append_right by blast
  then show ?thesis using f1_f1p le_trans by blast
qed
  
lemma le_fun_elt: assumes v1f: "(v,v') \<in> set f" shows "v\<mapsto>v' \<sqsubseteq> VFun f"
  using v1f apply (induction f) 
   apply force
  apply simp apply (erule disjE)
   apply simp
   apply (case_tac "f=[a]")
    apply simp using le_fun_left_join apply (metis append_Cons append_Nil le_fun_append_left)
   apply clarify
  using le_join_left apply (metis append.left_neutral append_Cons le_fun_append_left)
  apply (subgoal_tac "v \<mapsto> v' \<sqsubseteq> VFun ([a] @ f)") prefer 2
   apply (rule le_fun_append_right_sub) apply blast
  apply simp
  done
 
lemma le_fun_subset: fixes f1::func shows "\<lbrakk> set f1 \<subseteq> set f2 \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
  apply (induction f1)
  apply force
  apply simp apply clarify
  apply (subgoal_tac "a\<mapsto>b \<sqsubseteq> VFun f2") prefer 2 apply (rule le_fun_elt) apply blast
  using le_fun_left_join by force
    
lemma le_fun_subset_sub: "\<lbrakk> \<forall> a a'. (a,a')\<in>set f1\<longrightarrow> (\<exists> b b'. (b,b')\<in>set f2 \<and> a\<mapsto>a' \<sqsubseteq> b\<mapsto>b') \<rbrakk>
   \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
proof (induction f1 arbitrary: f2)
  case Nil
  then show ?case by auto
next
  case (Cons aa f1')
  obtain a a' where aa: "aa = (a,a')" apply (cases aa) apply auto done
  have 2: "VFun f1' \<sqsubseteq> VFun f2"
  proof -
    have "\<forall>a a'.(a, a') \<in> set f1' \<longrightarrow> (\<exists>b b'.(b, b') \<in> set f2 \<and>
           a \<mapsto> a' \<sqsubseteq> b \<mapsto> b')" using Cons(2) apply auto done
    then show ?thesis using Cons.IH[of f2] by blast 
  qed
  have 3: "VFun [aa] \<sqsubseteq> VFun f2"
  proof -
    obtain b b' where bb_f2: "(b,b') \<in> set f2" and aa_bb: "a\<mapsto>a' \<sqsubseteq> b\<mapsto>b'"
      using Cons(2) aa apply simp apply blast done
    have "VFun [(b,b')] \<sqsubseteq> VFun f2" apply (rule le_fun_subset) using bb_f2 apply auto done
    then show ?thesis using aa_bb le_trans[of "a\<mapsto>a'" "b\<mapsto>b'" "VFun f2"] aa by simp 
  qed
  show "VFun (aa # f1') \<sqsubseteq> VFun f2"
  proof (cases "[aa] = f1'")
    case True
    then show ?thesis using 3 using le_fun_left_join by fastforce
  next
    case False
    then have 1: "VFun [aa] \<squnion> VFun f1' = Some (VFun (aa#f1'))" by simp
    show "VFun (aa # f1') \<sqsubseteq> VFun f2" using 1 2 3 le_left_join by blast
  qed
qed

proposition arrow_join: fixes A::val and B::val and C::val and D::val
  assumes ac: "A \<squnion> C = Some AC" and bd: "B \<squnion> D = Some BD"
  shows "VFun [(AC, BD)] \<sqsubseteq> VFun [(A,B),(C,D)]"
proof -
  have 1: "VFun [(AC,BD)] \<sqsubseteq> VFun [(AC,B),(AC,D)]" using bd by (simp add: le_distr)
  have 2: "VFun [(AC,B),(AC,D)] \<sqsubseteq> VFun [(A,B),(C,D)]" using ac 
    by (smt insert_iff le_arrow le_fun_subset_sub le_join_left le_join_right list.set(2) val_le.le_refl)
  show ?thesis using 1 2 le_trans[of "VFun [(AC,BD)]"] by auto
qed

lemma append_sub: fixes x::func shows "VFun (x @ x) \<sqsubseteq> VFun x"
  apply (induction x)
   apply force
  using le_fun_left_join by blast
    
lemma join_self: fixes C::val shows "\<exists> C'. C \<squnion> C = Some C' \<and> C' \<sqsubseteq> C"
  apply (induction C) apply force
  apply auto
  done

inductive_cases le_fun_one_two_inv: "C \<mapsto> D \<sqsubseteq> VFun [(A1,B1),(A2,B2)]"

fun join_list :: "val list \<Rightarrow> val option" ("\<Squnion>") where
  jl_none: "\<Squnion> [] = None" |
  jl_one: "\<Squnion> [v] = Some v" |
  jl_cons: "\<Squnion> (v#vs) = 
     (case \<Squnion> vs of
        None \<Rightarrow> None
     | Some v' \<Rightarrow> v \<squnion> v')" 

abbreviation equivalent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<approx>" 60) where
  "v \<approx> v' \<equiv> v \<sqsubseteq> v' \<and> v' \<sqsubseteq> v"
  
proposition join_sym: fixes v1::val assumes v12: "v1\<squnion>v2 = Some v12" and v21: "v2\<squnion>v1 = Some v21"
  shows "v12 \<approx> v21"
proof
  have 3: "v1 \<sqsubseteq> v21" using le_join_right v21 by blast
  have 4: "v2 \<sqsubseteq> v21" using le_join_left v21 by blast
  show "v12 \<sqsubseteq> v21" using le_left_join 3 4 v12 by blast
next
  have 1: "v1 \<sqsubseteq> v12" using le_join_left v12 by blast
  have 2: "v2 \<sqsubseteq> v12" using le_join_right v12 by blast  
  show "v21 \<sqsubseteq> v12" using 1 2 le_left_join v21 by blast
qed

proposition arrow_compatible: assumes aa: "a \<approx> a'" and bb: "b \<approx> b'" shows "a\<mapsto>b \<approx> a' \<mapsto> b'"
  by (simp add: aa bb le_arrow)

lemma join_env_nth: "\<lbrakk> \<rho>1 \<squnion> \<rho>2 = Some \<rho>3; x < length \<rho>1; length \<rho>1 = length \<rho>2 \<rbrakk>
                      \<Longrightarrow> \<rho>1 ! x \<squnion> \<rho>2 ! x = Some (\<rho>3 ! x)"
  apply (induction arbitrary: x \<rho>3 rule: env_join.induct)
  apply fastforce
  apply simp apply (case_tac "v \<squnion> v'") apply force apply simp
    apply (case_tac "\<rho> \<squnion> \<rho>'") apply force apply simp
    apply (case_tac x) apply force apply force
  apply force  
  apply force
  done 

lemma join_list_sub: "\<lbrakk> A \<in> set L; \<Squnion>L = Some B \<rbrakk> \<Longrightarrow> A \<sqsubseteq> B"
  apply (induction L arbitrary: A B)
  apply force
  apply simp apply (erule disjE)
  apply (case_tac L) apply force
    apply (case_tac "join_list L") apply auto
    apply (simp add: le_join_left)
  apply (case_tac L) apply force
    apply (case_tac "join_list L") apply auto
    apply (metis le_join_right val_le.le_trans)
    apply (meson le_join_right val_le.le_trans)
  done

lemma join_list_glb: "\<lbrakk> \<forall> A. A \<in> set L \<longrightarrow> A \<sqsubseteq> B; \<Squnion>L = Some As \<rbrakk> \<Longrightarrow> As \<sqsubseteq> B"
proof (induction L arbitrary: As)
  case Nil
  then show ?case by auto
next
  case (Cons A1 L') then have a1l_as: "\<Squnion> (A1 # L') = Some As" by blast
  show ?case
  proof (cases L')
    case Nil
    then show ?thesis using Cons by auto
  next
    case (Cons A2 L'')
    obtain As' where asp: "\<Squnion> L' = Some As'" 
      using Cons a1l_as by (case_tac "\<Squnion> (A2 # L'')") auto
    have as2: "A1 \<squnion> As' = Some As" using asp a1l_as Cons by simp
    have "\<forall>A. A \<in> set L' \<longrightarrow> A \<sqsubseteq> B" by (simp add: Cons.prems(1))
    then have asp_b: "As' \<sqsubseteq> B" using Cons.IH Cons(1) asp by blast
    have a1_b: "A1 \<sqsubseteq> B" by (simp add: Cons.prems(1))
    show ?thesis using as2 a1_b asp_b using le_left_join by blast
  qed
qed
  
lemma join_list_sub_glb: fixes B2s::val and B3s::val and L2::"val list"
  assumes b2s: "\<Squnion> L2 = Some B2s" and b3s: "\<Squnion> L3 = Some B3s"
    and P: "\<forall> B2. B2 \<in> set L2 \<longrightarrow> (\<exists> B3. B3 \<in> set L3 \<and> B2 \<sqsubseteq> B3)"
  shows "B2s \<sqsubseteq> B3s"
proof -
  have 1: "\<forall> B2. B2 \<in> set L2 \<longrightarrow> B2 \<sqsubseteq> B3s"
  proof clarify
    fix B2 assume b2_l2: "B2 \<in> set L2"
    obtain B3 where b3_l3: "B3 \<in> set L3" and b2_b3: "B2 \<sqsubseteq> B3" using P b2_l2 by blast
    have "B3 \<sqsubseteq> B3s" using join_list_sub[of B3 L3 B3s] b3_l3 b3s by blast
    then show "B2 \<sqsubseteq> B3s" using b2_b3 le_trans by blast
  qed  
  show "B2s \<sqsubseteq> B3s" using 1 b2s join_list_glb by blast
qed

lemma upper_bound_join: fixes v1::val and v2::val and v3::val 
  assumes v1_v3: "v1 \<sqsubseteq> v3" and v2_v3: "v2 \<sqsubseteq> v3"
  shows "\<exists> v12. v1 \<squnion> v2 = Some v12"
  using v1_v3 v2_v3 apply (case_tac v3) apply (case_tac v1) apply force
    apply force apply (case_tac v1) apply force apply (case_tac v2) apply force
    apply simp
  done

lemma uppper_bound_join_list:
  assumes ub: "\<forall> v. v \<in> set L \<longrightarrow> v \<sqsubseteq> v3" and ll: "0 < length L"
  shows "\<exists> Ls. \<Squnion>L = Some Ls \<and> Ls \<sqsubseteq> v3"
  using ub ll apply (induction L arbitrary: v3)  
   apply force
  apply simp
  apply (subgoal_tac "\<forall>v. v \<in> set L \<longrightarrow> v \<sqsubseteq> v3") prefer 2 apply blast
  apply (case_tac L)
   apply force
  apply (subgoal_tac " \<exists>Ls. \<Squnion> L = Some Ls \<and> Ls \<sqsubseteq> v3") prefer 2 apply blast
  apply (erule exE) apply (erule conjE)
  apply (subgoal_tac "a \<sqsubseteq> v3") prefer 2 apply force
  apply (subgoal_tac "\<exists> b. a \<squnion> Ls = Some b") prefer 2
  using upper_bound_join apply force
  apply (erule exE) apply simp
  using le_left_join by blast

lemma le_join: fixes v1::val and v2::val
  assumes v1_v2: "v1 \<sqsubseteq> v2" shows "\<exists> v12. v1 \<squnion> v2 = Some v12 \<and> v2 \<approx> v12"
  using v1_v2
  apply (induction rule: val_le.induct)
  -- "case le_refl"
  apply (case_tac v) apply force apply force
  -- "case le_trans" 
  apply (erule exE)+
  apply (subgoal_tac "v1 \<sqsubseteq> v3") prefer 2 using le_trans apply blast
  apply (subgoal_tac "\<exists> v13. v1 \<squnion> v3 = Some v13") prefer 2 
  using upper_bound_join apply blast
        apply (erule exE) apply (rule_tac x=v13 in exI) apply simp
  using le_join_right le_left_join apply blast
  -- "case le_bot"
  apply force
  -- "case le_fun_append_left"
  apply (metis (no_types, lifting) Values.vfun_join le_fun_append_left le_fun_append_right le_left_join val_le.le_refl)  
  -- "case le_fun_append_right"
  apply (metis (no_types, lifting) Values.vfun_join le_fun_append_right le_left_join val_le.le_refl)
  -- "case le_fun_left_join"
  apply (metis (no_types, lifting) Values.vfun_join le_fun_append_right le_fun_left_join val_le.le_trans)
  -- "case le_arrow"      
  apply (metis Values.vfun_join le_arrow le_fun_append_right le_fun_elt le_fun_left_join list.set_intros(1))
  -- "case le_distr"
  by (metis Values.vfun_join le_distr le_fun_append_right le_fun_left_join val_le.le_refl)    
    

end