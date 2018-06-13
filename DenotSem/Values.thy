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
  
fun val_join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 56) where
  "VNat n1 \<squnion> VNat n2 = (if n1 = n2 then Some (VNat n1) else None)" |
  vfun_join: "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 @ f2))" |
  "v1 \<squnion> v2 = None"
  
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
  le_join_left: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v1 \<sqsubseteq> v12" (* incl_L *)| 
  le_join_right: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v2 \<sqsubseteq> v12" (* incl_R *) | 
  le_left_join: "\<lbrakk> v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3; v1 \<squnion> v2 = Some v12 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3" (* glb *) |
  le_arrow[intro!]: "\<lbrakk> v2 \<sqsubseteq> v1; v1' \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> v1 \<mapsto> v1' \<sqsubseteq> v2 \<mapsto> v2'" |
  le_distr: "(v1::val) \<squnion> v2 = Some v12 \<Longrightarrow> v\<mapsto>v12 \<sqsubseteq> VFun [(v,v1), (v,v2)]"

lemma le_fun_append_left: "VFun f1 \<sqsubseteq> VFun (f1@f2)"
  apply (subgoal_tac "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 @ f2))") prefer 2 apply simp
  apply (rule le_join_left) apply assumption done

lemma le_fun_append_right: "VFun f2 \<sqsubseteq> VFun (f1@f2)"
  apply (subgoal_tac "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 @ f2))") prefer 2 apply simp
  apply (rule le_join_right) apply assumption done
    
lemma le_fun_left_join: "\<lbrakk> VFun f1 \<sqsubseteq> VFun f3; VFun f2 \<sqsubseteq> VFun f3 \<rbrakk> \<Longrightarrow> VFun (f1@f2) \<sqsubseteq> VFun f3"
  apply (subgoal_tac "VFun f1 \<squnion> VFun f2 = Some (VFun (f1 @ f2))") prefer 2 apply simp
  apply (rule le_left_join) prefer 3 apply assumption+ done
    
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

lemma le_bot_inv_aux: fixes v1::val and f1::func
  assumes v12: "v1 \<sqsubseteq> v2" and v2b: "v2 = \<bottom>"
  shows "v1 = \<bottom>"
  using v12 v2b apply (induction rule: val_le.induct)
   apply auto
   apply (case_tac v1) apply (case_tac v2) apply auto
    apply (case_tac "x1=x1a") apply auto apply (case_tac v2) apply auto
   apply (case_tac v1) apply (case_tac v2) apply auto
    apply (case_tac "x1=x1a") apply auto apply (case_tac v2) apply auto
  done    

lemma le_bot_inv[elim!]: "\<lbrakk> f \<sqsubseteq> \<bottom>; f = \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  using le_bot_inv_aux by auto      
    
lemma le_any_nat_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v' = VNat n\<rbrakk> \<Longrightarrow> v = VNat n"
  apply (induction rule: val_le.induct)
         apply force
        apply force
  apply force
      apply (case_tac v1) apply (case_tac v2) apply simp apply (case_tac "x1=x1a") apply force
        apply force apply force apply (case_tac v2) apply force apply force 
     apply (case_tac v1) apply (case_tac v2) apply simp  apply (case_tac "x1=x1a") apply force
       apply force apply force apply simp apply (case_tac v2) apply force apply force
    apply force
   apply force
  apply force
  done
    
proposition le_any_nat_inv[elim!]: "\<lbrakk> v \<sqsubseteq> VNat n; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_any_nat_inv_aux[of v "VNat n" n] apply auto done
  
lemma le_nat_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VNat n\<rbrakk> \<Longrightarrow> v' = VNat n"
  apply (induction arbitrary: n rule: val_le.induct)
         apply force
        apply force
  apply force
      apply (case_tac v1) apply (case_tac v2) apply simp apply (case_tac "x1=x1a") apply force
        apply force apply force apply (case_tac v2) apply force apply force 
     apply (case_tac v1) apply (case_tac v2) apply simp apply (case_tac "x1=n") apply force
       apply force apply force apply simp apply (case_tac v2) apply force
    apply simp apply (case_tac v1) apply auto
  done
    
proposition le_nat_any_inv[elim!]: "\<lbrakk> VNat n \<sqsubseteq> v; \<lbrakk> v = VNat n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_nat_any_inv_aux[of "VNat n" v n] apply auto done    

lemma le_fun_any_inv_aux: "\<lbrakk> v \<sqsubseteq> v'; v = VFun f \<rbrakk> \<Longrightarrow> \<exists> f'. v' = VFun f'"
  apply (induction arbitrary: f rule: val_le.induct)
         apply auto
    apply (case_tac v2) apply auto apply (case_tac v1) apply auto
  apply (case_tac v1) apply (case_tac v2) apply auto
  done
  
proposition le_fun_any_inv: "\<lbrakk> VFun f \<sqsubseteq> v; \<And>f'. v = VFun f' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using le_fun_any_inv_aux by blast

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

lemma le_fun_elt: assumes v1f: "(v,v') \<in> set f" shows "v\<mapsto>v' \<sqsubseteq> VFun f"
  using v1f apply (induction f)
   apply force
  apply simp apply (erule disjE)
   apply simp
   apply (subgoal_tac "VFun [a] \<squnion> VFun f = Some (VFun (a#f))")
    prefer 2 apply force
   apply (rule le_join_left) apply assumption
  apply simp
  apply (subgoal_tac "VFun [a] \<squnion> VFun f = Some (VFun (a#f))")
   prefer 2 apply force
  apply (subgoal_tac "VFun [a] \<squnion> VFun [(v,v')] = Some (VFun [a,(v,v')])")
    prefer 2 apply force
    apply (subgoal_tac "v \<mapsto> v' \<sqsubseteq> VFun [a,(v,v')]") prefer 2
   apply (rule le_join_right) apply blast
  apply (subgoal_tac "VFun [a,(v,v')] \<sqsubseteq> VFun (a#f)") prefer 2
   apply (rule mon) prefer 3 apply assumption apply blast apply blast apply force
  apply (rule le_trans) apply auto
    done
 
lemma le_fun_subset: fixes f1::func shows "\<lbrakk> set f1 \<subseteq> set f2 \<rbrakk> \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
  apply (induction f1)
  apply force
  apply simp apply clarify
  apply (subgoal_tac "a\<mapsto>b \<sqsubseteq> VFun f2") prefer 2 apply (rule le_fun_elt) apply blast
  apply (subgoal_tac "a\<mapsto>b \<squnion> VFun f1 = Some (VFun ((a, b) # f1))") prefer 2 apply force
  using le_left_join by blast      
    
lemma le_fun_subset_sub: "\<lbrakk> \<forall> a a'. (a,a')\<in>set f1\<longrightarrow> (\<exists> b b'. (b,b')\<in>set f2 \<and> a\<mapsto>a' \<sqsubseteq> b\<mapsto>b') \<rbrakk>
   \<Longrightarrow> VFun f1 \<sqsubseteq> VFun f2"
proof (induction f1 arbitrary: f2)
  case Nil
  then show ?case by auto
next
  case (Cons aa f1')
  obtain a a' where aa: "aa = (a,a')" apply (cases aa) apply auto done
  have 1: "VFun [aa] \<squnion> VFun f1' = Some (VFun (aa#f1'))" by simp
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
  show "VFun (aa # f1') \<sqsubseteq> VFun f2" using 1 2 3 le_left_join by blast
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
  apply auto apply (rule append_sub) 
  done

inductive_cases le_fun_one_two_inv: "C \<mapsto> D \<sqsubseteq> VFun [(A1,B1),(A2,B2)]"

(*
theorem beta_sound_binary: fixes A1::val and A2::val and B1::val and B2::val 
  assumes cd_ab: "CD \<sqsubseteq> AB" and cd: "CD = C\<mapsto>D" and ab: "(A1\<mapsto>B1)\<squnion>(A2\<mapsto>B2) = Some AB"
  shows "(A1 \<sqsubseteq> C \<and> D \<sqsubseteq> B1) \<or> (A2 \<sqsubseteq> C \<and> D \<sqsubseteq> B2 ) 
      \<or> (\<exists>A3 B3. A3 \<sqsubseteq> C \<and> A1 \<squnion> A2 = Some A3 \<and> D \<sqsubseteq> B3 \<and> B1 \<squnion> B2 = Some B3)"
 using cd_ab cd ab 
proof (induction rule: val_le.induct)
  case (le_refl v)
  then show ?case by auto
next
  case (le_trans v1 v2 v3)
  then show ?case sorry
next
  case (le_bot f)
  then show ?case sorry
next
  case (le_join_left v1 v2 v12)
  then show ?case sorry
next
  case (le_join_right v1 v2 v12)
  then show ?case sorry
next
  case (le_left_join v1 v3 v2 v12)
  then show ?case sorry
next
  case (le_arrow v2 v1 v1' v2')
  then show ?case sorry
next
  case (le_distr v1 v2 v12 v)
  then show ?case sorry
qed
  *)    
(*  
  apply simp
  apply (subgoal_tac "VFun [(C,D)] \<sqsubseteq> VFun [(A1,B1),(A2,B2)]") prefer 2 apply fastforce
  apply (erule le_fun_fun_inv) apply (erule le_single_cons_right_inv)
  apply (metis Pair_inject le_cons_left_single_inv le_fun_bot_inv not_Cons_self2)
  apply (metis Pair_inject le_fun_bot_inv le_single_both_inv list.simps(3))  
  apply simp
  apply (rule disjI2) apply (rule disjI2)
  apply clarify
    apply (subgoal_tac "\<exists> C'. C \<squnion> C = Some C' \<and> C' \<sqsubseteq> C") apply (erule exE)
   apply (rule_tac x="C'" in exI) apply (rule conjI) apply blast
   apply (rule conjI) apply blast
   apply (rule_tac x=D in exI) apply force
    using join_self apply blast
  done
*)
    
fun select :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" where
  "select xs [] = []" |
  "select xs (i#I) = (xs!i)#(select xs I)"

fun join_list :: "val list \<Rightarrow> val option" ("\<Squnion>") where
  jl_none: "\<Squnion> [] = None" |
  jl_one: "\<Squnion> [v] = Some v" |
  jl_cons: "\<Squnion> (v#vs) = 
     (case \<Squnion> vs of
        None \<Rightarrow> None
     | Some v' \<Rightarrow> v \<squnion> v')" 
 
lemma select_append_map[simp]: "select (f1 @ f2) (map (\<lambda>i. i+length f1) I) = select f2 I"
  apply (induction I) apply fastforce by (simp add: nth_append)

lemma select_cons_map[simp]: "select (a#f2) (map Suc I) = select f2 I"
  using select_append_map[of "[a]" f2] by fastforce 

lemma nth_sub: "i < length f \<Longrightarrow> VFun [f!i] \<sqsubseteq> VFun f"
  apply (cases "f!i") apply simp using le_fun_elt nth_mem by fastforce

theorem join_select_sub:
  assumes a: "\<Squnion> (map fst (select f I)) = Some A" and
      b: "\<Squnion> (map snd (select f I)) = Some B"
      and li: "0 < length I" and in_f: "\<forall> i \<in> set I. i < length f"
    shows "VFun [(A,B)] \<sqsubseteq> VFun f"
  using a b li in_f
proof (induction I arbitrary: A B)
  case Nil
  then have "False" by auto then show ?case ..
next
  case (Cons i I')
  show ?case
  proof (cases I')
    case Nil
    then show ?thesis using Cons apply simp apply (case_tac "f!i") apply clarify
      using nth_sub[of i f] apply auto done
  next
    fix i' I'' assume ip: "I' = i' # I''"
    have lip: "0 < length I'" using ip by simp
    have in_f: "\<forall>i\<in>set I'. i < length f" using Cons ip by auto
    obtain A' where ap: "\<Squnion> (map fst (select f I')) = Some A'" 
      using Cons ip by (case_tac "\<Squnion> (map fst (select f I'))") auto 
    obtain B' where bp: "\<Squnion> (map snd (select f I')) = Some B'" 
      using Cons ip by (case_tac "\<Squnion> (map snd (select f I'))") auto 
    obtain fi1 fi2 where fi: "f!i = (fi1,fi2)" by (cases "f!i") blast
    obtain C D where fi: "f!i = (C,D)" by (cases "f!i") auto
    have a: "C \<squnion> A' = Some A" using Cons.prems(1) ap ip fi by auto
    have b: "D \<squnion> B' = Some B" using Cons.prems(2) bp ip fi by auto
    have "VFun [f!i] \<sqsubseteq> VFun f" using Cons nth_sub by auto
    then have cd_f: "VFun [(C,D)] \<sqsubseteq> VFun f" using fi by simp
    have ap_bp_f: "VFun [(A', B')] \<sqsubseteq> VFun f" using Cons.IH ap bp lip in_f by auto
    have 1: "VFun [(C,D),(A',B')] \<sqsubseteq> VFun f" using cd_f ap_bp_f le_fun_append_left 
      by (metis append_Cons append_Nil val_join.simps(2) val_le.intros(6))
    have 2: "VFun [(A,B)] \<sqsubseteq> VFun [(C,D),(A',B')]" using arrow_join a b by simp   
    show "VFun [(A, B)] \<sqsubseteq> VFun f" 
      using 2 1 le_trans[of "VFun [(A,B)]" "VFun [(C,D),(A',B')]"] by simp 
  qed
qed

lemma mem_nth: "x \<in> set ls \<Longrightarrow> \<exists> i. ls!i = x \<and> i < length ls"
  apply (induction ls)
  apply force
  apply simp apply (erule disjE) apply simp
  apply (rule_tac x=0 in exI) apply force
  apply simp apply (erule exE) apply (rule_tac x="Suc i" in exI) apply force
  done

lemma select_mem: "\<lbrakk> x \<in> set (select f I); \<forall>i\<in>set I. i < length f \<rbrakk> \<Longrightarrow> x \<in> set f"
  apply (induction I)
   apply force
  apply simp apply (erule disjE) apply force apply force
  done

theorem beta_sound_aux:
  "\<lbrakk> v1 \<sqsubseteq> v2; v1 = VFun f1; v2 = VFun f2 \<rbrakk> \<Longrightarrow>
    \<forall> C D. (C,D) \<in> set f1 \<longrightarrow> (\<exists> I A B.
       0 < length I \<and> (\<forall>i\<in>set I. i < length f2) \<and> \<Squnion> (map fst (select f2 I)) = Some A
      \<and> \<Squnion> (map snd (select f2 I)) = Some B \<and> C\<mapsto>D \<sqsubseteq> A\<mapsto>B)"  
proof (induction arbitrary: f1 f2 rule: val_le.induct)
  case (le_refl v)
  then show ?case 
    apply simp apply clarify
    apply (subgoal_tac "\<exists>i. f1!i = (C,D) \<and> i < length f1")
      prefer 2 apply (rule mem_nth) apply assumption
    apply (erule exE) apply (rule_tac x="[i]" in exI) apply (rule conjI) apply blast
    apply simp apply auto done      
next
  case (le_trans v1 v2 v3 f1 f3)
  obtain f2 where v2: "v2 = VFun f2" using le_trans by (meson le_fun_any_inv)
  show ?case apply clarify
  proof -
    fix C D assume cd_f1: "(C,D) \<in> set f1"
    obtain I A B where li: "0 < length I" and li_f2: "\<forall>i\<in>set I. i < length f2" and
      a: "\<Squnion> (map fst (select f2 I)) = Some A" and
      b: "\<Squnion> (map snd (select f2 I)) = Some B" and
      cd_ab: "C \<mapsto> D \<sqsubseteq> A \<mapsto> B" using le_trans.IH(1)[of f1 f2] le_trans.prems v2 cd_f1 by blast
    
    have 1: "\<forall>C D. (C, D) \<in> set f2 \<longrightarrow>
          (\<exists>I A B. 0 < length I \<and> (\<forall>i\<in>set I. i < length f3) \<and>
              \<Squnion> (map fst (select f3 I)) = Some A \<and>
              \<Squnion> (map snd (select f3 I)) = Some B \<and>
              C \<mapsto> D \<sqsubseteq> A \<mapsto> B)" using le_trans.IH(2)[of f2 f3] le_trans.prems v2 by blast
    
    have "\<forall> x \<in> set (select f2 I). x \<in> set f2" by (meson li_f2 select_mem)
    then have "\<forall> (X,Y) \<in> set (select f2 I). (X,Y) \<in> set f2" by auto
    then have "\<forall>C D. (C, D) \<in> set (select f2 I) \<longrightarrow>
          (\<exists>I A B. 0 < length I \<and> (\<forall>i\<in>set I. i < length f3) \<and>
              \<Squnion> (map fst (select f3 I)) = Some A \<and>
              \<Squnion> (map snd (select f3 I)) = Some B \<and>
              C \<mapsto> D \<sqsubseteq> A \<mapsto> B)" using 1 apply blast done
        
    show "\<exists>I A B. 0 < length I \<and> (\<forall>i\<in>set I. i < length f3) \<and>
          \<Squnion> (map fst (select f3 I)) = Some A \<and>
          \<Squnion> (map snd (select f3 I)) = Some B \<and>
          C \<mapsto> D \<sqsubseteq> A \<mapsto> B" sorry
  qed
next
  case (le_bot f)
  then show ?case sorry
next
  case (le_join_left v1 v2 v12)
  then show ?case sorry
next
  case (le_join_right v1 v2 v12)
  then show ?case sorry
next
  case (le_left_join v1 v3 v2 v12)
  then show ?case sorry
next
  case (le_arrow v2 v1 v1' v2')
  then show ?case sorry
next
  case (le_distr v1 v2 v12 v)
  then show ?case sorry
qed

(*    
theorem beta_sound: fixes C::val and D::val and f::func 
  assumes cd_f: "C\<mapsto>D \<sqsubseteq> VFun f"
  shows "\<exists> I A B. 0 < length I \<and> join_list (map fst (select f I)) = Some A \<and> A \<sqsubseteq> C
                           \<and> join_list (map snd (select f I)) = Some B \<and> D \<sqsubseteq> B"
  using cd_f 
proof (induction f)
  case Nil
  then show ?case by auto
next
  case (Cons a f)
  have "[(C, D)] \<sqsubseteq> a # f " using Cons(2) by (meson le_fun_fun_inv)
  then show ?case
  proof (rule le_single_cons_right_inv)
    assume "[(C, D)] \<sqsubseteq> [a]"
    then show ?thesis
      apply (case_tac a)
      apply (rule_tac x="[0]" in exI)
      apply simp 
      apply (metis (no_types, lifting) fst_conv le_fun_bot_inv le_single_cons_right_inv not_Cons_self2 sndI)
      done
  next
    assume "[(C, D)] \<sqsubseteq> f"
    then show ?thesis using Cons
      apply (subgoal_tac "\<exists>I A B. 0 < length I \<and>
           join_list (map fst (select f I)) = Some A \<and> A \<sqsubseteq> C \<and>
           join_list (map snd (select f I)) = Some B \<and> D \<sqsubseteq> B") prefer 2 apply force
      apply (erule exE)+ apply (erule conjE)+
      apply (rule_tac x="map Suc I" in exI) apply (rule_tac x=A in exI)
      apply (rule_tac x=B in exI) apply (rule conjI) apply fastforce apply (rule conjI)
       apply (subgoal_tac "select (a # f) (map Suc I) = select f I") prefer 2 apply fastforce
       apply fastforce apply force
      done
  next
    fix v2::val and v1 and v1'::val and v2'
    assume "(C, D) = (v1, v1')" and "v2 \<sqsubseteq> v1" and "v1' \<sqsubseteq> v2'" and "a = (v2, v2')"
      and "f = []"
    then show ?thesis using Cons apply (rule_tac x="[0]" in exI) 
      apply clarify apply (rule_tac x=v2 in exI) apply (rule_tac x=v2' in exI)
      apply simp done
  next
    fix v1::val and v2 v12 v assume cd: "(C, D) = (v, v12)" and v12: "v1 \<squnion> v2 = Some v12" and
      a: "a = (v, v1)" and f: "f = [(v, v2)]"
    then show ?thesis using Cons.prems
      apply (rule_tac x="[0,1]" in exI) apply auto
      apply (subgoal_tac "\<exists> v'. v \<squnion> v = Some v' \<and> v' \<sqsubseteq> v") prefer 2 using join_self apply blast
      apply (erule exE) apply blast done
  qed    
qed
*)

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

section "Consistency"

inductive consistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 52) and
    inconsistent :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "!~" 52) where
  vnat_consis[intro!]: "(VNat n) ~ (VNat n)" |
  vfun_consis[intro!]: "\<lbrakk> \<forall> v1 v1' v2 v2'. (v1,v1') \<in> set f1 \<and> (v2,v2') \<in> set f2 \<longrightarrow>
                        (v1 ~ v2 \<and> v1' ~ v2') \<or> v1 !~ v2 \<rbrakk> \<Longrightarrow> (VFun f1) ~ (VFun f2)" |
  vnat_inconsis[intro!]: "n \<noteq> n' \<Longrightarrow> (VNat n) !~ (VNat n')" |
  vfun_inconsis[intro!]: "\<lbrakk> (v1, v1') \<in> set f1; (v2, v2') \<in> set f2; v1 ~ v2; v1' !~ v2' \<rbrakk> 
                         \<Longrightarrow> (VFun f1) !~ (VFun f2)" |
  vnat_vfun_inconsis[intro!]: "VNat n !~ VFun f" |
  vfun_vnat_inconsis[intro!]: "VFun f !~ VNat n"

inductive_cases 
  vnat_consis_inv[elim!]: "VNat n ~ VNat n'" and
  vfun_consis_inv[elim!]: "VFun f ~ VFun f'" and
  vnat_inconsis_inv[elim!]: "VNat n !~ VNat n'" and
  vfun_inconsis_inv[elim!]: "VFun f !~ VFun f'" and
  vnat_vfun_consis_inv[elim!]: "VNat n ~ VFun f" and
  vfun_vnat_consis_inv[elim!]: "VFun f ~ VNat n"
  
inductive consis_env :: "val list \<Rightarrow> val list \<Rightarrow> bool" where
  consis_env_nil[intro!]: "consis_env [] []" |
  consis_env_cons[intro!]: "\<lbrakk> v ~ v'; consis_env \<rho> \<rho>' \<rbrakk> \<Longrightarrow> consis_env (v#\<rho>) (v'#\<rho>')" 

definition is_fun :: "func \<Rightarrow> bool" where
  "is_fun f \<equiv> VFun f ~ VFun f"
    
inductive is_val :: "val \<Rightarrow> bool" where
  vnat_is_val[intro!]: "is_val (VNat n)" |
  vfun_is_val[intro!]: "\<lbrakk> is_fun f; \<forall> v v'. (v,v') \<in> set f \<longrightarrow> is_val v \<and> is_val v' \<rbrakk>
                        \<Longrightarrow> is_val (VFun f)"
inductive_cases
  vfun_is_val_inv[elim!]: "is_val (VFun f)"

definition val_env :: "val list \<Rightarrow> bool" where
  "val_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> is_val (\<rho>!k)"

definition env_le :: "val list \<Rightarrow> val list \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "(\<rho>::val list) \<sqsubseteq> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k \<sqsubseteq> \<rho>'!k)" 
    
lemma consis_and_not_consis: "(v ~ v' \<longrightarrow> \<not> (v !~ v')) \<and> (v !~ v' \<longrightarrow> \<not>(v ~ v'))"
  by (induction rule: consistent_inconsistent.induct) blast+ 
        
lemma consis_or_not_aux: "\<forall> v v'. n = vsize v \<longrightarrow> v ~ v' \<or> v !~ v'"
 apply (induction n rule: nat_less_induct)
 apply (rule allI)+ apply (rule impI)
 apply (case_tac v)    
  apply (case_tac v')
    apply force
   apply force
  apply (case_tac v')
   apply force
  apply simp
  apply auto
    apply (metis add_lessD1 less_SucI size_fun_mem)
    apply (metis add_lessD1 less_SucI size_fun_mem)
    apply (metis add_lessD1 less_SucI size_fun_mem)
  by (metis add.commute add_lessD1 less_SucI size_fun_mem)    
    
lemma consis_or_not: "v ~ v' \<or> v !~ v'"
  using consis_or_not_aux by blast
  
lemma inconsis_not_consis[simp]: "(v1 !~ v2) = (\<not> (v1 ~ v2))"
  using consis_and_not_consis consis_or_not by blast
  
lemma consis_refl[intro!]: "is_val v \<Longrightarrow> v ~ v"
  apply (induction rule: is_val.induct)
  apply blast
  apply (simp only: is_fun_def)
  done

lemma consis_inconsis_sym: "(v ~ v' \<longrightarrow> v' ~ v) \<and> (v !~ v' \<longrightarrow> \<not>(v' ~ v))"
  apply (induction rule: consistent_inconsistent.induct) 
  apply blast
  using consis_or_not apply blast
  apply blast    
  using consis_and_not_consis apply blast
  apply blast    
  apply blast    
  done
    
lemma consis_sym[sym]: "v ~ v' \<Longrightarrow> v' ~ v"
  using consis_inconsis_sym by blast

lemma consis_join_val:
  assumes v1_v2: "v1 ~ v2" and v_v1: "is_val v1" and v_v2: "is_val v2"
  shows "\<exists> v12. (v1 \<squnion> v2) = Some v12 \<and> is_val v12"
proof (cases v1)
  case (VNat n1) then have v1: "v1 = VNat n1" .
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    show ?thesis using v1 VNat v1_v2 by auto
  next
    case (VFun f2)
    have "False" using v1_v2 v1 VFun by auto 
    then show ?thesis ..
  qed
next
  case (VFun f1) then have v1: "v1 = VFun f1" .
  show ?thesis
  proof (cases v2)
    case (VNat n2)
    show ?thesis using v1 VNat v1_v2 by auto
  next
    case (VFun f2)
    let ?v12 = "VFun (f1@f2)"
    have j12: "v1 \<squnion> v2 = Some ?v12" using v1 VFun by simp
    have v_v12: "is_val ?v12"
      apply (rule vfun_is_val)
       apply (simp only: is_fun_def)
       apply (rule vfun_consis) 
       apply (metis (mono_tags, lifting) Un_iff VFun consis_refl consis_sym set_append v1 v1_v2 v_v1 v_v2 vfun_consis_inv)
      using v_v1 v_v2 using VFun v1 apply auto
      done
    show ?thesis using j12 v_v12 by blast
  qed
qed

lemma consis_le_inconsis_le:
  "(v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1 \<sqsubseteq> v1' \<and> v2 \<sqsubseteq> v2' \<longrightarrow> v1 ~ v2))
  \<and> (v1' !~ v2' \<longrightarrow> (\<forall> v1 v2. v1' \<sqsubseteq> v1 \<and> v2' \<sqsubseteq> v2 \<longrightarrow> v1 !~ v2))"
proof (induction rule: consistent_inconsistent.induct)
  case (vnat_consis n)
  then show ?case by blast
next
  case (vfun_consis f1 f2)
  show ?case 
  proof clarify
    fix v1 v2 assume v1_f1: "v1 \<sqsubseteq> VFun f1" and v2_f2: "v2 \<sqsubseteq> VFun f2"
    (* Need beta sound or something *)
    show "v1 ~ v2" sorry
  qed
next
  case (vnat_inconsis n n')
  then show ?case by blast
next
  case (vfun_inconsis v1 v1' f1 v2 v2' f2)
  then show ?case sorry
next
  case (vnat_vfun_inconsis n f)
  then show ?case apply clarify apply (erule le_fun_any_inv) apply blast done
next
  case (vfun_vnat_inconsis f n)
  then show ?case apply clarify apply (erule le_fun_any_inv) apply blast done
qed
    (*
  apply (induction rule: consistent_inconsistent.induct)
  apply blast
  defer
  apply blast
  defer
  apply blast
  apply blast

  apply (rule allI)+
  apply (rule impI) apply (erule conjE)
  apply (case_tac v1) apply force
  apply (case_tac v2) apply force
  apply simp apply (rule vfun_consis)
  apply (rule allI)+ apply (rule impI) apply (erule conjE)

  apply (erule le_fun_fun_inv)+
   apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f1 \<and> u \<sqsubseteq> v1a \<and> v1' \<sqsubseteq> u'")
   prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
   apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f2 \<and> u \<sqsubseteq> v2a \<and> v2' \<sqsubseteq> u'")
   prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption

   apply (erule exE)+
   apply (erule conjE)+
    
   apply (erule_tac x=u in allE)    
   apply (erule_tac x=u' in allE)    
   apply (erule_tac x=ua in allE)    
   apply (erule_tac x=u'a in allE)    

  apply (erule impE) apply force
  apply (erule disjE)
    apply force
  apply (rule disjI2)
    apply force 
    
  apply (rule allI)+
  apply (rule impI) apply (erule conjE)
  apply (case_tac v1a) apply force 
  apply (case_tac v2a) apply force
  apply clarify
  
  apply (subgoal_tac "\<exists> u u'. (u,u') \<in> set f2a \<and> u \<sqsubseteq> v1 \<and> v1' \<sqsubseteq> u'")
  prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
  apply (subgoal_tac "\<exists> v v'. (v,v') \<in> set f2b \<and> v \<sqsubseteq> v2 \<and> v2' \<sqsubseteq> v'")
  prefer 2 apply (rule le_fun_sub_pair) apply assumption apply assumption
  apply (erule exE)+ apply (erule conjE)+
  apply (rule vfun_inconsis) apply assumption apply assumption
  apply auto   
  done
*)
    
lemma consis_le: "\<lbrakk> v1 \<sqsubseteq> v1'; v2 \<sqsubseteq> v2'; v1' ~ v2' \<rbrakk> \<Longrightarrow> v1 ~ v2"
  using consis_le_inconsis_le by blast

lemma inconsis_le: "\<lbrakk> v1' \<sqsubseteq> v1; v2' \<sqsubseteq> v2; v1' !~ v2' \<rbrakk> \<Longrightarrow> v1 !~ v2"
  using consis_le_inconsis_le by blast
  
lemma lookup_consis[intro]: "\<lbrakk> consis_env \<rho> \<rho>'; x < length \<rho> \<rbrakk>
  \<Longrightarrow> (\<rho>!x) ~ (\<rho>'!x)"
  apply (induction arbitrary: x rule: consis_env.induct)
   apply force
  apply (case_tac x) apply force apply auto
  done

lemma cons_val_env_inv[elim!]:
  "\<lbrakk> val_env (v#\<rho>); \<lbrakk> is_val v; val_env \<rho> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    unfolding val_env_def by fastforce

lemma ext_val_env[intro!]: "\<lbrakk> is_val v; val_env \<rho> \<rbrakk> \<Longrightarrow> val_env (v#\<rho>)"
  unfolding val_env_def apply auto apply (case_tac k) apply auto done
      
lemma consis_env_join: fixes \<rho>1::"val list" assumes r1_r2: "consis_env \<rho>1 \<rho>2" 
  and v_r1: "val_env \<rho>1" and v_r2: "val_env \<rho>2"
  shows "\<exists> \<rho>3. \<rho>1 \<squnion> \<rho>2 = Some \<rho>3 \<and> val_env \<rho>3"
  using r1_r2 v_r1 v_r2 apply (induction rule: consis_env.induct)
   apply (rule_tac x="[]" in exI) apply force
   apply (erule cons_val_env_inv)
  apply (erule cons_val_env_inv)
   apply (subgoal_tac "\<exists>\<rho>3. \<rho> \<squnion> \<rho>' = Some \<rho>3 \<and> val_env \<rho>3") prefer 2 apply blast
  apply (subgoal_tac "\<exists> v3. v \<squnion> v' = Some v3 \<and> is_val v3")
    prefer 2 using consis_join_val apply blast
  apply (erule exE)+ apply (erule conjE)+
  apply (rule_tac x="v3#\<rho>3" in exI) 
  apply (rule conjI) apply fastforce
  apply blast
  done
    
lemma consis_env_length: "consis_env \<rho> \<rho>' \<Longrightarrow> length \<rho> = length \<rho>'"
  apply (induction rule: consis_env.induct) apply auto done
     
lemma join_env_length: "\<lbrakk> consis_env \<rho>1 \<rho>2; \<rho>1 \<squnion> \<rho>2 = Some \<rho>3  \<rbrakk> \<Longrightarrow> length \<rho>3 = length \<rho>1"
  apply (induction arbitrary: \<rho>3 rule: consis_env.induct)
   apply fastforce
  apply simp
  apply (case_tac "v \<squnion> v'") apply auto
  apply (case_tac "\<rho> \<squnion> \<rho>'") apply auto
  done
    
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
    
lemma mem_select: "\<lbrakk> i \<in> set I \<rbrakk> \<Longrightarrow> f!i \<in> set (select f I)"
  by (induction I) auto
    
(* This version follows Alessi et al. 2005 *)
lemma beta_sound_aux2:
    "\<lbrakk> (v1::val) \<sqsubseteq> v2; v1 = VFun f1; v2 = VFun f2; (A1,B1) \<in> set f1;
       \<Squnion> (map snd [(A2, B2)\<leftarrow>f2 . A2 \<sqsubseteq> A1]) = Some B2s \<rbrakk> \<Longrightarrow> B1 \<sqsubseteq> B2s" 
proof (induction arbitrary: f1 f2 A1 B1 B2s rule: val_le.induct)
  case (le_refl v)
  let ?L = "map snd [(A,B)\<leftarrow>f1.  A \<sqsubseteq> A1]"
  have "B1 \<in> set ?L" using le_refl apply (subgoal_tac "A1 \<sqsubseteq> A1") prefer 2 apply blast
      apply force done
  then show "B1 \<sqsubseteq> B2s" using le_refl join_list_sub[of B1 ?L] by force 
next
  case (le_trans v1 v2 v3 f1 f3 A1 B1 B3s)
  obtain f2 where v2: "v2 = VFun f2" using le_trans(1) le_trans(5) 
    using le_fun_any_inv by blast
  let ?L3 = "\<lambda> A2. map snd [(A3,B3)\<leftarrow>f3. A3 \<sqsubseteq> A2]"
  have IH2: "\<And> A2 B2 B3. \<lbrakk> (A2, B2) \<in> set f2; \<Squnion>(?L3 A2) = Some B3 \<rbrakk> \<Longrightarrow>
    B2 \<sqsubseteq> B3" using le_trans.IH(2)[of f2 f3] v2 le_trans(6) by blast

  let ?L2 = "map snd [(A2,B2)\<leftarrow>f2. A2 \<sqsubseteq> A1]"
  obtain B2s where b2: "\<Squnion> ?L2 = Some B2s" sorry
  (* Need to require is_val to get self consistency *)
  from le_trans.IH(1)[of f1 f2] le_trans(5) v2 le_trans(7) le_trans(8) b2
  have d_b2: "B1 \<sqsubseteq> B2s" by blast
 
  have b3s: "\<Squnion> (?L3 A1) = Some B3s" using le_trans by blast
      
  have b2_b3: "B2s \<sqsubseteq> B3s"
  proof -
    have 1: "\<forall> B2. B2 \<in> set ?L2 \<longrightarrow> B2 \<sqsubseteq> B3s"
    proof clarify
      fix B2 assume b2_l2: "B2 \<in> set ?L2"
      obtain A2 where a2b2_f2: "(A2,B2) \<in> set f2" and a1_a2: "A2 \<sqsubseteq> A1" using b2_l2 by auto
      obtain B3s' where b3sp: "\<Squnion> (?L3 A2) = Some B3s'" sorry
      have b3sp_b3s: "B3s' \<sqsubseteq> B3s"
      proof -
        have all3s: "\<forall>B3. B3 \<in> set (?L3 A2) \<longrightarrow> B3 \<sqsubseteq> B3s"
        proof clarify
          fix B3 assume b3_l3: "B3 \<in> set (?L3 A2)"
          obtain A3 where a3b3_f3: "(A3,B3) \<in> set f3" and a2_a3: "A3 \<sqsubseteq> A2" using b3_l3 by auto
          have "A3 \<sqsubseteq> A1" using a1_a2 a2_a3 Values.le_trans by blast
          then have "B3 \<in> set (?L3 A1)" using a3b3_f3 by force
          then show "B3 \<sqsubseteq> B3s" using b3s join_list_sub by blast
        qed
        show ?thesis using join_list_glb[of "?L3 A2" B3s B3s'] b3sp all3s by blast
      qed
      have "B2 \<sqsubseteq> B3s'" using IH2[of A2 B2 B3s'] a2b2_f2 b3sp by blast
      then show "B2 \<sqsubseteq> B3s" using b3sp_b3s Values.le_trans by blast
    qed
    show ?thesis using 1 b2 join_list_glb by blast
  qed
  show ?case using d_b2 b2_b3 Values.le_trans[of B1 B2s B3s] by blast
next
  case (le_bot f)
  then show ?case by auto
next
  case (le_join_left v1 v2 v12 f1 f12)
  obtain f2 where v2: "v2 = VFun f2" and f12: "f12 = f1@f2"
    using le_join_left apply (cases v2) apply auto done
  let ?L12 = "map snd [(A2,B2)\<leftarrow>f12. A2 \<sqsubseteq> A1]"
  have "(A1,B1) \<in> set f12" using le_join_left f12 by auto
  then have "B1 \<in> set ?L12" by force 
  then show "B1 \<sqsubseteq> B2s" using join_list_sub le_join_left(5) by blast
next
  case (le_join_right v1 v2 v12 f2 f12)
  obtain f1 where v2: "v2 = VFun f2" and f12: "f12 = f1@f2"
    using le_join_right apply (cases v1) apply auto done
  let ?L12 = "map snd [(A2,B2)\<leftarrow>f12. A2 \<sqsubseteq> A1]"
  have "(A1,B1) \<in> set f12" using le_join_right f12 by auto
  then have "B1 \<in> set ?L12" by force       
  then show "B1 \<sqsubseteq> B2s" using join_list_sub le_join_right(5) by blast
next
  case (le_left_join v1 v3 v2 v12 f12 f3 A12 B12 B3s)
  obtain f1 where v1: "v1 = VFun f1" using le_left_join by (case_tac v1) auto 
  obtain f2 where v2: "v2 = VFun f2" using le_left_join by (case_tac v2) auto
  have v3: "v3 = VFun f3" using le_left_join.prems by blast
  have b3s: "\<Squnion> (map snd [(A3,B3)\<leftarrow>f3. A3 \<sqsubseteq> A12]) = Some B3s" 
    using le_left_join.prems(4) by auto   
  have "(A12, B12) \<in> set (f1@f2)" using v1 v2 le_left_join by force
  then show "B12 \<sqsubseteq> B3s" apply simp
  proof (erule disjE)
    assume ab12_f1: "(A12, B12) \<in> set f1"
    show ?thesis using le_left_join.IH(1)[of f1 f3 A12 B12 B3s] v1 v3 ab12_f1 b3s by blast
  next
    assume ab12_f2: "(A12, B12) \<in> set f2"
    show ?thesis using le_left_join.IH(2)[of f2 f3 A12 B12 B3s] v2 v3 ab12_f2 b3s by blast
  qed
next
  case (le_arrow v2 v1 v1' v2')
  have f1: "f1 = [(v1, v1')]" using le_arrow by blast
  have f2: "f2 = [(v2, v2')]" using le_arrow by blast
  have a1b1_f1: "(A1, B1) \<in> set f1" using le_arrow by blast
  have a1: "A1 = v1" using f1 a1b1_f1 by auto 
  have b1: "B1 = v1'" using f1 a1b1_f1 by auto
  let ?L2 = "map snd [(A2,B2)\<leftarrow>f2 . A2 \<sqsubseteq> v1]" 
  have b2s: "\<Squnion> ?L2 = Some B2s" using le_arrow a1 by force
  have "v2' \<in> set ?L2" using le_arrow(1) f2 by auto
  then have "v2' \<sqsubseteq> B2s" using b2s join_list_sub[of v2' ?L2 B2s] by blast 
  then show "B1 \<sqsubseteq> B2s" using le_arrow(2) b1 le_trans by blast
next
  case (le_distr v1 v2 v12 v)
  have b2s_v12: "B2s = v12" using le_distr le_refl by auto
  have b1_v12: "B1 = v12" using le_distr by auto    
  show "B1 \<sqsubseteq> B2s" using b1_v12 b2s_v12 le_refl by simp
qed


    
end