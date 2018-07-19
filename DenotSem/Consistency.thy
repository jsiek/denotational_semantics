theory Consistency
  imports IntersectionTypes
begin

section "Consistency"

fun consistent :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "~" 52) where
  "(TNat n) ~ (TNat m) = (n = m)" |
  "(v1\<rightarrow>v1') ~ (TNat m) = False" |
  "(TNat n) ~ (v2\<rightarrow>v2') = False" | 
  "(v1\<rightarrow>v1') ~ (v2\<rightarrow>v2') = ((v1 ~ v2 \<and> v1' ~ v2') \<or> \<not> (v1 ~ v2))" |
  "(TNat n) ~ (v2 \<sqinter> v2') = (TNat n ~ v2 \<and> TNat n ~ v2')" |
  "(v1\<rightarrow>v1') ~ (v2 \<sqinter> v2') = ((v1\<rightarrow>v1') ~ v2 \<and> (v1\<rightarrow>v1') ~ v2')" |
  "(v1\<sqinter>v1') ~ (TNat n) = (v1 ~ TNat n \<and> v1' ~ TNat n)" |
  "(v1\<sqinter>v1') ~ (v2\<rightarrow>v2') = (v1 ~ (v2\<rightarrow>v2') \<and> v1' ~ (v2\<rightarrow>v2'))" |
  "(v1\<sqinter>v1') ~ (v2\<sqinter>v2') = (v1 ~ v2 \<and> v1 ~ v2' \<and> v1' ~ v2 \<and> v1' ~ v2')"
  
abbreviation consis_env :: "ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "consis_env \<rho> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho> \<longrightarrow> \<rho>!k ~ \<rho>'!k)"
  
text{*
  The following well-formedness condition ensures that functions are
  really functions (and not just relations) and it ensures that
  intersections are only used for functions, not numbers.
  *} 
  
inductive wf_ty :: "ty \<Rightarrow> bool" where
  nat_wf_ty[intro]: "wf_ty (TNat n)" |
  arrow_func[intro]: "\<lbrakk> wf_ty v; wf_ty v' \<rbrakk> \<Longrightarrow> wf_ty (v \<rightarrow> v')" |
  inter_func[intro]: "\<lbrakk> f1 ~ f2; wf_ty f1; wf_ty f2 \<rbrakk> \<Longrightarrow> wf_ty (f1 \<sqinter> f2)"

inductive_cases 
  wf_ty_arrow_inv[elim!]: "wf_ty (v \<rightarrow> v')" and 
  wf_ty_inter_inv[elim!]: "wf_ty (f \<sqinter> f')"
  
abbreviation wf_env :: "ty list \<Rightarrow> bool" where
  "wf_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> wf_ty (\<rho>!k)"

abbreviation env_sub :: "ty list \<Rightarrow> ty list \<Rightarrow> bool" (infix "<:" 52) where 
  "(\<rho>::ty list) <: \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k <: \<rho>'!k)"

abbreviation env_inter :: "ty list \<Rightarrow> ty list \<Rightarrow> ty list" (infix "\<sqinter>" 60) where
  "env_inter \<rho>1 \<rho>2 \<equiv> map (\<lambda>(A,B). A \<sqinter> B) (zip \<rho>1 \<rho>2)" 

lemma consis_env_inter: "\<lbrakk> consis_env \<rho>1 \<rho>2; k < length \<rho>1 \<rbrakk> \<Longrightarrow> (\<rho>1 \<sqinter> \<rho>2)!k = \<rho>1!k \<sqinter> \<rho>2!k"
  by auto
 
lemma inter_env_length: "\<lbrakk> consis_env \<rho>1 \<rho>2 \<rbrakk> \<Longrightarrow> length (\<rho>1 \<sqinter> \<rho>2) = length \<rho>1"
  by auto
    



    
(*
  
lemma consis_join_L_inv[elim!]: "\<lbrakk> v1\<sqinter>v2 ~ v; \<lbrakk> v1 ~ v; v2 ~ v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto
lemma consis_join_R_inv[elim!]: "\<lbrakk> v ~ v1\<sqinter>v2; \<lbrakk> v ~ v1; v ~ v2 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induction v arbitrary: v1 v2) auto
*)     

lemma consis_sym_aux: "(v ~ v' \<longrightarrow> v' ~ v) \<and> (\<not> v ~ v' \<longrightarrow> \<not> v' ~ v)"
  by (induction v v' rule: consistent.induct) auto
    
lemma consis_sym[sym]: "v ~ v' \<Longrightarrow> v' ~ v"
  using consis_sym_aux by blast
    
lemma consis_refl[intro!]: "wf_ty v \<Longrightarrow> v ~ v"
  apply (induction rule: wf_ty.induct) using consis_sym by auto

    
(*    
corollary consis_upper_bound: fixes v1::val and v2::val 
  assumes v1_v2: "v1 ~ v2" and v_v1: "wf_ty v1" and v_v2: "wf_ty v2"
  shows "\<exists> v3. v1 \<sqsubseteq> v3 \<and> v2 \<sqsubseteq> v3 \<and> wf_ty v3"
proof -
  obtain v12 where v12: "v1 \<sqinter> v2 = Some v12" and v_v12: "wf_ty v12" 
    using v1_v2 v_v1 v_v2 consis_join_val by blast
  have 1: "v1 \<sqsubseteq> v12" using v12 le_join_left by blast
  have 2: "v2 \<sqsubseteq> v12" using v12 le_join_right by blast
  show ?thesis using 1 2 v_v12 by blast
qed

lemma upper_bound_consis: fixes v1::val and v2::val and v3::val 
  assumes v1_v3: "v1 \<sqsubseteq> v3" and v2_v3: "v2 \<sqsubseteq> v3" and v_v3: "wf_ty v3"
  shows "v1 ~ v2"
  using v_v3 v1_v3 v2_v3 apply (induction arbitrary: v1 v2 rule: wf_ty.induct)
   apply (case_tac v1) apply (case_tac v2) apply force apply force
   apply (case_tac v2) apply force apply force
  apply (case_tac v1) apply (case_tac v2) apply force apply force
  apply (case_tac v2) apply force
  apply simp
  apply (rule vfun_consis) apply (rule allI)+ apply (rule impI) apply (erule conjE)
  oops      
*)
    
lemma atoms_inter_inv[elim!]: "\<lbrakk> v \<in> atoms (v1 \<sqinter> v2); v \<in> atoms v1 \<Longrightarrow> P; v \<in> atoms v2 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"  
  by auto 
    
lemma consis_arrow_inter_inv[elim!]: "\<lbrakk> v1 \<rightarrow> v1' ~ v2 \<sqinter> v2'; \<lbrakk> v1\<rightarrow>v1' ~ v2; v1\<rightarrow>v1' ~ v2' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto  
  
lemma consis_inter_arrow_inv[elim!]: "\<lbrakk> v1 \<sqinter> v1' ~ v2 \<rightarrow> v2'; \<lbrakk> v1~ v2 \<rightarrow> v2'; v1' ~ v2\<rightarrow>v2' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto  

lemma consis_inter_inter_inv[elim!]: "\<lbrakk> v1 \<sqinter> v1' ~ v2 \<sqinter> v2'; 
    \<lbrakk> v1 ~ v2; v1~v2'; v1' ~ v2; v1' ~ v2' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto  
    
lemma consis_atoms: "\<lbrakk> v1 ~ v2; v1' \<in> atoms v1; v2' \<in> atoms v2 \<rbrakk> \<Longrightarrow> v1' ~ v2'"
  apply (induction v1 v2 arbitrary: v1' v2' rule: consistent.induct)  
        apply force
       apply force
        apply force
       apply (metis atoms.simps(2) singletonD)
    apply (subgoal_tac "TNat n ~ v2 \<and> TNat n ~ v2'") prefer 2  using consistent.simps(5) apply blast
    apply blast
     apply (subgoal_tac "v1 \<rightarrow> v1' ~ v2 \<and> v1 \<rightarrow> v1' ~ v2'") prefer 2 apply blast
     apply blast
    apply (subgoal_tac "v1 ~ TNat n \<and> v1' ~ TNat n") prefer 2 
         using consistent.simps(7) apply blast
           apply blast
          apply blast
         apply blast
         done

lemma inconsis_atoms: "\<lbrakk> \<not> v1 ~ v2 \<rbrakk> \<Longrightarrow> \<exists> v1' v2'. v1' \<in> atoms v1 \<and> v2' \<in> atoms v2 \<and> \<not>v1'~v2'"
  by (induction v1 v2 rule: consistent.induct) auto
    
lemma atoms_consis: "\<forall> v1' v2'. v1' \<in> atoms v1 \<longrightarrow> v2' \<in> atoms v2 \<longrightarrow> v1' ~ v2' \<Longrightarrow> v1 ~ v2"
  by (induction v1 v2 rule: consistent.induct) auto    

lemma atoms_inconsis: "\<lbrakk> \<not>(v1' ~ v2'); v1' \<in> atoms v1; v2' \<in> atoms v2 \<rbrakk> \<Longrightarrow> \<not>(v1 ~ v2)"
  by (induction v1 v2 arbitrary: v1' v2' rule: consistent.induct) auto

(*
lemma consis_merge: "\<lbrakk> a ~ b; a ~ y; x ~ b; x ~ y \<rbrakk> \<Longrightarrow> merge a x ~ merge b y"
  apply (case_tac a) apply (case_tac b) apply auto apply (case_tac y) apply auto
    apply (case_tac x) apply auto apply (case_tac b) apply auto apply (case_tac b)
    apply auto
  done
*)
  
lemma consis_inter_L[intro!]: "\<lbrakk> v1 ~ v3; v2 ~ v3 \<rbrakk> \<Longrightarrow> v1 \<sqinter> v2 ~ v3"
  using atoms_consis consis_atoms by blast
    
lemma consis_inter_R[intro!]: "\<lbrakk> v1 ~ v2; v1 ~ v3 \<rbrakk> \<Longrightarrow> v1 ~ v2 \<sqinter> v3"
  using atoms_consis consis_atoms by blast
    
(*
lemma consis_merge_left: "\<lbrakk> a ~ v; x ~ v; wf_ty a; wf_ty x \<rbrakk> \<Longrightarrow> merge a x ~ v"
  apply (case_tac a) apply (case_tac v) apply auto apply (case_tac x) apply auto
   apply (case_tac v) apply auto apply (case_tac x) apply auto 
    apply (rule consis_inter_right) apply blast apply blast apply blast apply blast
   apply (case_tac x) apply force apply force apply simp 
   apply clarify apply (rule consis_inter_right) apply blast apply blast apply blast apply blast
  apply (case_tac v) apply force apply force apply simp
  apply (case_tac x) apply force apply simp apply clarify apply (rule conjI)
    apply (rule consis_inter_right) apply blast apply blast apply blast apply blast 
    apply (rule consis_inter_right) apply blast apply blast apply blast apply blast 
  apply (rule conjI)
    apply (rule consis_inter_right) apply blast apply blast apply blast apply blast 
  apply (rule conjI)
    apply (rule consis_inter_right) apply blast apply blast apply blast apply blast 
  apply clarify
  apply (rule conjI)
    apply (rule consis_inter_right) apply blast apply blast apply blast apply blast 
    apply (rule consis_inter_right) apply blast apply blast apply blast apply blast 
  done   

lemma consis_merge_right: "\<lbrakk> v ~ a; v ~ x; wf_ty a; wf_ty x \<rbrakk> \<Longrightarrow> v ~ merge a x"
  sorry

lemma consis_fold_merge_left: "\<forall> x y. (\<forall> v1 v2. {v1,v2} \<subseteq> set L1 \<longrightarrow> v1 ~ v2) \<longrightarrow>
        (\<forall> v. v \<in> set L1 \<longrightarrow> x ~ v) \<longrightarrow> (\<forall>v. v \<in> set L1 \<longrightarrow> v ~ y) \<longrightarrow>
        x ~ y \<longrightarrow> wf_ty x \<longrightarrow> wf_ty y \<longrightarrow>
       (\<forall>v. v \<in> set L1 \<longrightarrow> wf_ty v)  \<longrightarrow>
   fold merge L1 x ~ y" (is "\<forall> x y. ?P L1 x y")
proof (induction L1)
  case Nil
  then show ?case by auto
next
  case (Cons a L1') then have IH: "\<forall> x y. ?P L1' x y" .
  show ?case 
  proof clarify
    fix x y assume 1: "\<forall>v1 v2. {v1,v2} \<subseteq> set (a # L1') \<longrightarrow> v1 ~ v2" and
      2: "\<forall>v. v \<in> set (a # L1') \<longrightarrow> x ~ v" and
      3: "\<forall>v. v \<in> set (a # L1') \<longrightarrow> v ~ y" and
      x_y: "x ~ y" and wf_x: "wf_ty x" and wf_y: "wf_ty y" and 
      wf_L1p: "\<forall>v. v \<in> set (a # L1') \<longrightarrow> wf_ty v" 
    have IH_spec: "?P L1' (merge a x) y" using IH by blast        
    have wf_a: "wf_ty a" using wf_L1p by auto
    have "fold merge L1' (merge a x) ~ y"
    proof (rule IH_spec[rule_format])
      fix v1 v2 show "{v1, v2} \<subseteq> set L1' \<Longrightarrow> v1 ~ v2" using 1 by auto
    next fix v assume v_l1: "v \<in> set L1'"
      have a_v: "a ~ v" using 1 v_l1 by auto
      have x_v: "x ~ v" using 2 v_l1 by auto
      show "merge a x ~ v" using consis_merge_left wf_x wf_a a_v x_v by simp
    next fix v assume "v \<in> set L1'" then show "v ~ y" using 3 by auto
    next 
      have a_y: "a ~ y" using 3 by auto
      show "merge a x ~ y" using a_y x_y wf_a wf_x consis_merge_left by simp
    next
      show "wf_ty (merge a x)" using wf_a wf_x by (simp add: "2" consis_sym wf_merge)
    next show "wf_ty y" using wf_y .
    next fix v assume "v \<in> set L1'" then show "wf_ty v" using wf_L1p by auto      
    qed  
    then show "fold merge (a # L1') x ~ y" by simp
  qed
qed

lemma consis_fold_merge_right: "\<forall> x y. (\<forall> v1 v2. {v1,v2} \<subseteq> set L2 \<longrightarrow> v1 ~ v2) \<longrightarrow>
        (\<forall> v. v \<in> set L2 \<longrightarrow> x ~ v) \<longrightarrow> (\<forall>v. v \<in> set L2 \<longrightarrow> v ~ y) \<longrightarrow>
        x ~ y \<longrightarrow> wf_ty x \<longrightarrow> wf_ty y \<longrightarrow>
       (\<forall>v. v \<in> set L2 \<longrightarrow> wf_ty v)  \<longrightarrow>
   x ~ fold merge L2 y" (is "\<forall> x y. ?P L2 x y")
  sorry  
*)
(*
lemma consis_fold_merge: "\<forall> L2 x y. (\<forall> v1 v2. {v1,v2} \<subseteq> set L1 \<union> set L2 \<longrightarrow> v1 ~ v2) \<longrightarrow>
        (\<forall> v. v \<in> set L1 \<union> set L2 \<longrightarrow> x ~ v) \<longrightarrow> (\<forall>v. v \<in> set L1 \<union> set L2 \<longrightarrow> v ~ y) \<longrightarrow>
        x ~ y \<longrightarrow> wf_ty x \<longrightarrow> wf_ty y \<longrightarrow> 
       (\<forall>v. v \<in> set L1 \<longrightarrow> wf_ty v) \<and> (\<forall>v. v \<in> set L2 \<longrightarrow> wf_ty v) \<longrightarrow>
   fold merge L1 x ~ fold merge L2 y" (is "\<forall> L2 x y. ?P L1 L2 x y")
proof (induction L1)
  case Nil
  show ?case
  proof clarify
    fix L2 x y assume 1: "\<forall>v1 v2. {v1,v2} \<subseteq> set [] \<union> set L2 \<longrightarrow> v1 ~ v2" and
      2: "\<forall>v. v \<in> set [] \<union> set L2 \<longrightarrow> x ~ v" and
      3: "\<forall>v. v \<in> set [] \<union> set L2 \<longrightarrow> v ~ y" and
      x_y: "x ~ y" and wf_x: "wf_ty x" and wf_y: "wf_ty y" and 
      wf_L1p: "\<forall>v. v \<in> set [] \<longrightarrow> wf_ty v" and
      wf_L2: "\<forall>v. v \<in> set L2 \<longrightarrow> wf_ty v"     
    have "x ~ fold merge L2 y" 
      apply (rule consis_fold_merge_right[rule_format])
      using 1 2 3 x_y wf_x wf_y wf_L2 by auto        
    then show "fold merge [] x ~ fold merge L2 y" by simp
  qed    
next
  case (Cons a L1') then have IH: "\<forall> L2 x y. ?P L1' L2 x y" .
  show ?case
  proof clarify
    fix L2 x y assume 1: "\<forall>v1 v2. {v1,v2} \<subseteq> set (a # L1') \<union> set L2 \<longrightarrow> v1 ~ v2" and
      2: "\<forall>v. v \<in> set (a # L1') \<union> set L2 \<longrightarrow> x ~ v" and
      3: "\<forall>v. v \<in> set (a # L1') \<union> set L2 \<longrightarrow> v ~ y" and
      x_y: "x ~ y" and wf_x: "wf_ty x" and wf_y: "wf_ty y" and 
      wf_L1p: "\<forall>v. v \<in> set (a # L1') \<longrightarrow> wf_ty v" and
      wf_L2: "\<forall>v. v \<in> set L2 \<longrightarrow> wf_ty v" 
    show "fold merge (a # L1') x ~ fold merge L2 y" 
    proof (cases L2)
      case Nil
      show ?thesis 
        apply (rule consis_fold_merge_left[rule_format])
          using 1 2 Nil 3 x_y Nil wf_x Nil wf_y wf_L1p by auto
    next
      case (Cons b L2')
      from IH have IH_spec: "?P L1' L2' (merge a x) (merge b y)" by simp        
      have ax_by: "merge a x ~ merge b y" using 1 2 3 local.Cons x_y consis_merge by auto
      have 4: "\<forall>v1 v2. {v1,v2} \<subseteq> set L1' \<union> set L2' \<longrightarrow> v1 ~ v2" using 1 Cons by auto
      have 5: "\<forall>v. v \<in> set L1' \<union> set L2' \<longrightarrow> merge a x ~ v" 
        apply clarify
        apply (subgoal_tac "a ~ v") prefer 2 using 1 Cons apply force
        apply (subgoal_tac "x ~ v") prefer 2 using 2 Cons apply force
        apply (rule consis_merge_left) apply blast apply blast
        using wf_L1p apply simp
        using wf_x apply simp done 
      have 6: "\<forall>v. v \<in> set L1' \<union> set L2'\<longrightarrow> v ~ merge b y" 
          apply clarify 
          apply (subgoal_tac "v ~ b") prefer 2 using 1 Cons apply force
          apply (subgoal_tac "v ~ y") prefer 2 using 3 Cons apply force
        apply (rule consis_merge_right) apply blast apply blast
        using wf_L2 Cons apply simp
        using wf_y apply simp done 
      have 8: "wf_ty (merge a x)"
      proof -
        have wf_a: "wf_ty a" using wf_L1p by auto
        have a_x: "a ~ x" using 2 consis_sym[of x a] by simp  
        show ?thesis using wf_x wf_a a_x wf_merge[of a x] by simp
      qed
      have 9: "wf_ty (merge b y)"
      proof -
        have wf_b: "wf_ty b" using wf_L2 Cons by auto
        have b_y: "b ~ y" using 3 consis_sym[of y b] Cons by simp  
        show ?thesis using wf_y wf_b b_y wf_merge[of b y] by simp
      qed
      have 10: "\<forall>v. v \<in> set L1' \<longrightarrow> wf_ty v" using wf_L1p by simp
      have 11: "\<forall>v. v \<in> set L2' \<longrightarrow> wf_ty v" using wf_L2 Cons by simp
      have "fold merge L1' (merge a x) ~ fold merge L2' (merge b y)"
        using IH_spec 4 5 6 8 9 10 11 ax_by by blast          
      then show ?thesis using Cons by simp
    qed
  qed
qed
*)
    
(*
lemma consis_merge_list: 
  assumes c_l12: "\<forall> v1 v2. {v1,v2} \<subseteq> set L1 \<union> set L2 \<longrightarrow> v1 ~ v2" and
    wf_l1: "\<forall>v. v \<in> set L1 \<longrightarrow> wf_ty v" and
    wf_l2: "\<forall>v. v \<in> set L2 \<longrightarrow> wf_ty v" and
    l1_ne: "L1 \<noteq> []" and l2_ne: "L2 \<noteq> []" 
  shows "\<Prod> L1 ~ \<Prod> L2"
proof -
  obtain x L1' where l1: "L1 = x#L1'" using l1_ne by (cases L1) auto
  obtain y L2' where l2: "L2 = y#L2'" using l2_ne by (cases L2) auto
  have 1: "\<forall> v1 v2. {v1,v2} \<subseteq> set L1' \<union> set L2' \<longrightarrow> v1 ~ v2" using c_l12 l1 l2 by auto
  have 2: "\<forall> v. v \<in> set L1' \<union> set L2' \<longrightarrow> x ~ v" using c_l12 l1 l2 by auto
  have 3: "\<forall>v. v \<in> set L1' \<union> set L2' \<longrightarrow> v ~ y" using c_l12 l1 l2 by auto
  have 4: "x ~ y" using c_l12 l1 l2 by auto
  have 5: "wf_ty x" using l1 wf_l1 by auto
  have 6: "wf_ty y" using l2 wf_l2 by auto
  have 8: "\<forall>v. v \<in> set L1' \<longrightarrow> wf_ty v" using wf_l1 l1 by auto
  have 9: "\<forall>v. v \<in> set L2' \<longrightarrow> wf_ty v" using wf_l2 l2 by auto
  have "fold merge L1' x ~ fold merge L2' y"
    using consis_fold_merge 1 2 3 4 5 6 8 9 by blast
  then show ?thesis using l1 l2 merge_list_def by simp
qed 
*)
    
(*
lemma d_consis_nat_L: "\<lbrakk> \<Gamma> \<turnstile> c : v; \<Gamma> = [TNat n] \<rbrakk> \<Longrightarrow> v ~ TNat n"
  apply (induction \<Gamma> c v arbitrary: n rule: deduce_le.induct)
       apply (case_tac \<Gamma>1) apply force apply force
      apply (case_tac \<Gamma>1) apply force apply force
     apply force+
    apply (case_tac \<Gamma>1) apply force apply force
   apply force+
  done
*)

lemma nat_atoms_consis: "atoms v \<subseteq> {TNat n} \<Longrightarrow> v ~ TNat n"
  by (induction v) auto
    
lemma le_any_nat_consis[intro]: assumes n_v: "TNat n <: v" shows "v ~ TNat n"
proof -
  have "atoms v \<subseteq> {TNat n}" using n_v sub_any_nat_inv_atoms by blast
  then show "v ~ TNat n" using nat_atoms_consis by blast
qed
  
lemma consis_nat_atoms: "\<lbrakk> v ~ TNat n \<rbrakk> \<Longrightarrow> atoms v \<subseteq> { TNat n }"
  by (induction v arbitrary: n) auto

(*
  
(*
lemma le_any_nat_atom_consis: "\<lbrakk> v \<sqsubseteq> TNat n \<rbrakk> \<Longrightarrow> atoms v \<subseteq> {TNat n}"
  using le_any_nat_inv_atoms by blast
*)

definition consis :: "ty set \<Rightarrow> bool" where
  "consis \<Gamma> \<equiv> (\<forall>v v'. v \<in> \<Gamma> \<longrightarrow> v' \<in> \<Gamma> \<longrightarrow> v ~ v')"
  
*)
    
  
(*   
lemma val_consis_atoms: "wf_ty v \<Longrightarrow> consis (atoms v)"
  apply (induction v) apply auto
    apply (simp add: consis_def)
   apply (simp add: consis_def) apply blast
  apply (simp add: consis_def) apply clarify
  apply (rule conjI) apply clarify apply (erule_tac x=v in allE) apply (erule impE)
    apply blast using consis_atoms apply blast 
  apply clarify using consis_sym consis_atoms apply blast
  done
*)  
    
lemma consis_nat_trans: "\<lbrakk> v1 ~ TNat n; TNat n ~ v2 \<rbrakk> \<Longrightarrow> v1 ~ v2"
  by (induction v1 arbitrary: v2) auto

lemma consis_nat_trans2: "\<lbrakk> v1 ~ v2; v2 ~ TNat n \<rbrakk> \<Longrightarrow> v1 ~ TNat n"
  apply (induction v2 arbitrary: v1 n) 
    apply force
   apply force
  apply (case_tac v1)
  apply force
   apply force
  apply force
  done    
    
(*
definition vals :: "ty set \<Rightarrow> bool" where
  "vals \<Gamma> \<equiv> (\<forall>v. v \<in> \<Gamma> \<longrightarrow> wf_ty v)"
  
lemma nat_atom_consis_nat: "\<lbrakk>  TNat n \<in> atoms v; wf_ty v \<rbrakk> \<Longrightarrow> v ~ TNat n"
  apply (induction v arbitrary: n)
    apply force
   apply force
  apply simp apply clarify apply (erule disjE) 
   apply (rule conjI) apply force
    apply (subgoal_tac "v1 ~ TNat n") prefer 2 apply blast 
  using consis_nat_trans2 consis_sym apply blast
  apply (rule conjI) 
   apply (subgoal_tac "v2 ~ TNat n") prefer 2 apply blast
  using consis_nat_trans2 apply blast
  apply blast
  done    
  
lemma le_nat_any_consis[intro!]: assumes n_v: "v <: TNat n" and v_v: "wf_ty v" 
  shows "v ~ TNat n"
proof -
  obtain c where "[v] \<turnstile> c : TNat n" using n_v unfolding sub_ty_def by blast
  then obtain v' where
    vp_v: "v' \<in> (\<Union>v\<in>set [v]. atoms v)" and vp_n: "v' = TNat n"
    using d_nat_inv by presburger
  have "TNat n \<in> atoms v" using vp_v vp_n by simp
  with v_v show "v ~ TNat n" using nat_atom_consis_nat by blast
qed    
*)
 
lemma consis_inter_right_elim[elim!]: "\<lbrakk> A ~ A1 \<sqinter> A2; \<lbrakk> A ~ A1; A ~ A2 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using atoms_consis consis_atoms by blast

lemma consis_inter_left_elim[elim!]: "\<lbrakk> A1 \<sqinter> A2 ~ A; \<lbrakk> A1 ~ A; A2 ~ A \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using atoms_consis consis_atoms by (smt IntersectionTypes.atoms_union Un_iff)

lemma fold_meet_atoms[simp]: "atoms (fold op \<sqinter> L A) = atoms A \<union> ctx_atoms L"
  by (induction L arbitrary: A) auto
    
lemma meet_list_atoms[simp]: "L \<noteq> [] \<Longrightarrow> atoms (\<Sqinter>L) = ctx_atoms L"
  unfolding meet_list_def by (cases L) auto

lemma meet_list_right_consis_inv: "\<lbrakk> A ~ \<Sqinter>L2; B \<in> set L2; L2 \<noteq> [] \<rbrakk> \<Longrightarrow> A ~ B"
  using meet_list_atoms atoms_consis consis_atoms by (smt UN_I)

lemma meet_list_right_consis: "\<lbrakk> \<forall>B. B \<in> set L2 \<longrightarrow> A ~ B; L2 \<noteq> [] \<rbrakk> \<Longrightarrow> A ~ \<Sqinter>L2"
  using meet_list_atoms atoms_consis consis_atoms by (smt UN_E)
  
lemma meet_list_left_consis_inv: "\<lbrakk> \<Sqinter>L1 ~ B; A \<in> set L1; L1 \<noteq> [] \<rbrakk> \<Longrightarrow> A ~ B"
  using meet_list_atoms atoms_consis consis_atoms by (smt UN_I)

lemma meet_list_consis_inv: "\<lbrakk> \<Sqinter>L1 ~ \<Sqinter>L2; A \<in> set L1; B \<in> set L2; L1 \<noteq> []; L2 \<noteq> [] \<rbrakk> \<Longrightarrow> A ~ B"
  using meet_list_atoms atoms_consis consis_atoms by (smt UN_I)

lemma meet_list_inconsis_inv: "\<lbrakk> \<not> \<Sqinter>L1 ~ \<Sqinter>L2; L1 \<noteq> []; L2 \<noteq> [] \<rbrakk> \<Longrightarrow> 
   \<exists> A B. A \<in> set L1 \<and> B \<in> set L2 \<and> \<not> A ~ B"
  using meet_list_atoms atoms_inconsis inconsis_atoms by (smt UN_E)
    
lemma consis_le_inconsis_le:
  "(v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1' <: v1 \<and> v2' <: v2 \<longrightarrow> v1 ~ v2))
  \<and> (\<not> v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1 <: v1' \<and> v2 <: v2' \<longrightarrow> \<not> v1 ~ v2))"
  (is "?P v1' v2' \<and> ?Q v1' v2'")
proof (induction v1' v2' rule: consistent.induct)
  case (1 n m)
  show ?case
  proof
    show "?P (TNat n) (TNat m)" 
    proof clarify
      fix v1 v2 assume n_m: "TNat n ~ TNat m" and n_v1: "TNat n <: v1" and m_v2: "TNat m <: v2"
      have 1: "v1 ~ TNat n" using n_v1 by (simp add: le_any_nat_consis)
      have 2: "v2 ~ TNat m" using m_v2 by (simp add: le_any_nat_consis)
      show "v1 ~ v2" using 1 2 n_m using consis_nat_trans consis_sym by meson
    qed
  next
    show "?Q (TNat n) (TNat m)" apply (rule impI)+ apply (rule allI)+
      apply (rule impI) apply (erule conjE)
    proof -
      fix v1 v2 assume n_m: "\<not> (TNat n ~ TNat m)" and v1_n: "v1 <: TNat n" and v2_m: "v2 <: TNat m"
      have 1: "TNat n \<in> atoms v1" using v1_n sub_nat_any_inv_atoms by blast
      have 2: "TNat m \<in> atoms v2" using v2_m sub_nat_any_inv_atoms by blast
      show "\<not> (v1 ~ v2)" using n_m 1 2 atoms_inconsis by blast
    qed
  qed    
next
  case (2 v1 v1' m)
  show ?case
  proof
    show "?P (v1\<rightarrow>v1') (TNat m)" by auto
  next
    show "?Q (v1\<rightarrow>v1') (TNat m)"
    proof clarify
      fix v3 v4 assume "\<not> v1 \<rightarrow> v1' ~ TNat m" and v11_v3: "v3 <: v1 \<rightarrow> v1'" and
        m_v4: "v4 <: TNat m"
        and v3_v4: "v3 ~ v4"
      have m_v4: "TNat m \<in> atoms v4" using m_v4 sub_nat_any_inv_atoms by blast
      obtain v2 v2' where v22_v3: "v2\<rightarrow>v2' \<in> atoms v3" 
        using v11_v3 sub_fun_any_inv_atoms_ex by blast
      have "\<not> (TNat m ~ v2\<rightarrow>v2')" by simp
      then have "\<not> (v4 ~ v3)" using v22_v3 m_v4 atoms_inconsis by blast
      then show False using v3_v4 using consis_sym by blast
    qed      
  qed  
next
  case (3 n v2 v2')
  show ?case
  proof
    show "?P (TNat n) (v2\<rightarrow>v2')" by auto
  next
    show "?Q (TNat n) (v2\<rightarrow>v2')"
    proof clarify
      fix v3 v4 assume "\<not> TNat n ~ (v2\<rightarrow>v2')" and v11_v3: "v4 <: v2 \<rightarrow> v2'" and 
        m_v4: "v3 <: TNat n" and v3_v4: "v3 ~ v4"
      have m_v4: "TNat n \<in> atoms v3" using m_v4 sub_nat_any_inv_atoms by blast
      obtain v1 v1' where v22_v3: "v1\<rightarrow>v1' \<in> atoms v4" 
        using v11_v3 sub_fun_any_inv_atoms_ex by blast
      have "\<not> (TNat n ~ v1\<rightarrow>v1')" by simp
      then have "\<not> (v3 ~ v4)" using v22_v3 m_v4 atoms_inconsis by blast
      then show False using v3_v4 using consis_sym by blast
    qed      
  qed  
next
  case (4 v1 v1' v2 v2')
  show ?case
  proof
    show "?P (v1\<rightarrow>v1') (v2\<rightarrow>v2')"
    proof clarify
      fix v3 v4 assume v11_v22: "v1 \<rightarrow> v1' ~ v2 \<rightarrow> v2'" and v3_v11: "v1\<rightarrow>v1' <: v3" and 
        v4_v22: "v2\<rightarrow>v2' <: v4" 
      have v3_fun: "\<forall>v'. v' \<in> atoms v3 \<longrightarrow> (\<exists> A B. v' = A\<rightarrow>B \<and> A <: v1 \<and> v1' <: B)"
        using v3_v11 using sub_any_fun_inv_atoms by blast
      have v4_fun: "\<forall>v'. v' \<in> atoms v4 \<longrightarrow> (\<exists> A B. v' = A\<rightarrow>B \<and> A <: v2 \<and> v2' <: B)"
        using v4_v22 using sub_any_fun_inv_atoms by blast          
      have "(v1 ~ v2 \<and> v1' ~ v2') \<or> \<not>(v1 ~ v2)" using v11_v22 by simp
      then show "v3 ~ v4"
      proof
        assume v1_v2: "v1 ~ v2 \<and> v1' ~ v2'"
        have "\<forall>a3 a4. a3 \<in> atoms v3 \<longrightarrow> a4 \<in> atoms v4 \<longrightarrow> a3 ~ a4"
        proof clarify
          fix a3 a4 assume a3_v3: "a3 \<in> atoms v3" and a4_v4: "a4 \<in> atoms v4"
          obtain A3 B3 where a3: "a3=A3\<rightarrow>B3" and v1_A3: "A3 <: v1" and B3_v1: "v1' <: B3" 
            using v3_fun a3_v3 by blast
          obtain A4 B4 where a4: "a4=A4\<rightarrow>B4" and v2_A4: "A4 <: v2" and B4_v2: "v2' <: B4" 
            using v4_fun a4_v4 by blast
          show "a3 ~ a4"
          proof (cases "A3 ~ A4")
            case True
            have "B3 ~ B4" using 4 v1_v2 B3_v1 B4_v2 by blast
            then show ?thesis using True a3 a4 by simp
          next
            case False
            then show ?thesis using a3 a4 by simp
          qed
        qed
        then show ?thesis using atoms_consis by blast
      next
        assume v1_v2: "\<not>(v1 ~ v2)"
        have "\<forall>a3 a4. a3 \<in> atoms v3 \<longrightarrow> a4 \<in> atoms v4 \<longrightarrow> a3 ~ a4"
        proof clarify
          fix a3 a4 assume a3_v3: "a3 \<in> atoms v3" and a4_v4: "a4 \<in> atoms v4"
          obtain A3 B3 where a3: "a3=A3\<rightarrow>B3" and v1_A3: "A3 <: v1" and B3_v1: "v1' <: B3" 
            using v3_fun a3_v3 by blast
          obtain A4 B4 where a4: "a4=A4\<rightarrow>B4" and v2_A4: "A4 <: v2" and B4_v2: "v2' <: B4" 
            using v4_fun a4_v4 by blast
          have "\<not> A3 ~ A4" using v1_v2 4 v1_A3 v2_A4 by blast
          then show "a3 ~ a4" using a3 a4 by simp              
        qed
        then show ?thesis using atoms_consis by blast
      qed
    qed      
  next
    show "?Q (v1\<rightarrow>v1') (v2\<rightarrow>v2')"
      apply (rule impI) apply (rule allI)+ apply (rule impI) apply (erule conjE)
    proof -
      fix v3 v4 assume v11_v22: "\<not> v1 \<rightarrow> v1' ~ v2 \<rightarrow> v2'" and v11_v3: "v3 <: v1 \<rightarrow> v1'" and
        v22_v4: "v4 <: v2 \<rightarrow> v2'" 
      have v1_v2: "v1 ~ v2" and 
        not_v1p_v2p: "\<not> v1' ~ v2'" using v11_v22 by auto

      obtain \<Gamma>3 where g3_ne: "\<Gamma>3 \<noteq> []" and af_g3: "all_funs (set \<Gamma>3)" and g3_v3: "set \<Gamma>3 \<subseteq> atoms v3" and
        v1_g3: "v1 <: \<Sqinter>(map dom \<Gamma>3)" and g3_v1p: "\<Sqinter>(map cod \<Gamma>3) <: v1'" 
        using v11_v3 sub_any_fun_elim2 by blast
      obtain \<Gamma>4 where g4_ne: "\<Gamma>4 \<noteq> []" and af_g4: "all_funs (set \<Gamma>4)" and g4_v4: "set \<Gamma>4 \<subseteq> atoms v4" and
        v2_g4: "v2 <: \<Sqinter>(map dom \<Gamma>4)" and g4_v2p: "\<Sqinter>(map cod \<Gamma>4) <: v2'" 
        using v22_v4 sub_any_fun_elim2 by blast
      
      have c_dg3_dg4: "\<Sqinter>(map dom \<Gamma>3) ~ \<Sqinter>(map dom \<Gamma>4)" using v1_v2 v1_g3 v2_g4 4 by blast
      have nc_cg3_cg4: "\<not> \<Sqinter>(map cod \<Gamma>3) ~ \<Sqinter>(map cod \<Gamma>4)" using not_v1p_v2p g3_v1p g4_v2p 4 by blast 
      obtain C D where c_g3: "C \<in> set (map cod \<Gamma>3)" and d_g4: "D \<in> set (map cod \<Gamma>4)" and 
        c_d: "\<not> C ~ D" using nc_cg3_cg4 by(meson g3_ne g4_ne map_is_Nil_conv meet_list_inconsis_inv)
      obtain A where ac_g3: "A \<rightarrow> C \<in> set \<Gamma>3" using c_g3 af_g3 g3_v3 apply auto apply (case_tac x)
          apply auto done
      obtain B where bd_g4: "B \<rightarrow> D \<in> set \<Gamma>4" using d_g4 af_g4 apply auto apply (case_tac x)
          apply auto done         
      have a_b: "A ~ B" using c_dg3_dg4
        apply (rule meet_list_consis_inv)
        using ac_g3 apply force
        using bd_g4 apply force
          using g3_ne apply force using g4_ne apply force done
      have "\<not> A \<rightarrow> C ~ B \<rightarrow> D" using a_b c_d by simp
      then show "\<not> v3 ~ v4" 
        using g3_v3 g4_v4 ac_g3 bd_g4 atoms_inconsis[of "A\<rightarrow>C" "B\<rightarrow>D" v3 v4] by blast 
    qed      
  qed    
next
  case (5 n v2 v2')
  show ?case
  proof
    show "?P (TNat n) (v2 \<sqinter> v2')"   
      by (metis consis_nat_atoms sub_trans atoms_sub_any_nat consis_nat_trans 
          consis_sym le_any_nat_consis)
  next
    show "?Q (TNat n) (v2 \<sqinter> v2')" 
      by (metis (no_types, lifting) atoms.simps(1) atoms_consis atoms_sub_any_nat consis_atoms 
          consis_nat_atoms consis_sym le_any_nat_consis singletonD sub_nat_any_inv_atoms sub_trans)
  qed
next
  case (6 v1 v1' v2 v2')
  show ?case
  proof
    show "?P (v1 \<rightarrow> v1') (v2 \<sqinter> v2')"
    proof clarify
      fix v3 v4
      assume v11_v2: "v1 \<rightarrow> v1' ~ v2" and v11_v2p: "v1 \<rightarrow> v1' ~ v2'" and
        v11_v3: "v1 \<rightarrow> v1' <: v3" and v22_v4: "v2 \<sqinter> v2' <: v4"
      have v3a: "\<forall>a. a \<in> atoms v3 \<longrightarrow> (\<exists>a1 a2. a=a1\<rightarrow>a2 \<and> a1 <: v1 \<and> v1' <: a2)"
        using sub_any_fun_inv_atoms v11_v3 by blast
      
      have af_v2: "all_funs (atoms v2)" 
        apply clarify apply (subgoal_tac "v1\<rightarrow>v1' ~ v") prefer 2
        using v11_v2 consis_atoms[of "v1\<rightarrow>v1'" v2] apply force
        apply (case_tac v) apply auto done          
      have af_v2p: "all_funs (atoms v2')" 
        apply clarify apply (subgoal_tac "v1\<rightarrow>v1' ~ v") prefer 2
        using v11_v2p consis_atoms[of "v1\<rightarrow>v1'" v2'] apply force
        apply (case_tac v) apply auto done
          
      have af_v4: "all_funs (atoms v4)" using v22_v4 af_v2 af_v2p
        by (smt UN_E Un_iff atoms.simps(3) d_fun_atoms_L_inv list.set(1) list.set(2) singletonD sub_ty_def)
          
      show  "v3 ~ v4"
        apply (rule atoms_consis) apply clarify
      proof -
        fix v3' v4' assume v3p_v3: "v3' \<in> atoms v3" and v4p_v4: "v4' \<in> atoms v4"
        obtain v41 v42 where v4p: "v4'=v41\<rightarrow>v42" using af_v4 v4p_v4 
            apply (case_tac v4') apply auto done          
        obtain v31 v32 where v3p: "v3' = v31 \<rightarrow> v32" and 
          v31_v1: "v31 <: v1" and v1p_v32: "v1' <: v32" using v3a v3p_v3 by blast
        have v22_v4p: "v2 \<sqinter> v2' <: v41\<rightarrow>v42" using v4p v22_v4 v4p_v4 sub_atom_sub by blast
        
        obtain \<Gamma>2 where g2_ne: "\<Gamma>2 \<noteq> []" and af_g2: "all_funs (set \<Gamma>2)" and
          g2_v22: "set \<Gamma>2 \<subseteq> atoms (v2 \<sqinter> v2')" and
          v41_g2: "v41 <: \<Sqinter>(map dom \<Gamma>2)" and g2_v42: "\<Sqinter>(map cod \<Gamma>2) <: v42" 
          using v22_v4p sub_any_fun_elim2 by blast
            
        show "v3' ~ v4'"
        proof (cases "v31 ~ v41")
          case True
          have v1_dg2: "v1 ~ \<Sqinter>(map dom \<Gamma>2)"
            using v31_v1 v41_g2 sorry (* Need IH based on size *)
          then have g2_v1: "\<forall>B. B \<in> set (map dom \<Gamma>2) \<longrightarrow> v1 ~ B"
            using meet_list_right_consis_inv g2_ne by auto          
          have v1p_cg2: "v1' ~ \<Sqinter>(map cod \<Gamma>2)"
            apply (rule meet_list_right_consis) defer using g2_ne apply blast
            apply clarify
            apply (subgoal_tac "\<exists> x. x \<in> set \<Gamma>2 \<and> cod x = B") prefer 2 apply force apply (erule exE)
            using af_g2 apply (case_tac x) apply force prefer 2 apply force
            apply clarify apply simp
            apply (subgoal_tac "v1 \<rightarrow> v1' ~ x21 \<rightarrow> x22") prefer 2  
            using v11_v2 v11_v2p g2_v22 
            apply (metis IntersectionTypes.atoms_union Un_iff atoms.simps(2) atoms_consis consis_atoms singletonD subsetCE)
            using g2_v1 apply auto done
          then have v32_v42: "v32 ~ v42"
            using v1p_v32 g2_v42 sorry (* Need IH based on size *)
          then show ?thesis using True v3p v4p by simp
        next
          case False
          then show ?thesis using v3p v4p by simp
        qed
      qed
    qed      
  next
    show "?Q (v1 \<rightarrow> v1') (v2 \<sqinter> v2')" sorry
  qed    
next
  case (7 v1 v1' v2)
  show ?case
  proof
    show "?P (v1 \<sqinter> v1') (TNat v2)" 
      by (meson "7.IH"(1) atoms_nat_eq_nat consis_nat_atoms consistent.simps(7) sub_trans ty_equiv_def)
  next
    show "?Q (v1 \<sqinter> v1') (TNat v2)" 
      by (metis (no_types, lifting) atoms.simps(1) atoms_consis atoms_sub_any_nat consis_atoms consis_nat_atoms le_any_nat_consis singletonD sub_nat_any_inv_atoms sub_trans)
  qed
next
  case (8 v1 v1' v2 v2')
  show ?case
  proof
    show "?P (v1 \<sqinter> v1') (v2 \<rightarrow> v2')" sorry
  next
    show "?Q (v1 \<sqinter> v1') (v2 \<rightarrow> v2')" sorry
  qed
next
  case (9 v1 v1' v2 v2')
  show ?case
  proof
    show "?P (v1 \<sqinter> v1') (v2 \<sqinter> v2')" sorry
  next
    show "?Q (v1 \<sqinter> v1') (v2 \<sqinter> v2')" sorry
  qed    
oops

lemma size_atoms[simp]: "B \<in> atoms A \<Longrightarrow> size B \<le> size A"
  apply (induction A) apply auto done

fun depth :: "ty \<Rightarrow> nat" where
  "depth (TNat n) = 0" |
  "depth (A \<rightarrow> B) = Suc (max (depth A) (depth B))" |
  "depth (A \<sqinter> B) = max (depth A) (depth B)"

lemma atoms_depth: "A \<in> atoms B \<Longrightarrow> depth A \<le> depth B"
  apply (induction B arbitrary: A)
  apply force
   apply force
  apply force
  done

abbreviation list_depth :: "ty list \<Rightarrow> nat" where
  "list_depth ls \<equiv> (case ls of [] \<Rightarrow> 0
                    | A#ls \<Rightarrow> fold (\<lambda>a b. max (depth a) b) ls (depth A))"

lemma fold_depth_bounded: "\<lbrakk> (\<forall>A. A \<in> set L \<longrightarrow> depth A \<le> n); d \<le> n \<rbrakk> \<Longrightarrow> 
     fold (\<lambda>a b. max (depth a) b) L d \<le> n"
  apply (induction L arbitrary: d)
   apply force
  apply force
  done


lemma list_depth_bounded: "\<lbrakk> L \<noteq> []; \<forall>A. A \<in> set L \<longrightarrow> depth A \<le> n \<rbrakk> \<Longrightarrow> list_depth L \<le> n"
  apply (case_tac L) apply force
    apply simp
  apply (rule fold_depth_bounded)
   apply force
  apply force
  done
    
lemma fold_meet_depth: "depth (fold op \<sqinter> L A) = fold (\<lambda>a b. max (depth a) b) L (depth A)"
  apply (induction L arbitrary: A)
  apply force
  apply force
  done
    
lemma meet_list_depth: assumes l_ne: "L \<noteq> []" shows "depth (\<Sqinter> L) = list_depth L"
  using l_ne  apply (case_tac L) apply force apply (simp add: meet_list_def)
  apply (rule fold_meet_depth)
  done
    
lemma fold_depth_dom: "\<lbrakk> all_funs (set \<Gamma>); d1 < d2 \<rbrakk> \<Longrightarrow>
   fold (\<lambda>a b. max (depth a) b) (map dom \<Gamma>) d1
   < fold (\<lambda>a b. max (depth a) b) \<Gamma> d2"
  apply (induction \<Gamma> arbitrary: d1 d2)
   apply force
  apply (case_tac a) apply force defer apply force
  apply simp
  apply (subgoal_tac "max (depth x21) d1 < max (Suc (max (depth x21) (depth x22))) d2")
   prefer 2 apply force
  apply force
  done        
    
lemma list_depth_dom: "\<lbrakk> all_funs (set \<Gamma>); \<Gamma> \<noteq> [] \<rbrakk> \<Longrightarrow> list_depth (map dom \<Gamma>) < list_depth \<Gamma>"
  apply (case_tac \<Gamma>) apply force
  apply simp apply (case_tac a) apply force defer apply force apply simp
    using fold_depth_dom apply auto done
    
lemma depth_meet_list_dom:
  assumes g_a: "set \<Gamma> \<subseteq> atoms A" and af_g: "all_funs (set \<Gamma>)" and g_ne: "\<Gamma> \<noteq> []"
  shows "depth (\<Sqinter> (map dom \<Gamma>)) < depth A"
proof -
  have "list_depth (map dom \<Gamma>) < list_depth \<Gamma>" using af_g g_ne by (rule list_depth_dom)
  then have "depth (\<Sqinter>(map dom \<Gamma>)) < list_depth \<Gamma>" using meet_list_depth g_ne by auto
  also have "list_depth \<Gamma> \<le> depth A"
    apply (rule list_depth_bounded) using g_ne apply blast
    using g_a atoms_depth apply blast done
  finally show ?thesis by blast
qed

lemma consis_sub_aux: 
  "(\<forall> A B C D. n = depth A + depth B + depth C + depth D 
      \<longrightarrow> A ~ B \<longrightarrow> A <: C \<longrightarrow> B <: D \<longrightarrow> C ~ D)
  \<and> (\<forall> A B C D. n = depth A + depth B + depth C + depth D
      \<longrightarrow> \<not> A ~ B \<longrightarrow> C <: A \<longrightarrow> D <: B \<longrightarrow> \<not> C ~ D)"
    (is "?P n \<and> ?Q n")
proof (induction n rule: nat_less_induct)
  case (1 n)
  show ?case
  proof
    show "?P n"
    proof clarify
      fix A::ty and B::ty and C::ty and D::ty
      assume n: "n = depth A + depth B + depth C + depth D" and
        a_b: "A ~ B" and a_c: "A <: C" and b_d: "B <: D"
        
      show "C ~ D" apply (rule atoms_consis) apply clarify
      proof -
        fix C' D' assume cp_c: "C' \<in> atoms C" and dp_d: "D' \<in> atoms D"
        have a_cp: "A <: C'" using a_c cp_c using sub_atom_sub by blast
        have b_dp: "B <: D'" using b_d dp_d using sub_atom_sub by blast        
        show "C' ~ D'"
        proof (cases C')
          case (TNat n1)
          then have "TNat n1 \<in> atoms A" using a_cp
            by (simp add: sub_nat_any_inv_atoms)
          then have "atoms B \<subseteq> {TNat n1}" using a_b
            by (metis atoms.simps(1) atoms_consis consis_atoms consis_nat_atoms 
                consis_sym singletonD)
          then have "atoms D \<subseteq> {TNat n1}" using b_dp  
            by (meson atoms_sub_any_nat b_d sub_any_nat_inv_atoms sub_trans)
          then have "D' = TNat n1" using dp_d by auto
          then show ?thesis using TNat by simp
        next
          case (TArrow C1 C2)
          then obtain A1 A2 where "A1\<rightarrow>A2 \<in> atoms A" using a_cp sub_fun_any_inv_atoms_ex by blast
          then have "all_funs (atoms B)" 
            apply clarify apply (subgoal_tac "A1\<rightarrow>A2 ~ v") prefer 2
            using a_b consis_atoms[of A B "A1\<rightarrow>A2"] apply blast
            apply (case_tac v) apply auto done
          then have "is_fun D'" using b_d d_fun_atoms_L_inv dp_d 
            using sub_ty_def by fastforce
          then obtain D1 D2 where dp: "D' = D1 \<rightarrow> D2" apply (cases D') by auto
              
          have "A <: C1 \<rightarrow> C2" using a_cp TArrow by simp
          then show ?thesis
          proof (rule sub_any_fun_elim2)
            fix \<Gamma>a assume ga_ne: "\<Gamma>a \<noteq> []" and "all_funs (set \<Gamma>a)" and
              ga_a: "set \<Gamma>a \<subseteq> atoms A" and c1_dga: "C1 <: \<Sqinter> (map dom \<Gamma>a)" and
              cga_c2: "\<Sqinter> (map cod \<Gamma>a) <: C2" 
            have "B <: D1 \<rightarrow> D2" using b_dp dp by simp
            then show "C' ~ D'"
            proof (rule sub_any_fun_elim2)
              fix \<Gamma>b assume gb_ne: "\<Gamma>b \<noteq> []" and af_gb: "all_funs (set \<Gamma>b)" and 
                gb_b: "set \<Gamma>b \<subseteq> atoms B" and
                d1_dgb: "D1 <: \<Sqinter> (map dom \<Gamma>b)" and
                cgb_d2: "\<Sqinter> (map cod \<Gamma>b) <: D2"
              show "C' ~ D'"
              proof (cases "C1 ~ D1")
                case True
                have s_c1: "depth C1 < depth C" using cp_c TArrow atoms_depth[of C' C] by auto
                have s_d1: "depth D1 < depth D" using dp_d dp atoms_depth[of D' D] by auto
                have s_c2: "depth C2 < depth C" using cp_c TArrow atoms_depth[of C' C] by auto
                have s_d2: "depth D2 < depth D" using dp_d dp atoms_depth[of D' D] by auto
                have s_ga: "depth (\<Sqinter>(map dom \<Gamma>a)) < depth A" using ga_a sorry
                have s_gb: "depth (\<Sqinter>(map dom \<Gamma>b)) < depth B" using gb_b sorry
                have s_cga: "depth (\<Sqinter>(map cod \<Gamma>a)) < depth A" using ga_a sorry
                have s_cgb: "depth (\<Sqinter>(map cod \<Gamma>b)) < depth B" using gb_b sorry
                have "\<Sqinter>(map dom \<Gamma>a) ~ \<Sqinter>(map dom \<Gamma>b)"
                  using c1_dga d1_dgb True 1 s_c1 s_d1 s_ga s_gb n
                  apply (erule_tac x="depth (\<Sqinter>(map dom \<Gamma>a)) + depth (\<Sqinter>(map dom \<Gamma>b)) + depth C1 + depth D1" in allE)
                  apply (erule impE) apply force
                  apply blast done
                then have "\<Sqinter>(map cod \<Gamma>a) ~ \<Sqinter>(map cod \<Gamma>b)" using a_b ga_a gb_b sorry
                then have "C2 ~ D2" using cga_c2 cgb_d2 1 s_c2 s_d2 s_cga s_cgb n
                  apply (erule_tac x="depth (\<Sqinter>(map cod \<Gamma>a)) + depth (\<Sqinter>(map cod \<Gamma>b)) + depth C2 + depth D2" in allE)
                  apply (erule impE) apply force
                  apply blast done
                then show ?thesis using True TArrow dp by simp
              next
                case False
                then show ?thesis using TArrow dp by simp
              qed
            qed
          qed
        next
          case (TInter C1 C2)
          then have "False" using cp_c 
            by blast
          then show ?thesis ..
        qed
      qed
    qed
  next
    show "?Q n" sorry
  qed    
qed
    
  
  

lemma consis_le: "\<lbrakk> v1' <: v1; v2' <: v2; v1' ~ v2' \<rbrakk> \<Longrightarrow> v1 ~ v2"
  sorry
    
lemma inconsis_le: "\<lbrakk> v1 <: v1'; v2 <: v2'; \<not> v1' ~ v2' \<rbrakk> \<Longrightarrow> \<not> v1 ~ v2"
  sorry
(*    
lemma lookup_consis[intro]: "\<lbrakk> consis_env \<rho> \<rho>'; x < length \<rho> \<rbrakk> \<Longrightarrow> (\<rho>!x) ~ (\<rho>'!x)"
  by auto

lemma cons_wf_env_inv[elim!]: "\<lbrakk> wf_env (v#\<rho>); \<lbrakk> wf_ty v; wf_env \<rho> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by fastforce

lemma ext_wf_env[intro!]: "\<lbrakk> wf_ty v; wf_env \<rho> \<rbrakk> \<Longrightarrow> wf_env (v#\<rho>)"
   apply auto apply (case_tac k) apply auto done

abbreviation join_env :: "ty list \<Rightarrow> ty list \<Rightarrow> ty list" (infix "\<sqinter>" 55) where
  "\<rho> \<sqinter> \<rho>' \<equiv> map (\<lambda>(v,v'). v \<sqinter> v') (zip \<rho> \<rho>')"
    

    
lemma consis_env_length: "consis_env \<rho> \<rho>' \<Longrightarrow> length \<rho> = length \<rho>'"
  by auto

lemma join_env_length: "\<lbrakk> consis_env \<rho>1 \<rho>2 \<rbrakk> \<Longrightarrow> length (\<rho>1 \<sqinter> \<rho>2) = length \<rho>1"
  by auto
*)
    
lemma consis_env_wf_inter: fixes \<rho>1::"ty list" assumes r1_r2: "consis_env \<rho>1 \<rho>2" 
  and v_r1: "wf_env \<rho>1" and v_r2: "wf_env \<rho>2"
shows "wf_env (\<rho>1 \<sqinter> \<rho>2)" using r1_r2 v_r1 v_r2 
  apply simp
  apply (rule allI) apply (rule impI) 
  apply (subgoal_tac "\<rho>1!k ~ \<rho>2!k") prefer 2 apply force
  apply (subgoal_tac "wf_ty (\<rho>1!k)") prefer 2 apply simp
  apply (subgoal_tac "wf_ty (\<rho>2!k)") prefer 2 apply simp
  apply blast+
  done
 
lemma wf_atoms[intro]: "\<lbrakk> wf_ty B; A \<in> atoms B \<rbrakk> \<Longrightarrow> wf_ty A"
  by (induction B) auto   
    
lemma wf_consis_atoms: "\<lbrakk> wf_ty B; A \<in> atoms B; C \<in> atoms B \<rbrakk> \<Longrightarrow> A ~ C"
  apply (induction B)
    apply force
   apply force
    apply clarify 
  apply simp apply (erule disjE) apply (erule disjE) apply blast
  using consis_atoms apply blast
    apply (erule disjE) using consis_atoms consis_sym apply blast
  apply blast
  done    
    
end
