theory Consistency
  imports IntersectionTypes
begin

section "Consistency"

fun consistent :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "~" 52) where
  "(TNat n) ~ (TNat m) = (n = m)" |
  "(v1\<rightarrow>v1') ~ (TNat m) = False" |
  "(TNat n) ~ (v2\<rightarrow>v2') = False" | 
  "(v1\<rightarrow>v1') ~ (v2\<rightarrow>v2') = ((v1 ~ v2 \<and> v1' ~ v2') \<or> \<not> (v1 ~ v2))" |
  "(TNat n) ~ (v2 \<sqinter> v2') = False" |
  "(v1\<rightarrow>v1') ~ (v2 \<sqinter> v2') = ((v1\<rightarrow>v1') ~ v2 \<and> (v1\<rightarrow>v1') ~ v2')" |
  "(v1\<sqinter>v1') ~ (TNat n) = False" |
  "(v1\<sqinter>v1') ~ (v2\<rightarrow>v2') = (v1 ~ (v2\<rightarrow>v2') \<and> v1' ~ (v2\<rightarrow>v2'))" |
  "(v1\<sqinter>v1') ~ (v2\<sqinter>v2') = (v1 ~ v2 \<and> v1 ~ v2' \<and> v1' ~ v2 \<and> v1' ~ v2')"
  
abbreviation consis_env :: "ty list \<Rightarrow> ty list \<Rightarrow> bool" where
  "consis_env \<rho> \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho> \<longrightarrow> \<rho>!k ~ \<rho>'!k)"
  
text{*
  The following well-formedness condition ensures that functions are
  really functions (and not just relations) and it ensures that
  intersections are only used for functions, not numbers.
  *} 
  
inductive wf_ty :: "ty \<Rightarrow> bool" and wf_fun :: "ty \<Rightarrow> bool" where
  nat_wf_ty[intro]: "wf_ty (TNat n)" |
  fun_wf_ty[intro]: "\<lbrakk> wf_fun f \<rbrakk> \<Longrightarrow> wf_ty f" |
  arrow_func[intro]: "\<lbrakk> wf_ty v; wf_ty v' \<rbrakk> \<Longrightarrow> wf_fun (v \<rightarrow> v')" |
  inter_func[intro]: "\<lbrakk> f1 ~ f2; wf_fun f1; wf_fun f2 \<rbrakk> \<Longrightarrow> wf_fun (f1 \<sqinter> f2)"

inductive_cases 
  wf_ty_arrow_inv[elim!]: "wf_ty (v \<rightarrow> v')" and 
  wf_ty_inter_inv[elim!]: "wf_ty (f \<sqinter> f')" and
  wf_arrow_inv[elim!]: "wf_fun (v \<rightarrow> v')" and 
  wf_inter_inv[elim!]: "wf_fun (f \<sqinter> f')" and
  wf_fun_nat_inv[elim!]: "wf_fun (TNat n)" and
  wf_fun_inv: "wf_fun f"
  
abbreviation wf_env :: "ty list \<Rightarrow> bool" where
  "wf_env \<rho> \<equiv> \<forall>k. k < length \<rho> \<longrightarrow> wf_ty (\<rho>!k)"

abbreviation env_sub :: "ty list \<Rightarrow> ty list \<Rightarrow> bool" (infix "<:" 52) where 
  "(\<rho>::ty list) <: \<rho>' \<equiv> length \<rho> = length \<rho>' \<and> (\<forall> k. k < length \<rho>  \<longrightarrow> \<rho>!k <: \<rho>'!k)"

fun merge :: "ty \<Rightarrow> ty \<Rightarrow> ty" where
  "merge (TNat n1) (TNat n2) = (if n1 = n2 then TNat n1 else undefined)" |
  "merge f1 f2 = f1 \<sqinter> f2"
  
definition merge_list :: "ty list \<Rightarrow> ty" ("\<Prod>" 1000) where
  "\<Prod> xs \<equiv> (case xs of [] \<Rightarrow> undefined | x#xs' \<Rightarrow> fold merge xs' x)"

abbreviation env_inter :: "ty list \<Rightarrow> ty list \<Rightarrow> ty list" (infix "\<sqinter>" 60) where
  "env_inter \<rho>1 \<rho>2 \<equiv> map (\<lambda>(A,B). merge A B) (zip \<rho>1 \<rho>2)" 

lemma consis_env_inter: "\<lbrakk> consis_env \<rho>1 \<rho>2; k < length \<rho>1 \<rbrakk> \<Longrightarrow> (\<rho>1 \<sqinter> \<rho>2)!k = merge (\<rho>1!k) (\<rho>2!k)"
  by auto
 
lemma inter_env_length: "\<lbrakk> consis_env \<rho>1 \<rho>2 \<rbrakk> \<Longrightarrow> length (\<rho>1 \<sqinter> \<rho>2) = length \<rho>1"
  by auto
    
(*
lemma consis_join_R[intro!]: "\<lbrakk> v1 ~ v2; v1 ~ v3 \<rbrakk> \<Longrightarrow> v1 ~ v2 \<sqinter> v3"
  by (induction v1) auto

lemma consis_join_L[intro!]: "\<lbrakk> v1 ~ v3; v2 ~ v3 \<rbrakk> \<Longrightarrow> v1 \<sqinter> v2 ~ v3"
  by auto  
  
lemma consis_join_L_inv[elim!]: "\<lbrakk> v1\<sqinter>v2 ~ v; \<lbrakk> v1 ~ v; v2 ~ v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto
lemma consis_join_R_inv[elim!]: "\<lbrakk> v ~ v1\<sqinter>v2; \<lbrakk> v ~ v1; v ~ v2 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induction v arbitrary: v1 v2) auto
*)     

lemma consis_sym_aux: "(v ~ v' \<longrightarrow> v' ~ v) \<and> (\<not> v ~ v' \<longrightarrow> \<not> v' ~ v)"
  by (induction v v' rule: consistent.induct) auto
    
lemma consis_sym[sym]: "v ~ v' \<Longrightarrow> v' ~ v"
  using consis_sym_aux by blast
    
lemma consis_refl_aux: "(wf_ty v \<longrightarrow> v ~ v) \<and> (wf_fun f \<longrightarrow> f ~ f)"
  apply (induction rule: wf_ty_wf_fun.induct) 
    apply force
   apply force
   apply force
  apply simp apply (rule consis_sym) apply blast  
  done

lemma consis_refl[intro!]: "wf_ty v \<Longrightarrow> v ~ v" using consis_refl_aux by blast
    
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
      apply force
    apply blast
    apply force
    apply blast
    apply blast
  done

lemma wf_merge[intro!]: "\<lbrakk> wf_ty a; wf_ty b; a ~ b \<rbrakk> \<Longrightarrow> wf_ty (merge a b)"
  by (induction a b rule: consistent.induct) force+
    
lemma consis_merge: "\<lbrakk> a ~ b; a ~ y; x ~ b; x ~ y \<rbrakk> \<Longrightarrow> merge a x ~ merge b y"
  apply (case_tac a) apply (case_tac b) apply auto apply (case_tac y) apply auto
    apply (case_tac x) apply auto apply (case_tac b) apply auto apply (case_tac b)
    apply auto
  done

lemma consis_inter_right: "\<lbrakk> wf_fun A; wf_fun B; A ~ C; B ~ C \<rbrakk> \<Longrightarrow> A \<sqinter> B ~ C"
  apply (induction C arbitrary: A B)
    apply (erule wf_fun_inv) apply force apply force
    apply (erule wf_fun_inv) apply force apply force
  apply (erule wf_fun_inv) apply simp 
   apply (erule wf_fun_inv) apply simp apply force
  apply simp apply (erule wf_fun_inv) apply force apply force
  done    

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
  
(*
lemma d_consis_nat_L: "\<lbrakk> \<Gamma> \<turnstile> c : v; \<Gamma> = [TNat n] \<rbrakk> \<Longrightarrow> v ~ TNat n"
  apply (induction \<Gamma> c v arbitrary: n rule: deduce_le.induct)
       apply (case_tac \<Gamma>1) apply force apply force
      apply (case_tac \<Gamma>1) apply force apply force
     apply force+
    apply (case_tac \<Gamma>1) apply force apply force
   apply force+
  done

lemma le_any_nat_consis[intro]: "TNat n <: v \<Longrightarrow> v ~ TNat n"
  unfolding sub_ty_def using d_consis_nat_L by auto

lemma consis_nat_atoms: "\<lbrakk> v ~ TNat n \<rbrakk> \<Longrightarrow> atoms v \<subseteq> { TNat n }"
  by (induction v arbitrary: n) auto
  
(*
lemma le_any_nat_atom_consis: "\<lbrakk> v \<sqsubseteq> TNat n \<rbrakk> \<Longrightarrow> atoms v \<subseteq> {TNat n}"
  using le_any_nat_inv_atoms by blast
*)

definition consis :: "ty set \<Rightarrow> bool" where
  "consis \<Gamma> \<equiv> (\<forall>v v'. v \<in> \<Gamma> \<longrightarrow> v' \<in> \<Gamma> \<longrightarrow> v ~ v')"
  


lemma atoms_inconsis: "\<lbrakk> \<not>(v1' ~ v2'); v1' \<in> atoms v1; v2' \<in> atoms v2 \<rbrakk> \<Longrightarrow> \<not>(v1 ~ v2)"
  by (induction v1 v2 arbitrary: v1' v2' rule: consistent.induct) auto
*)

lemma atoms_consis: "\<lbrakk> (\<forall> v1' v2'. v1' \<in> atoms v1 \<longrightarrow> v2' \<in> atoms v2 \<longrightarrow> v1' ~ v2');
      wf_fun v1; wf_fun v2 \<rbrakk> \<Longrightarrow> v1 ~ v2"
  by (induction v1 v2 rule: consistent.induct) auto    

lemma atoms_wf_fun: "\<lbrakk> wf_fun f; a \<in> atoms f \<rbrakk> \<Longrightarrow> \<exists> a1 a2. a = a1\<rightarrow>a2"
  by (induction f) auto  
  
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
  
lemma consis_nat_trans: "\<lbrakk> v1 ~ TNat n; TNat n ~ v2 \<rbrakk> \<Longrightarrow> v1 ~ v2"
  by (induction v1) auto   

lemma consis_nat_trans2: "\<lbrakk> v1 ~ v2; v2 ~ TNat n \<rbrakk> \<Longrightarrow> v1 ~ TNat n"
  by (induction v2 arbitrary: v1 n) auto

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

lemma consis_le_inconsis_le:
  "(v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1' <: v1 \<and> v2' <: v2 \<longrightarrow> v1 ~ v2))
  \<and> (\<not> v1' ~ v2' \<longrightarrow> (\<forall> v1 v2. v1 <: v1' \<and> v2 <: v2' \<longrightarrow> \<not> v1 ~ v2))"
  (is "?P v1' v2' \<and> ?Q v1' v2'")
proof (induction v1' v2' rule: consistent.induct)
  case (1 n m)
  then show ?case apply (rule conjI) apply clarify 
     apply (subgoal_tac "v1 ~ TNat n") prefer 2 using le_any_nat_consis apply auto[1]
     apply (subgoal_tac "v2 ~ TNat n") prefer 2 using le_any_nat_consis apply auto[1]
    using consis_nat_trans consis_sym apply blast
    apply (rule impI) apply simp
    using consis_atoms consistent.simps(1) sub_nat_any_inv_atoms by blast
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
      obtain v2 v2' where v22_v3: "v2\<rightarrow>v2' \<in> atoms v3" using v11_v3 sub_fun_any_inv_atoms_ex by blast
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
      obtain v1 v1' where v22_v3: "v1\<rightarrow>v1' \<in> atoms v4" using v11_v3 sub_fun_any_inv_atoms_ex by blast
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
    proof clarify
      fix v3 v4 assume "\<not> v1 \<rightarrow> v1' ~ v2 \<rightarrow> v2'" and v11_v3: "v3 <: v1 \<rightarrow> v1'" and
        v22_v4: "v4 <: v2 \<rightarrow> v2'" and v3_v4: "v3 ~ v4"
      then have v1_v2: "v1 ~ v2 \<and> \<not> v1' ~ v2'" by simp
      obtain v31 v32 where v33_v3: "v31 \<rightarrow> v32 \<in> atoms v3" 
        using sub_fun_any_inv_atoms_ex v11_v3 by blast
      have "v1 <: v31 \<and> v32 <: v1'" using v33_v3 v11_v3 sub_fun_any_inv_atoms
        sorry    
          
      have "\<not> v3 ~ v4" sorry 
      then show "False" using v3_v4 ..
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
      sorry
  qed
next
  case (6 v1 v1' v2 v2')
  then show ?case sorry
next
  case (7 v1 v1' v2)
  then show ?case sorry
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
*)  
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
  apply (rule wf_merge) apply blast+
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
