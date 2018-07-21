(*<*)
theory Consistency
  imports IntersectionTypes
begin
(*>*)

section "Consistency and Well-Formed Types"

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
  
lemma consis_inter_L[intro!]: "\<lbrakk> v1 ~ v3; v2 ~ v3 \<rbrakk> \<Longrightarrow> v1 \<sqinter> v2 ~ v3"
  using atoms_consis consis_atoms by blast
    
lemma consis_inter_R[intro!]: "\<lbrakk> v1 ~ v2; v1 ~ v3 \<rbrakk> \<Longrightarrow> v1 ~ v2 \<sqinter> v3"
  using atoms_consis consis_atoms by blast

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

definition consis :: "ty set \<Rightarrow> bool" where
  "consis \<Gamma> \<equiv> (\<forall>v v'. v \<in> \<Gamma> \<longrightarrow> v' \<in> \<Gamma> \<longrightarrow> v ~ v')"
  
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

lemma meet_list_singleton[simp]: "\<Sqinter> [a] = a"
  by (simp add: meet_list_def)
    
lemma meet_list_consis: "\<lbrakk> L1 \<noteq> []; L2 \<noteq> []; \<forall>A B. {A,B} \<subseteq> set L1 \<union> set L2 \<longrightarrow> A ~ B\<rbrakk>
    \<Longrightarrow> \<Sqinter>L1 ~ \<Sqinter>L2"
 apply (induction L1 arbitrary: L2)
  apply force
  apply (case_tac L1)
    apply simp using meet_list_right_consis apply blast
  by (simp add: consis_sym meet_list_right_consis)  
        
lemma meet_list_left_consis_inv: "\<lbrakk> \<Sqinter>L1 ~ B; A \<in> set L1; L1 \<noteq> [] \<rbrakk> \<Longrightarrow> A ~ B"
  using meet_list_atoms atoms_consis consis_atoms by (smt UN_I)

lemma meet_list_consis_inv: "\<lbrakk> \<Sqinter>L1 ~ \<Sqinter>L2; A \<in> set L1; B \<in> set L2; L1 \<noteq> []; L2 \<noteq> [] \<rbrakk> \<Longrightarrow> A ~ B"
  using meet_list_atoms atoms_consis consis_atoms by (smt UN_I)

lemma meet_list_inconsis_inv: "\<lbrakk> \<not> \<Sqinter>L1 ~ \<Sqinter>L2; L1 \<noteq> []; L2 \<noteq> [] \<rbrakk> \<Longrightarrow> 
   \<exists> A B. A \<in> set L1 \<and> B \<in> set L2 \<and> \<not> A ~ B"
  using meet_list_atoms atoms_inconsis inconsis_atoms by (smt UN_E)

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

lemma fold_depth_cod: "\<lbrakk> all_funs (set \<Gamma>); d1 < d2 \<rbrakk> \<Longrightarrow>
   fold (\<lambda>a b. max (depth a) b) (map cod \<Gamma>) d1
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
    
lemma list_depth_cod: "\<lbrakk> all_funs (set \<Gamma>); \<Gamma> \<noteq> [] \<rbrakk> \<Longrightarrow> list_depth (map cod \<Gamma>) < list_depth \<Gamma>"
  apply (case_tac \<Gamma>) apply force
  apply simp apply (case_tac a) apply force defer apply force apply simp
    using fold_depth_cod apply auto done

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
  
lemma depth_meet_list_cod:
  assumes g_a: "set \<Gamma> \<subseteq> atoms A" and af_g: "all_funs (set \<Gamma>)" and g_ne: "\<Gamma> \<noteq> []"
  shows "depth (\<Sqinter> (map cod \<Gamma>)) < depth A"
proof -
  have "list_depth (map cod \<Gamma>) < list_depth \<Gamma>" using af_g g_ne by (rule list_depth_cod)
  then have "depth (\<Sqinter>(map cod \<Gamma>)) < list_depth \<Gamma>" using meet_list_depth g_ne by auto
  also have "list_depth \<Gamma> \<le> depth A"
    apply (rule list_depth_bounded) using g_ne apply blast
    using g_a atoms_depth apply blast done
  finally show ?thesis by blast
qed

lemma consis_sub_aux: 
  "(\<forall> A B C D. n = depth A + depth B + depth C + depth D 
      \<longrightarrow> A ~ B \<longrightarrow> A <: C \<longrightarrow> B <: D \<longrightarrow> C ~ D)" (is "?P n ")
proof (induction n rule: nat_less_induct)
  case (1 n)
  show ?case    
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
          fix \<Gamma>a assume ga_ne: "\<Gamma>a \<noteq> []" and af_ga: "all_funs (set \<Gamma>a)" and
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
              have s_ga: "depth (\<Sqinter>(map dom \<Gamma>a)) < depth A" 
                using ga_a depth_meet_list_dom ga_ne af_ga by blast
              have s_gb: "depth (\<Sqinter>(map dom \<Gamma>b)) < depth B" 
                using gb_b depth_meet_list_dom gb_ne af_gb by blast
              have s_cga: "depth (\<Sqinter>(map cod \<Gamma>a)) < depth A"
                using ga_a depth_meet_list_cod ga_ne af_ga by blast
              have s_cgb: "depth (\<Sqinter>(map cod \<Gamma>b)) < depth B" 
                using gb_b depth_meet_list_cod gb_ne af_gb by blast
              have c_ga_gb: "\<Sqinter>(map dom \<Gamma>a) ~ \<Sqinter>(map dom \<Gamma>b)"
                using c1_dga d1_dgb True 1 s_c1 s_d1 s_ga s_gb n
                apply (erule_tac x="depth (\<Sqinter>(map dom \<Gamma>a)) + depth (\<Sqinter>(map dom \<Gamma>b)) + depth C1 + depth D1" in allE)
                apply (erule impE) apply force apply force
                done                
              have "\<Sqinter>(map cod \<Gamma>a) ~ \<Sqinter>(map cod \<Gamma>b)" apply (rule atoms_consis) apply clarify
              proof -
                fix A' B' assume ap_ga: "A' \<in> atoms (\<Sqinter>(map cod \<Gamma>a))" and
                  bp_gb: "B' \<in> atoms (\<Sqinter>(map cod \<Gamma>b))"
                have "A' \<in> ctx_atoms (map cod \<Gamma>a)" using ap_ga meet_list_atoms ga_ne by auto
                then obtain A1 A2 where a12_ga: "A1\<rightarrow>A2 \<in> set \<Gamma>a" and ap_a2: "A' \<in> atoms A2"
                  using af_ga apply auto apply (case_tac x) apply auto done
                have "B' \<in> ctx_atoms (map cod \<Gamma>b)" using bp_gb meet_list_atoms gb_ne by auto
                then obtain B1 B2 where b12_gb: "B1\<rightarrow>B2 \<in> set \<Gamma>b" and bp_b2: "B' \<in> atoms B2"
                  using af_gb apply auto apply (case_tac x) apply auto done
                have a12_a: "A1\<rightarrow>A2 \<in> atoms A" using a12_ga ga_a by blast
                have b12_b: "B1\<rightarrow>B2 \<in> atoms B" using b12_gb gb_b by blast
                have a12_b12: "A1\<rightarrow>A2 ~ B1\<rightarrow>B2" using a12_a b12_b a_b consis_atoms by blast
                have "A1 ~ B1"
                proof -
                  have a1_dga: "A1 \<in> set (map dom \<Gamma>a)" using a12_ga by force
                  have b1_dgb: "B1 \<in> set (map dom \<Gamma>b)" using b12_gb by force
                  show ?thesis
                    using c_ga_gb a1_dga b1_dgb ga_ne gb_ne meet_list_consis_inv by auto
                qed
                then have "A2 ~ B2" using a12_b12 by simp                    
                then show "A' ~ B'" using ap_a2 bp_b2 consis_atoms by blast
              qed                
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
qed

lemma consis_le: "\<lbrakk> v1' <: v1; v2' <: v2; v1' ~ v2' \<rbrakk> \<Longrightarrow> v1 ~ v2"
  using consis_sub_aux by auto
    
lemma inconsis_sub_aux:
  "\<forall> A B C D. n = depth A + depth B + depth C + depth D
      \<longrightarrow> \<not> A ~ B \<longrightarrow> C <: A \<longrightarrow> D <: B \<longrightarrow> \<not> C ~ D"
 (is "?Q n")
proof (induction n rule: nat_less_induct)
  case (1 n)
  show ?case apply (rule allI)+ apply (rule impI)+    
  proof -
    fix A::ty and B::ty and C::ty and D::ty
    assume n: "n = depth A + depth B + depth C + depth D" and
      a_b: "\<not> A ~ B" and c_a: "C <: A" and d_b: "D <: B"
    obtain A' B' where ap_a: "A' \<in> atoms A" and bp_b: "B' \<in> atoms B" and ap_bp: "\<not> A' ~ B'"
      using a_b inconsis_atoms by blast
    show "\<not> C ~ D"
    proof (cases A')
      case (TNat n)
      have n_c: "TNat n \<in> atoms C" using c_a ap_a TNat sub_atom_sub sub_nat_any_inv_atoms by blast
      have "(\<exists>m. B' = TNat m \<and> m \<noteq> n) \<or> (\<exists>B1 B2. B' = B1\<rightarrow>B2)" using TNat ap_bp bp_b
          apply (cases B') apply auto done
      then show ?thesis
      proof
        assume "\<exists>m. B' = TNat m \<and> m \<noteq> n"
        then obtain m where bp: "B' = TNat m" and m_n: "m \<noteq> n" by blast
        have m_d: "TNat m \<in> atoms D" using bp d_b bp_b 
           sub_atom_sub sub_nat_any_inv_atoms by blast
        have tn_tm: "\<not> TNat n ~ TNat m" using m_n by simp
        then show "\<not> C ~ D" apply (rule atoms_inconsis) using n_c m_d apply auto done
      next
        assume "\<exists>B1 B2. B' = B1\<rightarrow>B2"
        then obtain B1 B2 where bp: "B' = B1 \<rightarrow> B2" by blast
        have "D <: B1 \<rightarrow> B2" using d_b bp_b bp using sub_atom_sub by blast
        then obtain D1 D2 where d12_d: "D1\<rightarrow>D2 \<in> atoms D"
          using sub_fun_any_inv_atoms_ex by blast
        have "\<not> TNat n ~ D1\<rightarrow>D2" by simp            
        then show "\<not> C ~ D" using n_c d12_d atoms_inconsis by blast          
      qed
    next
      case (TArrow A1 A2)
      have c_a12: "C <: A1 \<rightarrow> A2" using c_a TArrow sub_atom_sub ap_a by blast
      have "(\<exists>n. B' = TNat n) \<or> (\<exists> B1 B2. B' = B1\<rightarrow>B2 \<and> A1~B1 \<and> \<not> A2 ~ B2)"
        using ap_bp TArrow bp_b apply (cases B') by auto      
      then show ?thesis
      proof 
        assume "\<exists>n. B' = TNat n" then obtain n where bp: "B' = TNat n" by blast
        have n_d: "TNat n \<in> atoms D" using d_b bp_b bp sub_atom_sub sub_nat_any_inv_atoms by blast
        obtain C1 C2 where c12_c: "C1\<rightarrow>C2 \<in> atoms C" using c_a12 sub_fun_any_inv_atoms_ex by blast
        have "\<not> C1\<rightarrow>C2 ~ TNat n" by simp
        then show ?thesis using c12_c n_d atoms_inconsis by blast
      next
        assume "\<exists> B1 B2. B' = B1\<rightarrow>B2 \<and> A1~B1 \<and> \<not> A2 ~ B2"
        then obtain B1 B2 where bp: "B' = B1\<rightarrow>B2" and a1_b1: "A1 ~ B1" and a2_b2: "\<not> A2 ~ B2"
          by blast
            
        have v11_v3: "C <: A1 \<rightarrow> A2" using c_a12 by blast
        have v22_v4: "D <: B1 \<rightarrow> B2" using bp bp_b d_b sub_atom_sub by blast
        have v1_v2: "A1 ~ B1" using a1_b1 by blast 
        have not_v1p_v2p: "\<not> A2 ~ B2" using a2_b2 by blast

        obtain \<Gamma>3 where g3_ne: "\<Gamma>3 \<noteq> []" and af_g3: "all_funs (set \<Gamma>3)" and g3_v3: "set \<Gamma>3 \<subseteq> atoms C" and
          v1_g3: "A1 <: \<Sqinter>(map dom \<Gamma>3)" and g3_v1p: "\<Sqinter>(map cod \<Gamma>3) <: A2" 
          using v11_v3 sub_any_fun_elim2 by blast
        obtain \<Gamma>4 where g4_ne: "\<Gamma>4 \<noteq> []" and af_g4: "all_funs (set \<Gamma>4)" and g4_v4: "set \<Gamma>4 \<subseteq> atoms D" and
          v2_g4: "B1 <: \<Sqinter>(map dom \<Gamma>4)" and g4_v2p: "\<Sqinter>(map cod \<Gamma>4) <: B2" 
          using v22_v4 sub_any_fun_elim2 by blast
      
        have c_dg3_dg4: "\<Sqinter>(map dom \<Gamma>3) ~ \<Sqinter>(map dom \<Gamma>4)" using v1_v2 v1_g3 v2_g4 consis_le by blast
            
        have nc_cg3_cg4: "\<not> \<Sqinter>(map cod \<Gamma>3) ~ \<Sqinter>(map cod \<Gamma>4)"
        proof -
           have s_a2: "depth A2 < depth A" using ap_a TArrow atoms_depth[of A' A] by auto
           have s_b2: "depth B2 < depth B" using bp_b bp atoms_depth[of B' B] by auto
           have s_g3: "depth (\<Sqinter>(map cod \<Gamma>3)) < depth C"
                using g3_v3 depth_meet_list_cod g3_ne af_g3 by blast
           have s_g4: "depth (\<Sqinter>(map cod \<Gamma>4)) < depth D" 
                using g4_v4 depth_meet_list_cod g4_ne af_g4 by blast
          show ?thesis using not_v1p_v2p g3_v1p g4_v2p n 1
            apply (erule_tac x="depth A2 + depth B2 + depth (\<Sqinter>(map cod \<Gamma>3)) + depth (\<Sqinter>(map cod \<Gamma>4))" in allE)
            apply (erule impE) using s_a2 s_b2 s_g3 s_g4 apply force apply blast done
        qed
        obtain C3 D3 where c_g3: "C3 \<in> set (map cod \<Gamma>3)" and d_g4: "D3 \<in> set (map cod \<Gamma>4)" and 
        c_d: "\<not> C3 ~ D3" using nc_cg3_cg4 by(meson g3_ne g4_ne map_is_Nil_conv meet_list_inconsis_inv)
        obtain A where ac_g3: "A \<rightarrow> C3 \<in> set \<Gamma>3" using c_g3 af_g3 g3_v3 apply auto apply (case_tac x)
          apply auto done
        obtain B where bd_g4: "B \<rightarrow> D3 \<in> set \<Gamma>4" using d_g4 af_g4 apply auto apply (case_tac x)
          apply auto done         
        have a_b: "A ~ B" using c_dg3_dg4
          apply (rule meet_list_consis_inv)
          using ac_g3 apply force
          using bd_g4 apply force
          using g3_ne apply force using g4_ne apply force done
        have "\<not> A \<rightarrow> C3 ~ B \<rightarrow> D3" using a_b c_d by simp
        then show "\<not> C ~ D" 
          apply (rule atoms_inconsis)
          using g3_v3 g4_v4 ac_g3 bd_g4 apply auto done
      qed
    next
      case (TInter A1 A2)
      then have "False" using ap_a by auto
      then show ?thesis ..
    qed
  qed
qed
  
lemma inconsis_le: "\<lbrakk> v1 <: v1'; v2 <: v2'; \<not> v1' ~ v2' \<rbrakk> \<Longrightarrow> \<not> v1 ~ v2"
  using inconsis_sub_aux by blast


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
    
(*<*)
end
(*>*)

