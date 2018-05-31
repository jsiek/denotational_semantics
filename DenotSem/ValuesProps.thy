theory ValuesProps
  imports Values
begin
  
section "Facts about Value Sizes"
  
lemma val_size_mem: fixes e::entry assumes e_t: "e \<in> set t" shows "esize e < fsize t"
  using e_t apply (induction t arbitrary: e)
   apply force
  apply simp apply (erule disjE)
   apply arith    
  apply (subgoal_tac "esize e < fsize t") prefer 2 apply blast
  apply arith
  done

lemma val_size_mem_l: assumes v12_t: "v1\<mapsto>v2 \<in> set t" shows "vsize v1 < fsize t"
  using v12_t val_size_mem[of "v1\<mapsto>v2" t] by auto
    
lemma val_size_mem_r: assumes v12_t: "v1\<mapsto>v2 \<in> set t" shows "vsize v2 < fsize t"
  using v12_t val_size_mem[of "v1\<mapsto> v2" t] by auto
    
section "More stuff"    

lemma entry_set_in: "p \<in> set f \<Longrightarrow> p in f"
  apply (induction f) apply force  
    apply simp apply (erule disjE) apply force apply force done
  
lemma fun_le_subset: fixes f::func shows "set f \<subseteq> set f' \<Longrightarrow> f \<sqsubseteq> f'"
  apply (induction f arbitrary: f') 
   apply force
  apply simp apply clarify
  apply (rule ins_le) using entry_set_in apply blast
  apply blast
  done

lemma le_refl_aux:
    "(\<forall> v. n = vsize v \<longrightarrow> v \<sqsubseteq> v)
   \<and> (\<forall> p. n = esize p \<longrightarrow> p \<sqsubseteq> p) 
   \<and> (\<forall> f. n = fsize f \<longrightarrow> f \<sqsubseteq> f)"
proof (induction n rule: nat_less_induct)
  case (1 n)
  show ?case apply (rule conjI) apply clarify defer apply (rule conjI) apply clarify defer
     apply clarify defer
  proof -
    fix v assume n: "n = vsize v"
    show "v \<sqsubseteq> v"
    proof (cases v)
    case (VNat k)
      then show ?thesis by blast
    next
      case (VFun t)
      have "fsize t < n" using n VFun by simp
      then show ?thesis using 1 VFun by auto
    qed
  next
    fix p assume n: "n = esize p"
    obtain v v' where p: "p = v \<mapsto> v'" by (cases p) auto
    have "vsize v < n" using n p by auto
    then have 2: "v \<sqsubseteq> v" using 1 by blast
    have "vsize v' < n" using n p by auto
    then have 3: "v' \<sqsubseteq> v'" using 1 by blast        
    show "p \<sqsubseteq> p" using 2 3 p by blast
  next
    fix f assume n: "n = fsize f"
    show "f \<sqsubseteq> f"
    proof (cases f)
      case Nil
      then show ?thesis by auto
    next
      case (Cons p f')
      have "fsize f' < n" using n Cons by auto
      then have 2: "f' \<sqsubseteq> f'" using 1 Cons by auto
      show ?thesis using 2 Cons apply simp apply (rule ins_le) defer
          apply (rule fun_le_subset) apply force apply auto done
    qed
  qed
qed
  
proposition val_le_refl[simp]: fixes v::val shows "v \<sqsubseteq> v" 
  using le_refl_aux by blast
  
lemma fun_in_empty: assumes pe: "p in []" shows "False"
proof -
  let ?P1 = "\<lambda>v1 v2. True" and ?P2 = "\<lambda>p1 p2. True" and ?P3 = "\<lambda>f1 f2. True"
    and ?P4 = "\<lambda>p f. f = [] \<longrightarrow> False"
  have base: "\<And>p t. p \<in> set t \<Longrightarrow> t = [] \<longrightarrow> False" apply (case_tac t) by auto
  show "False" using val_le_entry_le_fun_le_fun_in.induct[of ?P1 ?P2 ?P3 ?P4] pe base by blast
qed
 
thm val_le_entry_le_fun_le_fun_in.induct
lemma le_trans_aux:
    "(val_le v1 v2 \<longrightarrow> (\<forall> v3. (val_le v2 v3 \<longrightarrow> val_le v1 v3) 
                            \<and> (val_le v3 v1 \<longrightarrow> val_le v3 v2)))
  \<and> (entry_le p1 p2 \<longrightarrow> (\<forall> p3. (entry_le p2 p3 \<longrightarrow> entry_le p1 p3)
                            \<and> (entry_le p3 p1 \<longrightarrow> entry_le p3 p2)))
  \<and> (fun_le f1 f2 \<longrightarrow> (\<forall> f3. (fun_le f2 f3 \<longrightarrow> fun_le f1 f3)
                           \<and> (fun_le f3 f1 \<longrightarrow> fun_le f3 f2)))
  \<and> (p in f1 \<longrightarrow> (\<forall> f2. f1 \<sqsubseteq> f2 \<longrightarrow> p in f2))"
proof (induction rule: val_le_entry_le_fun_le_fun_in.induct)
  case (vnat_le n)
  then show ?case by auto
next
  case (vfun_le t1 t2)
  then show ?case by auto
next
  case (entry_le v2 v1 v1' v2')
  then show ?case by auto 
next
  case (empty_le t2)
  then show ?case apply clarify apply (rule conjI) apply force
    apply clarify using fun_in_empty 
next
  case (ins_le p t2 t1)
  then show ?case sorry
next
  case (fun_in_match p t)
  then show ?case sorry
next
  case (fun_in_rest p t q)
  then show ?case sorry
next
  case (fun_in_sub p1 t p2)
  then show ?case sorry
qed


 (*
  case (1 n)
  show ?case apply (rule conjI) apply clarify defer apply (rule conjI) apply clarify defer
      apply (rule conjI) apply clarify defer apply clarify defer
  proof -
    fix v1 v2::val and v3 assume n: "n = vsize v1 + vsize v2 + vsize v3" and
      v12: "v1 \<sqsubseteq> v2" and v23: "v2 \<sqsubseteq> v3"
    show "v1 \<sqsubseteq> v3" 
    proof (cases v2)
      case (VNat n2)
      then show ?thesis using v12 v23 by auto
    next
      case (VFun f2) then have v2: "v2 = VFun f2" .
      obtain f1 where v1: "v1 = VFun f1" and f12: "f1 \<sqsubseteq> f2" using v12 v2 by auto
      obtain f3 where v3: "v3 = VFun f3" and f23: "f2 \<sqsubseteq> f3" using v23 v2 by auto
      have "fsize f1 + fsize f2 + fsize f3 < n" using n v1 v2 v3 by auto
      then have f13: "f1 \<sqsubseteq> f3" using f12 f23 1 by blast
      show ?thesis using v1 v3 f13 by auto
    qed   
  next
    fix p1 p2::entry and p3 assume n: "n = esize p1 + esize p2 + esize p3" and 
      p12: "p1 \<sqsubseteq> p2" and p23: "p2 \<sqsubseteq> p3"
    obtain v1 v1' where p1: "p1 = v1\<mapsto>v1'" by (cases p1) auto
    obtain v2 v2' where p2: "p2 = v2\<mapsto>v2'" by (cases p2) auto
    obtain v3 v3' where p3: "p3 = v3\<mapsto>v3'" by (cases p3) auto
    have v31: "v3 \<sqsubseteq> v1"
    proof -
      have v32: "v3 \<sqsubseteq> v2" using p23 p2 p3 by auto
      have v21: "v2 \<sqsubseteq> v1" using p12 p1 p2 by auto
      have sv2: "vsize v1 + vsize v2 + vsize v3 < n" using n p1 p2 p3 by auto
      show ?thesis using v32 v21 1 sv2 by auto
    qed
    have v13p: "v1' \<sqsubseteq> v3'"
    proof -
      have v12p: "v1' \<sqsubseteq> v2'" using p12 p1 p2 by auto
      have v23p: "v2' \<sqsubseteq> v3'" using p23 p2 p3 by auto
      have sv2p: "vsize v1' + vsize v2' + vsize v3' < n" using n p1 p2 p3 by auto
      show ?thesis using v12p v23p 1 sv2p by auto
    qed
    show "p1 \<sqsubseteq> p3" using v31 v13p p1 p3 by auto
  next
    fix f1 f2::func and f3 assume n: "n = fsize f1 + fsize f2 + fsize f3" and
      f12: "f1 \<sqsubseteq> f2" and f23: "f2 \<sqsubseteq> f3"
    show "f1 \<sqsubseteq> f3"
    proof (cases f1)
      case Nil
      then show ?thesis by auto
    next
      case (Cons p1 f1')
      have p1_f2: "p1 in f2" using f12 Cons by auto
      have f1p_f2: "f1' \<sqsubseteq> f2" using f12 Cons by auto
      have sf: "fsize f1' + fsize f2 + fsize f3 < n" using n Cons by auto
      show ?thesis using Cons apply simp
      proof
        show "p1 in f3" sorry
      next
        show "f1' \<sqsubseteq> f3" using sf 1 f1p_f2 f23 by blast
      qed
    qed
  next
    fix p::entry and f1::func and f2 assume n: "n = fsize f1 + fsize f2" and 
      pf1: "p in f1" and f12: "f1 \<sqsubseteq> f2"
    show "p \<in> set f2"
      sorry
  qed
qed
    *)
  (*
lemma val_le_trans_aux: fixes v2::val 
  assumes n_vs2: "n = vsize v2"
  shows "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3" using n_vs2
proof (induction n arbitrary: v1 v2 v3 rule: nat_less_induct)
  case (1 n v1 v2 v3)
  show ?case
  proof (cases v1)
    case (VNat n1)
    with 1 show ?thesis by auto 
  next
    case (VFun t1) from VFun have v1: "v1 = VFun t1" .
    show ?thesis
    proof (cases v2)
      case (VNat n2)
      with VFun 1 have "False" by auto thus ?thesis ..
    next
      case (VFun t2) from VFun have v2: "v2 = VFun t2" .
      show ?thesis
      proof (cases v3)
        case (VNat n3) with v1 1 have "False" by auto thus ?thesis ..
      next
        case (VFun t3) then have v3: "v3 = VFun t3" .
        show ?thesis sorry
(*        using VFun v1 v2
        proof clarify
          fix v11 v11' assume v11_t1: "(v11,v11') |\<in>| t1"
          from v11_t1 1(2) v1 v2 obtain v22 v22' where v22_t2: "(v22,v22') |\<in>| t2" 
            and v2_v1: "v22 \<sqsubseteq> v11" and v1p_v2p: "v11' \<sqsubseteq> v22'" by blast
          from v22_t2 1(3) v2 VFun obtain v33 v33' where v33_t3: "(v33,v33') |\<in>| t3"
            and v3_v2: "v33 \<sqsubseteq> v22" and v2p_v3p: "v22' \<sqsubseteq> v33'" by blast
          have "vsize v22 < fsize t2" using v22_t2 val_size_mem_l by blast
          from this have s22_n: "vsize v22 < n" using v2 1(4) by auto   
          have v3_v1: "v33 \<sqsubseteq> v11" using 1(1)
            apply (erule_tac x="vsize v22" in allE) apply (erule impE) using s22_n apply blast
              using v3_v2 v2_v1 by blast
          have "vsize v22' < fsize t2" using v22_t2 val_size_mem_r by blast
          from this have s22p_n: "vsize v22' < n" using v2 1(4) by auto   
          have v1_v3: "v11' \<sqsubseteq> v33'" using 1(1)
            apply (erule_tac x="vsize v22'" in allE) apply (erule impE) using s22p_n apply blast
            using v1p_v2p v2p_v3p by blast 
          from v3_v1 v1_v3 v33_t3
          show "\<exists>v33 v33'. (v33, v33') |\<in>| t3 \<and> v33 \<sqsubseteq> v11 \<and> v11' \<sqsubseteq> v33'" by blast
        qed
      qed
*)
      qed
    qed
  qed
qed
*)

proposition val_le_trans[trans]: fixes v2::val shows "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  sorry
    
lemma consis_and_not_consis:
  "(v ~ v' \<longrightarrow> \<not> (v !~ v')) \<and> (v !~ v' \<longrightarrow> \<not>(v ~ v'))"
  apply (induction rule: consistent_inconsistent.induct) apply force+ done

lemma consis_or_not_aux: assumes vs: "n = vsize v" shows "v ~ v' \<or> v !~ v'"
  using vs apply (induction n  arbitrary: v v' rule: nat_less_induct)
  apply (case_tac v)
   apply (case_tac v')
    apply force
   apply force
  apply (case_tac v')
   apply force
proof -
  fix n v v' x2 x2a
  assume IH: "\<forall>m<n. \<forall>x. m = vsize x \<longrightarrow> (\<forall>xa. x ~ xa \<or> x !~ xa)"
    and n: "n = vsize v"
    and v: "v = VFun x2" and vp: "v' = VFun x2a"
  show "v ~ v' \<or> v !~ v'"
  proof (cases "v !~ v'")
    case True
    then show ?thesis by blast
  next
    case False hence nc: "\<not> (v !~ v')" .
    from v vp have "v ~ v'" apply simp apply (rule vfun_consis) apply (rule allI)+
        apply (rule impI) apply (erule conjE)
    proof -
      fix v1 v1' v2 v2' assume 1: "v1\<mapsto> v1' \<in> set x2" and 2: "v2\<mapsto> v2' \<in> set x2a"
      have 3: "vsize v1 < vsize (VFun x2)" using 1 val_size_mem_l[of v1 v1' x2] by auto 
      from IH 3 n v have "v1 ~ v2 \<or> v1 !~ v2" by blast
      from this show "(v1 ~ v2 \<and> v1' ~ v2') \<or> v1 !~ v2"
      proof
        assume v1_v2: "v1 ~ v2"
        have 4: "vsize v1' < vsize (VFun x2)" using 1 val_size_mem_r[of v1 v1' x2] by auto 
        have "v1' ~ v2' \<or> v1' !~ v2'" using IH 4 n v by blast
        from this show ?thesis 
        proof
          assume "v1' ~ v2'" from v1_v2 this show ?thesis by blast
        next
          assume "v1' !~ v2'" 
          then have "v !~ v'" using v1_v2 1 2 v vp by blast 
          with nc have "False" ..
          from this show ?thesis ..
        qed
      next
        assume "v1 !~ v2"
        then show ?thesis by blast
      qed
    qed
    then show ?thesis by blast
  qed
qed
    
lemma consis_not[intro]: "\<not>(v !~ v') \<Longrightarrow> v ~ v'"
  using consis_or_not_aux by blast 
    
lemma not_consis[intro]: "v ~ v' \<Longrightarrow> \<not> (v !~ v')" 
  using consis_and_not_consis by blast

lemma consis_refl[intro!]: "is_val v \<Longrightarrow> v ~ v"
  apply (induction rule: is_val.induct)
   apply blast
  apply (simp only: is_fun_def)
  apply (rule vfun_consis)
  apply (rule allI)+ apply (rule impI)+ apply (erule conjE)+
  apply (case_tac "v1 ~ v2") apply force apply blast 
  done

lemma consis_symm_aux:
  "(v ~ v' \<longrightarrow> v' ~ v) \<and> (v !~ v' \<longrightarrow> v' !~ v)"
  by (induction rule: consistent_inconsistent.induct) force+

lemma consis_symm[sym]: "v ~ v' \<Longrightarrow> v' ~ v" 
  using consis_symm_aux by blast

lemma inconsis_symm[sym]: "v !~ v' \<Longrightarrow> v' !~ v" 
  using consis_symm_aux by blast
   
lemma env_refl[intro!]: fixes \<rho>::"val list" shows "\<rho> \<sqsubseteq> \<rho>"
  unfolding env_le_def apply auto done
  
lemma env_le_ext[intro!]: fixes v::val and \<rho>::"val list" 
  shows "\<lbrakk> v \<sqsubseteq> v'; \<rho> \<sqsubseteq> \<rho>' \<rbrakk> \<Longrightarrow> v#\<rho> \<sqsubseteq> v'#\<rho>'"
  unfolding env_le_def apply auto apply (case_tac k) apply force apply force done

lemma val_env_ext[intro!]: "\<lbrakk> is_val v; val_env \<rho> \<rbrakk> \<Longrightarrow> val_env (v#\<rho>)"
  unfolding val_env_def apply auto apply (case_tac k) apply auto done
 
lemma consis_env_refl[intro!]: "val_env \<rho> \<Longrightarrow> consis_env \<rho> \<rho>"
  apply (induction \<rho>) apply force
  apply (rule consis_env_cons)
   unfolding val_env_def apply (erule_tac x=0 in allE) apply force
  apply (subgoal_tac "\<forall>k<length \<rho>. is_val (\<rho> ! k)") apply force 
    apply clarify apply (erule_tac x="Suc k" in allE) apply auto done
    
lemma consis_length: "\<lbrakk> consis_env \<rho> \<rho>' \<rbrakk> \<Longrightarrow> length \<rho> = length \<rho>'"
  apply (induction rule: consis_env.induct)
   apply auto done

lemma lookup_consis[intro]: "\<lbrakk> consis_env \<rho> \<rho>'; x < length \<rho> \<rbrakk> \<Longrightarrow> \<rho>!x ~ \<rho>'!x"
  apply (induction arbitrary: x rule: consis_env.induct )
   apply force apply (case_tac x) apply auto done

lemma fun_le_subset: fixes t1::"func" shows "set t1 \<subseteq> set t2 \<Longrightarrow> t1 \<sqsubseteq> t2"
 by (induction t1) auto  
  
lemma fun_le_append1: fixes t1::"func" shows "t1 \<sqsubseteq> t1 @ t2"
proof -
  have "set t1 \<subseteq> set (t1 @ t2)" by auto
  then show ?thesis using fun_le_subset by blast
qed
  
lemma fun_le_append2: fixes t1::"func" shows "t1 \<sqsubseteq> t2 @ t1"
proof -
  have "set t1 \<subseteq> set (t2 @ t1)" by auto
  then show ?thesis using fun_le_subset by blast
qed

lemma fun_append_le: fixes t1::"func" and t1'::"func"
  assumes t1_t2: "t1 \<sqsubseteq> t2" and t1p_t2: "t1' \<sqsubseteq> t2" shows "t1 @ t1' \<sqsubseteq> t2"    
  using t1_t2 t1p_t2 by (induction t1 arbitrary: t1' t2) auto
    
lemma join_lub_aux: fixes v1::val and v2::val 
  assumes n: "n = size v1 + size v2" and ub1: "v1 \<sqsubseteq> v" and ub2: "v2 \<sqsubseteq> v"
  shows "val_lub (v1 \<squnion> v2) v1 v2"
  using n ub1 ub2 apply (induction n arbitrary: v1 v2 v rule: nat_less_induct)
  apply (case_tac v1)
   apply (case_tac v2) apply force apply force
  apply (case_tac v2) apply force
  apply clarify  
  apply (rule conjI) apply (simp only: vfun_join)
   apply clarify apply (rule fun_le_append1)
  apply (rule conjI) apply (simp only: vfun_join)
   apply clarify apply (rule fun_le_append2)
  apply clarify apply (simp only: vfun_join)
  apply clarify
  apply (rule fun_append_le) apply blast apply blast
  done

abbreviation bounded :: "val \<Rightarrow> val \<Rightarrow> bool" where
  "bounded v1 v2 \<equiv> (\<exists> v. is_val v \<and> v1 \<sqsubseteq> v \<and> v2 \<sqsubseteq> v)" 

proposition join_lub: fixes v1::val and v2::val 
  assumes v12: "bounded v1 v2" shows "val_lub (v1 \<squnion> v2) v1 v2"
  using join_lub_aux v12 by blast

end
