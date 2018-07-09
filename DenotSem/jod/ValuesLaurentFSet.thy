theory ValuesLaurentFSet
  imports Main "~~/src/HOL/Library/FSet" 
begin

datatype val = VNat nat | VArrow val val (infix "\<mapsto>" 60) | VUnion val val (infix "\<squnion>" 59)
  
abbreviation is_fun :: "val \<Rightarrow> bool" where
  "is_fun v \<equiv> (case v of v1\<mapsto>v2 \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation all_funs :: "val fset \<Rightarrow> bool" where
   "all_funs xs \<equiv> (\<forall>v. v |\<in>| xs \<longrightarrow> is_fun v)"

interpretation is_fun_commute: comp_fun_commute "(\<lambda>v b. is_fun v \<and> b)"
  unfolding comp_fun_commute_def by auto  
  
fun dom :: "val \<Rightarrow> val" where
  "dom (v\<mapsto>v') = v" 
  
fun cod :: "val \<Rightarrow> val" where
  "cod (v\<mapsto>v') = v'"

inductive deduce_le :: "val fset \<Rightarrow> nat \<Rightarrow> val fset \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 56) where
  wk_nat[intro!]: "\<lbrakk> xs \<turnstile> k : {|v|} \<rbrakk> \<Longrightarrow> finsert (VNat n) xs \<turnstile> Suc k : {|v|}" |
  wk_fun[intro!]: "\<lbrakk> xs \<turnstile> k : {|v|} \<rbrakk> \<Longrightarrow> finsert (v1 \<mapsto> v2) xs \<turnstile> Suc k : {|v|}" |
  empty_R[intro!]: "xs \<turnstile> k : {||}" |
  cons_R[intro!]: "\<lbrakk> xs \<turnstile> k : ys1; xs \<turnstile> k : ys2 \<rbrakk> 
    \<Longrightarrow> xs \<turnstile> Suc k : ys1 |\<union>| ys2" |
  union_R[intro!]: "\<lbrakk> xs \<turnstile> k : {|v1|}; xs \<turnstile> k : {|v2|} \<rbrakk> \<Longrightarrow> xs \<turnstile> Suc k : {|v1\<squnion>v2|}" |
  union_L[intro]:"\<lbrakk> {|v1,v2|}|\<union>|xs \<turnstile> k : {|v|} \<rbrakk>
                  \<Longrightarrow> finsert (v1\<squnion>v2) xs \<turnstile> Suc k : {|v|}" | 
  le_nat[intro!]: "{|VNat n|} \<turnstile> k : {|VNat n|}" |
  le_arrow[intro!]: "\<lbrakk>all_funs xs; {|v1|} \<turnstile> k : dom|`|xs; cod|`|xs \<turnstile> k : {|v2|}\<rbrakk>
    \<Longrightarrow> xs \<turnstile> Suc k : {|v1 \<mapsto> v2|}"

inductive_cases deduce_finsert_inv: "xs \<turnstile> c : finsert x ys"
  
section "Weakening Lemmas"
  
lemma weaken1: "\<lbrakk> xs \<turnstile> k : {|v'|} \<rbrakk> \<Longrightarrow> \<exists> k'. finsert v xs \<turnstile> k' : {|v'|}"
proof (induction v arbitrary: xs k v')
  case (VNat n)
  then have "finsert (VNat n) xs \<turnstile> Suc k : {|v'|}" by blast
  then show ?case by blast
next
  case (VArrow v1 v2)
  then have "finsert (VArrow v1 v2) xs \<turnstile> Suc k : {|v'|}" by blast
  then show ?case by blast
next
  case (VUnion v1 v2)
  obtain c2 where 1: "finsert v2 xs \<turnstile> c2 : {|v'|}" using VUnion by blast
  obtain c1 where 2: "finsert v1 (finsert v2 xs) \<turnstile> c1 : {|v'|}" using VUnion 1 by blast
  show ?case using 2 union_L by force
qed

lemma weaken_aux: "\<lbrakk> xs \<turnstile> c : {|v'|} \<rbrakk> \<Longrightarrow> \<exists> c'. xs' |\<union>| xs \<turnstile> c' : {|v'|}"
proof (induction xs' arbitrary: xs c v')
  case empty
  then show ?case by force
next
  case (insert x xs')
  obtain c' where cp: "xs' |\<union>| xs \<turnstile> c' : {|v'|}" using insert.IH insert(3) by blast
  obtain c'' where cpp: "finsert x (xs'|\<union>|xs) \<turnstile> c'' : {|v'|}" using cp weaken1 by blast
  then show ?case by auto
qed

lemma weaken: "\<lbrakk> xs \<turnstile> c : {|v'|}; xs |\<subseteq>| xs' \<rbrakk> \<Longrightarrow> \<exists> c'. xs' \<turnstile> c' : {|v'|}"
  using weaken_aux by (metis sup.orderE)

lemma factor_union: "a |\<subseteq>| b|\<union>|c \<Longrightarrow> \<exists>a1 a2. a = a1|\<union>|a2 \<and> a1 |\<subseteq>| b \<and> a2 |\<subseteq>| c"
  apply (induction a)
   apply blast
  apply simp apply (erule exE)+ apply (erule conjE)+ apply (erule disjE)
  using finsert_absorb2 apply blast
  by (metis finsert_fsubset funion_finsert_right)
    
lemma weaken_size: "\<lbrakk> xs \<turnstile> c : ys; c \<le> c' \<rbrakk> \<Longrightarrow> xs \<turnstile> c' : ys"
  apply (induction xs c ys arbitrary: c' rule: deduce_le.induct) 
  apply (metis Suc_le_D Suc_le_lessD less_Suc_eq_le wk_nat)
  apply (metis Suc_le_D Suc_le_lessD less_Suc_eq_le wk_fun)
  apply blast    
  using Suc_le_D apply force
  apply (metis Suc_le_D Suc_le_lessD less_Suc_eq_le union_R)
  apply (metis Suc_le_D Suc_le_lessD less_Suc_eq_le union_L)
  apply blast  
  by (metis Suc_le_D Suc_le_lessD le_arrow less_Suc_eq_le)

lemma weaken_right: "\<lbrakk> xs \<turnstile> c : ys; ys' |\<subseteq>| ys  \<rbrakk> \<Longrightarrow> \<exists>c'. xs \<turnstile> c' : ys' \<and> c' \<le> c"
proof (induction xs c ys arbitrary: ys' rule: deduce_le.induct)
  case (wk_nat xs c v n)
  then have "ys' = bot \<or> ys' = {|v|}" by blast
  then show ?case
  proof
    assume "ys' = bot"
    then show ?thesis by auto
  next
    assume "ys' = {|v|}" 
    then show ?thesis using wk_nat by blast
  qed
next
  case (wk_fun xs c v v1 v2)
  then have "ys' = bot \<or> ys' = {|v|}" by blast
  then show ?case
  proof
    assume "ys' = bot"
    then show ?thesis by auto
  next
    assume "ys' = {|v|}" 
    then show ?thesis using wk_fun by blast
  qed
next
  case (empty_R xs)
  then show ?case by auto
next
  case (cons_R xs k ys1 ys2)
  have "\<exists>ys1' ys2'. ys'=ys1'|\<union>|ys2' \<and> ys1' |\<subseteq>| ys1 \<and> ys2' |\<subseteq>| ys2"
    using cons_R(5) by (simp add: factor_union)
  then obtain ys1' ys2' where ysp: "ys'=ys1'|\<union>|ys2'" and ys11: "ys1' |\<subseteq>| ys1" and ys22: "ys2' |\<subseteq>| ys2"
    by blast      
  from cons_R.IH(1) ys11 obtain c3 where c3: "xs \<turnstile> c3 : ys1'" and c3_k: "c3 \<le> k" by blast
  from cons_R.IH(2) ys22 obtain c4 where c4: "xs \<turnstile> c4 : ys2'" and c4_k: "c4 \<le> k" by blast
  let ?c34 = "max c3 c4"
  have c3_2: "xs \<turnstile> ?c34 : ys1'" using c3 weaken_size by auto
  have c4_2: "xs \<turnstile> ?c34 : ys2'" using c4 weaken_size by auto
  have "xs \<turnstile> Suc ?c34 : ys'" using c3_2 c4_2 ysp by auto
  then show ?case using c3_k c4_k by auto
next
  case (union_R xs k v1 v2)
  have "ys' = bot \<or> ys' = {|v1 \<squnion> v2|}" using union_R(5) by blast
  then show ?case
  proof
    assume "ys' = bot"
    then show ?thesis by auto
  next
    assume ysp: "ys' = {|v1 \<squnion> v2|}" 
    show ?thesis using ysp union_R by blast
  qed
next
  case (union_L v1 v2 xs k v)
  have "ys' = bot \<or> ys' = {|v|}" using union_L(3) by blast
  then show ?case
  proof
    assume "ys' = bot"
    then show ?thesis by auto
  next
    assume ysp: "ys' = {|v|}" 
    show ?thesis using ysp union_L by blast
  qed
next
  case (le_nat n ys')
  have "ys' = bot \<or> ys' = {|VNat n|}" using le_nat by auto
  then show ?case
  proof
    assume "ys' = bot"
    then show ?thesis by auto
  next
    assume ysp: "ys' = {|VNat n|}" 
    show ?thesis using ysp le_nat by blast
  qed
next
  case (le_arrow xs v1 k v1')
  have "ys' = bot \<or> ys' = {|v1 \<mapsto> v1'|}" using le_arrow(6) by blast
  then show ?case
  proof
    assume "ys' = bot"
    then show ?thesis by auto
  next
    assume ysp: "ys' = {|v1 \<mapsto> v1'|}" 
    show ?thesis using ysp le_arrow by blast
  qed
qed    

section "Axiom Lemma"

lemma ax: "v |\<in>| xs \<Longrightarrow> \<exists>c. xs \<turnstile> c : {|v|}"
proof (induction v arbitrary: xs)
  case (VNat n)
  have "{|VNat n|} \<turnstile> 0 : {|VNat n|}" by blast
  then obtain c where "xs \<turnstile> c : {|VNat n|}" using weaken[of "{|VNat n|}"] VNat by blast
  then show ?case by blast
next
  case (VArrow v1 v2)
  let ?xs = "{|v1 \<mapsto> v2|}"
  have af_xs: "all_funs ?xs" by auto
  obtain c1 where c1: "{|v1|} \<turnstile> c1 : dom|`|?xs" using VArrow.IH(1) by auto
  obtain c2 where c2: "cod|`|?xs \<turnstile> c2 : {|v2|}" using VArrow.IH(2) by auto
  let ?k = "max c1 c2"
  have c1_2: "{|v1|} \<turnstile> ?k : dom|`|?xs" using weaken_size c1 by auto
  have c2_2: "cod|`|?xs \<turnstile> ?k : {|v2|}" using weaken_size c2 by auto
  have "?xs \<turnstile> Suc ?k : {|v1 \<mapsto> v2|}" using af_xs c1_2 c2_2 by (rule le_arrow)
  then show ?case using VArrow(3) weaken[of "{|v1 \<mapsto> v2|}"] by blast
next
  case (VUnion v1 v2)
  obtain xs' where xs: "xs = finsert (v1\<squnion>v2) xs'" using VUnion.prems by blast
  obtain c1' where "{|v1,v2|}|\<union>|xs' \<turnstile> c1' : {|v1|}" using VUnion.IH by blast
  then have "finsert (v1\<squnion>v2) xs' \<turnstile> Suc c1' : {|v1|}" by blast
  then have c1: "xs \<turnstile> Suc c1' : {|v1|}" using xs by simp      
  obtain c2' where "{|v1,v2|}|\<union>|xs' \<turnstile> c2' : {|v2|}" using VUnion.IH by blast
  then have "finsert (v1\<squnion>v2) xs' \<turnstile> Suc c2' : {|v2|}" by blast
  then have c2: "xs \<turnstile> Suc c2' : {|v2|}" using xs by simp      
  show ?case apply (rule_tac x="Suc (Suc (max c1' c2'))" in exI)    
    using c1 c2 weaken_size max_Suc_Suc union_R by auto
qed

section "Union Left Inversion Lemma"

lemma "va \<squnion> vb = va \<Longrightarrow> False"
  by (metis add.assoc add_eq_0_iff_both_eq_0 add_eq_self_zero n_not_Suc_n val.size_gen(3))
  
lemma "va \<squnion> vb = vb \<Longrightarrow> False"
  by (metis add.right_neutral nat_add_left_cancel_less not_add_less2 val.size_gen(3) zero_less_Suc)
    
lemma union_Le: "\<lbrakk> xs \<turnstile> c : ys; ys = {|v|}; xs = finsert (v1\<squnion>v2) xs'; v1\<squnion>v2 |\<notin>| xs' \<rbrakk> \<Longrightarrow>
                  \<exists>c'. {|v1,v2|} |\<union>| xs' \<turnstile> c' : {|v|} \<and> c' < c"
proof (induction xs c ys arbitrary: v1 v2 v xs' rule: deduce_le.induct)
  case (wk_nat xs k vr n)
  show ?case
  proof (cases "VNat n |\<in>| xs")
    case True
    then have xs: "xs = finsert (v1 \<squnion> v2) xs'" using wk_nat.prems finsert_absorb by fastforce
    then obtain c' where "{|v1, v2|} |\<union>| xs' \<turnstile> c' : {|v|}" and "c' < k" 
      using wk_nat.IH[of v v1 v2 xs'] wk_nat.prems by blast
    then show ?thesis by auto
  next
    case False
    then have xs: "xs = finsert (v1\<squnion>v2) (xs'|-| {|VNat n|})" using wk_nat.prems(2) by auto
    have v12_xs: "v1 \<squnion> v2 |\<notin>| xs' |-| {|VNat n|}" using wk_nat.prems by auto      
    obtain c' where cp: "{|v1, v2|} |\<union>| (xs'|-| {|VNat n|}) \<turnstile> c' : {|v|}" and cp_k: "c' < k" 
      using wk_nat.IH[of v v1 v2 "xs'|-| {|VNat n|}"] xs v12_xs wk_nat.prems(1) by blast
    have "finsert (VNat n) ({|v1, v2|} |\<union>| (xs'|-| {|VNat n|})) \<turnstile> Suc c' : {|v|}" using cp
         deduce_le.wk_nat[of "({|v1, v2|} |\<union>| (xs'|-| {|VNat n|}))" c' v n] by simp
    then have "{|v1, v2|} |\<union>| xs' \<turnstile> Suc c' : {|v|}" 
      by (metis False finsertI1 finsertI2 finsert_fminus finsert_fminus_single finsert_ident funion_finsert_right wk_nat.prems(2) xs)
    then show ?thesis using cp_k by auto
  qed
next
  case (wk_fun xs k vr va vb)
  show ?case
  proof (cases "va \<mapsto> vb |\<in>| xs")
    case True
    then have xs: "xs = finsert (v1 \<squnion> v2) xs'" using wk_fun.prems finsert_absorb by fastforce
    then obtain c' where "{|v1, v2|} |\<union>| xs' \<turnstile> c' : {|v|}" and "c' < k" 
      using wk_fun.IH[of v v1 v2 xs'] wk_fun.prems by blast
    then show ?thesis by auto
  next
    case False
    then have xs: "xs = finsert (v1\<squnion>v2) (xs'|-| {|va \<mapsto> vb|})" using wk_fun.prems(2) by auto
    have v12_xs: "v1 \<squnion> v2 |\<notin>| xs' |-| {|va \<mapsto> vb|}" using wk_fun.prems by auto      
    obtain c' where cp: "{|v1, v2|} |\<union>| (xs'|-| {|va \<mapsto> vb|}) \<turnstile> c' : {|v|}" and cp_k: "c' < k" 
      using wk_fun.IH[of v v1 v2 "xs'|-| {|va \<mapsto> vb|}"] xs v12_xs wk_fun.prems(1) by blast
    have "finsert (va \<mapsto> vb) ({|v1, v2|} |\<union>| (xs'|-| {|va \<mapsto> vb|})) \<turnstile> Suc c' : {|v|}" using cp
         deduce_le.wk_fun[of "({|v1, v2|} |\<union>| (xs'|-| {|va \<mapsto> vb|}))" c' v] by simp
    then have "{|v1, v2|} |\<union>| xs' \<turnstile> Suc c' : {|v|}" 
      by (metis False finsertI1 finsertI2 finsert_fminus finsert_fminus_single finsert_ident funion_finsert_right wk_fun.prems(2) xs)
    then show ?thesis using cp_k by auto
  qed
next
  case (empty_R xs k)
  then show ?case by auto
next
  case (cons_R xs k ys1 ys2)
  have "ys1 = {|v|} \<or> ys2 = {|v|}" using cons_R.prems by blast
  then show ?case
  proof
    assume "ys1 = {|v|}"
    then obtain c1' where "{|v1, v2|} |\<union>| xs' \<turnstile> c1' : {|v|}" and "c1' < k"
      using cons_R.IH(1)[of v v1 v2 xs'] cons_R.prems by blast
    then show ?case by (rule_tac x="c1'" in exI) simp 
  next
    assume ys2_v: "ys2 = {|v|}"
    then obtain c2' where "{|v1, v2|} |\<union>| xs' \<turnstile> c2' : {|v|}" and "c2' < k" using cons_R.IH(2) cons_R.prems by blast
    then show ?case by (rule_tac x="c2'" in exI) simp
  qed
next
  case (union_R xs k va vb)
  let ?xs = "{|v1, v2|} |\<union>| xs'"
  obtain c1 where a: "?xs \<turnstile> c1 : {|va|}" and c1_c: "c1 < k" using union_R.IH(1) union_R.prems by blast
  obtain c2 where b: "?xs \<turnstile> c2 : {|vb|}" and c2_c: "c2 < k" using union_R.IH(2) union_R.prems by blast
  have "?xs \<turnstile> Suc (max c1 c2) : {|va \<squnion> vb|}" using a b c1_c c2_c 
    using deduce_le.union_R weaken_size by auto
  then show ?case using c1_c c2_c union_R.prems by (rule_tac x="Suc (max c1 c2)" in exI) auto
next
  case (union_L va vb xs k vr)
  show ?case
  proof (cases "v1 \<squnion> v2 = va \<squnion> vb")
    case True then have v12_vab: "v1 \<squnion> v2 = va \<squnion> vb" by simp
    show ?thesis
    proof (cases "v1 \<squnion> v2 |\<in>| xs")
      case True
      have xs: "xs = finsert (v1 \<squnion> v2) xs'" using v12_vab True union_L.prems finsert_absorb by force
      have 1: "{|va, vb|} |\<union>| xs = finsert (v1 \<squnion> v2) ({|va, vb|} |\<union>| xs')" by (simp add: xs)
      have 2: "v1 \<squnion> v2 |\<notin>| {|va, vb|} |\<union>| xs'" using union_L.prems v12_vab apply auto
        apply (metis add.assoc add_eq_0_iff_both_eq_0 add_eq_self_zero n_not_Suc_n val.size_gen(3))
        apply (metis add.right_neutral nat_add_left_cancel_less not_add_less2 val.size_gen(3) zero_less_Suc)
        done
      from union_L.IH[of v v1 v2 "{|va,vb|} |\<union>| xs'"] 1 2 union_L.prems(1)
      obtain c' where "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs') \<turnstile> c' : {|v|}" and "c' < k" by blast      
      then show ?thesis by (metis less_SucI sup_left_idem v12_vab val.inject(3))
    next
      case False
      then have xs_xsp: "xs = xs'" using v12_vab union_L.prems finsert_ident by fastforce
      show ?thesis using union_L(1) v12_vab xs_xsp union_L.prems(1) by auto  
    qed
  next
    case False then have v12_vab: "v1 \<squnion> v2 \<noteq> va \<squnion> vb" by simp
    have vab_xsp: "va \<squnion> vb |\<in>| xs'" using v12_vab union_L.prems(2) by auto
    have v12_xs: "v1 \<squnion> v2 |\<in>| xs" using union_L.prems(2) v12_vab by fastforce
    show ?thesis
    proof (cases "va \<squnion> vb |\<in>| xs")
      case True
      let ?xs = "{|va, vb|} |\<union>| xs'"
      have 1: "{|va, vb|} |\<union>| xs = finsert (v1 \<squnion> v2) ?xs"
        using union_L.prems(2) v12_vab True finsert_absorb by force
      have 2: "v1 \<squnion> v2 |\<notin>| {|va, vb|} |\<union>| xs'" sorry
      from union_L.IH[of v v1 v2 ?xs] union_L.prems(1) 1 2
      obtain c' where "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs') \<turnstile> c' : {|v|}" and "c' < k" 
        by blast
        
      then show ?thesis sorry
    next
      case False
      then have 1: "{|va, vb|} |\<union>| xs = finsert (v1 \<squnion> v2) ({|va, vb|} |\<union>| (xs' |-| {|va\<squnion>vb|}))"
        using union_L.prems(2) v12_vab by blast 
      
      then show ?thesis sorry
    qed
      
      
        
    then show ?thesis sorry
  qed
    
next
  case (le_nat n k)
  then show ?case sorry
next
  case (le_arrow xs v1 k v2)
  then show ?case sorry
qed
  
  
(*  
lemma union_Le: "\<lbrakk> xs \<turnstile> c : ys; ys = {|v|}; xs = finsert (v1\<squnion>v2) xs' \<rbrakk> \<Longrightarrow>
                  \<exists>c'. {|v1,v2|} |\<union>| (xs - {|v1\<squnion>v2|}) \<turnstile> c' : {|v|} \<and> c' < c"
proof (induction xs c ys arbitrary: v1 v2 v xs' rule: deduce_le.induct)
  case (wk_nat xs c ys n)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  obtain c' where a: "?xs \<turnstile> c' : {|v|}" and cp_c: "c' < c" using wk_nat.IH wk_nat.prems by blast
  then have "finsert (VNat n) ?xs \<turnstile> Suc c' : {|v|}" using deduce_le.wk_nat by blast
  then show ?case using cp_c apply (rule_tac x="Suc c'" in exI) by (simp add: finsert_fminus_if)
next
  case (wk_fun xs c ys va vb)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  obtain c' where a: "?xs \<turnstile> c' : {|v|}" and cp_c: "c' < c" using wk_fun by blast
  then have "finsert (VArrow va vb) ?xs \<turnstile> Suc c' : {|v|}" using deduce_le.wk_fun by blast
  then show ?case using cp_c apply (rule_tac x="Suc c'" in exI) by (simp add: finsert_fminus_if)
next
  case (empty_R xs)
  then show ?case by auto
next
  case (cons_R xs c ys1 ys2)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  have "ys1 = {|v|} \<or> ys2 = {|v|}" using cons_R.prems by blast
  then show ?case
  proof
    assume "ys1 = {|v|}"
    then obtain c1' where "?xs \<turnstile> c1' : {|v|}" and "c1' < c" using cons_R.IH(1) cons_R.prems by blast
    then show ?case by (rule_tac x="c1'" in exI) simp 
  next
    assume ys2_v: "ys2 = {|v|}"
    then obtain c2' where "?xs \<turnstile> c2' : {|v|}" and "c2' < c" using cons_R.IH(2) cons_R.prems by blast
    then show ?case by (rule_tac x="c2'" in exI) simp
  qed
next
  case (union_R xs c va vb v1 v2)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  obtain c1 where a: "?xs \<turnstile> c1 : {|va|}" and c1_c: "c1 < c" using union_R.IH(1) union_R.prems by blast
  obtain c2 where b: "?xs \<turnstile> c2 : {|vb|}" and c2_c: "c2 < c" using union_R.IH(2) union_R.prems by blast
  have "?xs \<turnstile> Suc (max c1 c2) : {|va \<squnion> vb|}" using a b c1_c c2_c 
    using deduce_le.union_R weaken_size by auto
  then show ?case using c1_c c2_c union_R.prems by (rule_tac x="Suc (max c1 c2)" in exI) auto
next
  case (union_L va vb xs c vr)
  let ?F = "\<lambda> xs. {|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  have "(v1 \<squnion> v2 = va \<squnion> vb) \<or> (v1 \<squnion> v2 |\<in>| xs \<and> v1 \<squnion> v2 \<noteq> va \<squnion> vb)" 
    using union_L by blast
  then show ?case
  proof
    assume 2: "v1 \<squnion> v2 = va \<squnion> vb"
    have 3: "{|va, vb|} |\<union>| xs \<turnstile> c : {|v|}" using union_L by blast      
    show ?thesis
    proof (cases "v1 \<squnion> v2 |\<in>| xs")
      case True
      then have 3: "v1 \<squnion> v2 |\<in>| {|va, vb|} |\<union>| xs" by auto
      obtain c' where cp: "?F ({|va, vb|} |\<union>| xs) \<turnstile> c' : {|v|}" and cp_c: "c' < c"
        using union_L.IH[of v] 3 union_L.prems by blast
      have "?F ({|va, vb|} |\<union>| xs) = ?F (finsert (va \<squnion> vb) xs)"
        using 2 finsert_absorb by blast
      then show ?thesis using cp cp_c by (rule_tac x=c' in exI) simp        
    next
      case False
      then have "?F (finsert (va \<squnion> vb) xs) = {|va, vb|} |\<union>| xs" using 2 by simp
      then show ?thesis using 3 by (rule_tac x=c in exI) simp
    qed  
  next
    assume 2: "v1 \<squnion> v2 |\<in>| xs \<and> v1 \<squnion> v2 \<noteq> va \<squnion> vb"     
    have 3: "v1 \<squnion> v2 |\<in>| {|va, vb|} |\<union>| xs" using 2 by auto      
    obtain c' where cp: "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|v|}" 
      and cp_c: "c' < c" using union_L.IH 3 union_L.prems by blast
        
(*    
    have "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|})
           |\<subseteq>| {|va,vb|} |\<union>| ({|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|}))" by auto
    then obtain c'' where "{|va,vb|} |\<union>| ({|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})) \<turnstile> c'' : {|v|}" 
      using weaken cp by presburger
    then have "finsert (va\<squnion>vb) ({|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})) \<turnstile> Suc c'' : {|v|}" by blast
    then have "{|v1, v2|} |\<union>| (finsert (va\<squnion>vb) (xs |-| {|v1 \<squnion> v2|})) \<turnstile> Suc c'' : {|v|}" by auto
    then show ?thesis using 2 apply (rule_tac x="Suc c''" in exI) 
      by (metis finsert_fminus_if fsingleton_iff)
*)
  show ?thesis sorry
  qed
next
  case (le_nat n)
  then have "False" by auto
  then show ?case ..
next
  case (le_arrow xs y1 c1 c2 y2 v1 v2)
  then have "False" by auto
  then show ?case ..
qed

(*
section "Size of Finite Sets of Values"  
  
fun vadd :: "(val \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "vadd (_,v) r = v + r"
  
abbreviation vprod_size :: "val \<Rightarrow> (val \<times> nat)" where
  "vprod_size \<equiv> (\<lambda> v. (v,size v))"

definition fsize :: "val fset \<Rightarrow> nat" where
  "fsize t \<equiv> ffold vadd 0 (fimage vprod_size t)"
  
interpretation vadd_vprod: comp_fun_commute "vadd \<circ> vprod_size"
  unfolding comp_fun_commute_def by auto  

lemma vprod_size_inj: "inj_on vprod_size (fset A)"
  unfolding inj_on_def by auto
    
lemma fsize_finsert_in[simp]:
  assumes v12_t: "v12 |\<in>| t" shows "fsize (finsert v12 t) = fsize t"
proof -
  from v12_t have "finsert v12 t = t" by auto
  from this show ?thesis by simp
qed

lemma fsize_finsert_notin[simp]: 
  assumes v12_t: "v12 |\<notin>| t"
  shows "fsize (finsert v12 t) = size v12 + fsize t"
proof -
  let ?f = "vadd \<circ> vprod_size"
  have "fsize (finsert v12 t) = ffold ?f 0 (finsert v12 t)"
    unfolding fsize_def using v12_t apply simp
    by (metis (no_types, lifting) comp_apply ffold_fimage fimage_finsert finsert_absorb2 fminus_finsert_absorb vadd.simps vadd_vprod.ffold_finsert_fremove vprod_size_inj)
  also from v12_t have "... = ?f v12 (ffold ?f 0 t)" by simp
  finally have "fsize (finsert v12 t) = ?f v12 (ffold ?f 0 t)" .
  from this show ?thesis unfolding fsize_def apply auto
    by (simp add: ffold_fimage vprod_size_inj)
qed

lemma size_fset_mem[simp]: "v \<in> fset f \<Longrightarrow> size v  \<le> fsize f"
  by (induction f) auto

lemma fsize_union[simp]: "fsize (x1 |\<union>| x2) \<le> fsize x1 + fsize x2"
  apply (induction x1)
   apply force
  by (smt add.commute add.left_commute dual_order.trans fsize_finsert_in fsize_finsert_notin funion_finsert_left le_add2 nat_add_left_cancel_le)
    
lemma fsize_empty[simp]: "fsize {||} = 0"
  unfolding fsize_def by auto
    
lemma dom_finsert[simp]: "all_funs (finsert x ys) \<Longrightarrow>
               dom |`| (finsert x ys) = finsert (dom x) (dom |`| ys)"
  by simp
    
lemma mem_cod: "\<lbrakk> all_funs ys; \<forall>x1. x1\<mapsto>x2 |\<notin>| ys \<rbrakk> \<Longrightarrow> x2 |\<notin>| (cod|`|ys)"
  apply (induction ys arbitrary: x2) 
   apply force
   apply (subgoal_tac "is_fun x") prefer 2 apply force
  apply (case_tac x) apply force prefer 2 apply force
  apply simp
  done
    
lemma fsize_funs[simp]: "all_funs ys \<Longrightarrow> fsize (dom|`|ys) + fsize(cod|`|ys) \<le> fsize ys"
  apply (induction ys)
   apply force
  apply (subgoal_tac "is_fun x") prefer 2 apply force apply (case_tac x) apply force
    prefer 2 apply force apply simp
   apply (case_tac "dom x |\<in>| (dom|`|ys)") apply simp
   apply (case_tac "cod x |\<in>| (cod|`|ys)") apply force apply force
  apply simp apply (case_tac "cod x |\<in>| (cod|`|ys)") apply force apply force
  done
    
lemma fsize_subset[simp,intro]: "xs |\<subseteq>| ys \<Longrightarrow> fsize xs \<le> fsize ys"
  apply (induction ys arbitrary: xs)
   apply force
  apply simp 
  apply (case_tac "x |\<in>| xs")
    apply (subgoal_tac "\<exists>xs'. xs = finsert x xs' \<and> x |\<notin>| xs'") prefer 2 
    apply (simp add: mk_disjoint_finsert)
   apply (erule exE) apply (erule conjE)
   apply simp apply blast
  apply (subgoal_tac "xs |\<subseteq>| ys") prefer 2 apply blast
  apply (subgoal_tac "fsize xs \<le> fsize ys") prefer 2 apply blast
  apply arith
  done
    
section "Cut Elimination"
    
lemma deduce_mem_inv: "\<lbrakk> xs \<turnstile> c : ys; v |\<in>| ys \<rbrakk> \<Longrightarrow> \<exists>c'. xs \<turnstile> c' : {|v|}"
  apply (induction ys arbitrary: xs c v)
   apply force
  apply (erule deduce_finsert_inv)
        apply blast+
      defer
      apply blast+
     apply (subgoal_tac "ys = bot \<or> ys = {|x|}") prefer 2 apply blast
     apply (erule disjE)
      apply force     
     apply force
    apply (subgoal_tac "ys = bot \<or> ys = {|VNat n|}") prefer 2 apply blast
    apply (erule disjE)
     apply force     
    apply force
   apply (subgoal_tac "ys = bot \<or> ys = {|v1 \<mapsto> v1'|}") prefer 2 apply blast
   apply (erule disjE)
    apply force     
   apply force
  using weaken_right apply blast
  done
       
lemma cut: "\<forall>xs ys zs c1 c2. m = (fsize ys, size c1, size c2) \<longrightarrow>
   xs \<turnstile> c1 : ys \<longrightarrow> xs |\<union>| ys \<turnstile> c2 : zs \<longrightarrow> (\<exists>c3. xs \<turnstile> c3 : zs)" (is "?P m")
proof (induction m rule: wf_induct[of "less_than <*lex*> (less_than <*lex*> less_than)"])
  case 1
  then show ?case by auto
next
  case (2 m)
  then show ?case
  proof clarify
    fix xs ys zs c1 c2
    assume IH: "\<forall>m'. (m', fsize ys, size c1, size c2) \<in> less_than <*lex*> (less_than <*lex*> less_than) \<longrightarrow> ?P m'" and
       m: "m = (fsize ys, size c1, size c2)" and
       c1: "xs \<turnstile> c1 : ys" and c2: "xs |\<union>| ys \<turnstile> c2 : zs"
    from c2 show "\<exists>c3. xs \<turnstile> c3 : zs"
    proof
      fix xys c2' v n assume xs_ys: "xs |\<union>| ys = finsert (VNat n) xys" and
        c2_c2p: "c2 = CWkNat c2'" and zs: "zs = {|v|}" and c2p: "xys \<turnstile> c2' : {|v|}"

      show ?thesis
      proof (cases "VNat n |\<in>| xys")
        case True
        then have "xys = xs |\<union>| ys" using xs_ys by auto
        then have "xs|\<union>|ys \<turnstile> c2' : {|v|}" using c2p by simp
        then have "\<exists>c3. xs \<turnstile> c3 : {|v|}" using IH c1
          apply (erule_tac x="(fsize ys, size c1, size c2')" in allE)
            apply (erule impE) using c2_c2p apply force
            apply blast done
        then show ?thesis using zs by simp
      next
        case False then have n_xys: "VNat n |\<notin>| xys" by blast
        then have xys: "xys = (xs - {|VNat n|}) |\<union>| (ys - {|VNat n|})" using xs_ys by auto
        show ?thesis
        proof (cases "VNat n |\<in>| ys")
          assume n_ys: "VNat n |\<in>| ys"          
          then have "fsize (ys - {|VNat n|}) < fsize ys" sorry
            
          show ?thesis sorry
        next
          assume n_ys: "VNat n |\<notin>| ys"
          then have xys2: "xys = (xs - {|VNat n|}) |\<union>| ys" using xys by simp
          have n_xs: "VNat n |\<in>| xs" using xs_ys n_ys by auto
          then obtain xs' where xs_xsp: "xs = finsert (VNat n) xs'" and n_xsp: "VNat n |\<notin>| xs'"
            by (meson mk_disjoint_finsert)
          have c2p2: "xs' |\<union>| ys \<turnstile> c2' : {|v|}" using c2p xys2 xs_xsp n_xsp by auto
                        
          show ?thesis sorry
        qed
      qed
    next
      assume "c2 = CNil" and zs: "zs = {||}"
      have "xs \<turnstile> CNil : zs" using zs by auto
      then show ?thesis by blast
    next
      fix xsa c2a zs1 c2b zs2
      assume xsa: "xs |\<union>| ys = xsa" and c2: "c2 = CCons c2a c2b" and
        zs: "zs = zs1 |\<union>| zs2" and c2a_: "xsa \<turnstile> c2a : zs1" and c2b_: "xsa \<turnstile> c2b : zs2"
      have c2a: "xs |\<union>| ys \<turnstile> c2a : zs1" using c2a_ xsa by blast
      have c2b: "xs |\<union>| ys \<turnstile> c2b : zs2" using c2b_ xsa by blast
      from c1 c2a xsa IH c2 have "\<exists>c. xs \<turnstile> c : zs1" 
        apply (erule_tac x="(fsize ys, size c1, size c2a)" in allE) apply (erule impE) apply force
        apply blast done
      then obtain c3 where c3: "xs \<turnstile> c3 : zs1" by blast
      from c1 c2b xsa IH c2 have "\<exists>c. xs \<turnstile> c : zs2" 
        apply (erule_tac x="(fsize ys, size c1, size c2b)" in allE) apply (erule impE) apply force
        apply blast done
      then obtain c4 where c4: "xs \<turnstile> c4 : zs2" by blast
      show ?thesis using c3 c4 zs by blast
    next
      show ?thesis sorry
    next
      show ?thesis sorry
    next
      (*
      fix n xsa assume xsa: "xs |\<union>| ys = xsa" and "c2 = CNat n" and zs: "zs = {|VNat n|}"
        and n_xsa: "VNat n |\<in>| xsa"
      have "VNat n |\<in>| xs \<or> VNat n |\<in>| ys" using n_xsa xsa by auto
      then show ?thesis
      proof
        assume "VNat n |\<in>| xs"
        then show ?thesis using zs by blast
      next
        assume n_ys: "VNat n |\<in>| ys"
        then have "{|VNat n|} |\<subseteq>| ys" by blast
        with c1 obtain c1' where c1p: "xs \<turnstile> c1' : {|VNat n|}" using weaken_right by blast
        with zs show ?thesis by blast
      qed
*)
      show ?thesis sorry
    next
      show ?thesis sorry
(*
      fix fs xsa z1 c2a c2b z2
      assume xsa: "xs |\<union>| ys = xsa" and c2: "c2 = CArrow c2a c2b" and zs: "zs = {|z1 \<mapsto> z2|}" 
         and xsp_xsa: "fs |\<subseteq>| xsa" and af_fs: "all_funs fs" and 
         c2a: "{|z1|} \<turnstile> c2a : dom |`| fs" and c2b: "cod |`| fs \<turnstile> c2b : {|z2|}" 
      obtain xs' ys' where fs: "fs = xs'|\<union>| ys'" and xsp_xs: "xs'|\<subseteq>| xs" and ysp_ys: "ys'|\<subseteq>|ys" 
        using xsa xsp_xsa factor_union[of fs xs ys] by blast
      have af_xsp: "all_funs xs'" using af_fs fs by auto
      have af_ysp: "all_funs ys'" using af_fs fs by auto
      obtain c3a where c3a: "{|z1|} \<turnstile> c3a : dom |`| xs'"
        apply (subgoal_tac "dom |`| xs' |\<subseteq>| dom|`| fs") prefer 2 using fs apply force
        using c2a weaken_right apply blast done
      have c2b_: "(cod|`|xs') |\<union>| (cod|`|ys') \<turnstile> c2b : {|z2|}" 
        using fs by (metis c2b fimage_funion)
      have "\<exists> c11. cod |`| xs' \<turnstile> c11 : cod |`| ys' \<and> size c11 \<le> size c1" using c1
      proof (* using c1 xsp_xs ysp_ys 2 af_ysp *)
        show ?thesis sorry
      next
        show ?thesis sorry
      next
        show ?thesis sorry
      next
        show ?thesis sorry
      next
        show ?thesis sorry
      next
        show ?thesis sorry
            (*
        fix fs1 xs0 y1 c1a c1b y2 assume xs_xsz: "xs = xs0" and c1_arrow: "c1 = CArrow c1a c1b" and
          ys_arrow: "ys = {|y1 \<mapsto> y2|}" and fs1_xsz: "fs1 |\<subseteq>| xs0" and af_fs1: "all_funs fs1" and
          "{|y1|} \<turnstile> c1a : dom |`|fs1" and c1b: "cod |`| fs1 \<turnstile> c1b : {|y2|}"
        have "cod|`|fs1 |\<subseteq>| cod|`|xs'" using xs_xsz fs1_xsz xsp_xs sorry
          
        show "\<exists>c11. cod |`| xs' \<turnstile> c11 : cod |`| ys' \<and> size c11 \<le> size c1" 
         sorry*)
      next
        show ?thesis sorry
      next
        show ?thesis sorry
      qed
      then obtain c11 where c11: "cod |`| xs' \<turnstile> c11 : cod |`| ys'"  
        and c11_c1: "size c11 \<le> size c1" by blast
      have scysp_ys: "fsize (cod |`| ys') \<le> fsize ys"
        using fs xsa xsp_xsa af_fs ysp_ys apply simp
          apply (subgoal_tac "fsize (dom |`| ys') + fsize (cod |`| ys') \<le> fsize ys'")
         prefer 2 using fsize_funs[of ys'] apply blast
        apply (subgoal_tac "fsize ys' \<le> fsize ys") prefer 2 apply blast apply arith done
      have c2b_c11: "size c2b < size c2" using c2 by auto
      obtain c3b where c3b: "cod |`| xs' \<turnstile> c3b : {|z2|}" using c2b_ c11 IH
        apply (erule_tac x="(fsize (cod |`| ys'), size c11, size c2b)" in allE)
        apply (erule impE) using c2b_c11 c11_c1 scysp_ys apply force by blast
(*      have "xs \<turnstile> CArrow c3a c3b : {|z1 \<mapsto> z2|}" using xsp_xs af_xsp c3a c3b by blast
      then show ?thesis using zs by blast
*)
      show ?thesis sorry
*)
    next
      show ?thesis sorry
    qed
  qed
qed

*)
  
end