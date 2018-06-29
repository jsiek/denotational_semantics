theory ValuesLaurentFSet
  imports Main "~~/src/HOL/Library/FSet" 
begin

datatype val = VNat nat | VArrow val val (infix "\<mapsto>" 60) | VUnion val val (infix "\<squnion>" 59)
  
abbreviation is_fun :: "val \<Rightarrow> bool" where
  "is_fun v \<equiv> (case v of v1\<mapsto>v2 \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation all_funs :: "val fset \<Rightarrow> bool" where
  "all_funs xs \<equiv> ffold (\<lambda>v b. is_fun v \<and> b) True xs"

interpretation is_fun_commute: comp_fun_commute "(\<lambda>v b. is_fun v \<and> b)"
  unfolding comp_fun_commute_def by auto  
  
fun dom :: "val \<Rightarrow> val" where
  "dom (v\<mapsto>v') = v" 
  
fun cod :: "val \<Rightarrow> val" where
  "cod (v\<mapsto>v') = v'"

datatype coercion = CWkNat coercion | CWkFun coercion 
  | CNat nat | CArrow coercion coercion
  | CUnionR coercion coercion | CUnionL coercion | CNil | CCons coercion coercion

inductive deduce_le :: "val fset \<Rightarrow> coercion \<Rightarrow> val fset \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 56) where
  empty_R[intro!]: "xs \<turnstile> CNil : {||}" |
  cons_R[intro!]: "\<lbrakk> ys \<noteq> {||}; xs \<turnstile> c1 : {|v|}; xs \<turnstile> c2 : ys \<rbrakk> 
    \<Longrightarrow> xs \<turnstile> CCons c1 c2 : finsert v ys" |
  union_R[intro!]: "\<lbrakk> xs \<turnstile> c1 : {|v1|}; xs \<turnstile> c2 : {|v2|} \<rbrakk> \<Longrightarrow> xs \<turnstile> CUnionR c1 c2 : {|v1\<squnion>v2|}" |
  union_L[intro]:"\<lbrakk> {|v1,v2|}|\<union>|xs \<turnstile> c: {|v|} \<rbrakk>
                  \<Longrightarrow> finsert (v1\<squnion>v2) xs \<turnstile> CUnionL c: {|v|}" | 
  le_nat[intro!]: "VNat n |\<in>| xs \<Longrightarrow> xs \<turnstile> CNat n : {|VNat n|}" |
  le_arrow[intro!]: "\<lbrakk> xs' |\<subseteq>| xs; all_funs xs'; {|v1|} \<turnstile> c1 : dom|`|xs'; cod|`|xs' \<turnstile> c2 : {|v1'|}\<rbrakk>
    \<Longrightarrow> xs \<turnstile> CArrow c1 c2 : {|v1 \<mapsto> v1'|}"

inductive_cases
   cwknat_inv[elim!]: "xs \<turnstile> CWkNat c : ys" and
   cwkfun_inv[elim!]: "xs \<turnstile> CWkFun c : ys" and
   cunionr_inv[elim!]: "xs \<turnstile> CUnionR c1 c2 : ys" and
   cunionl_inv[elim!]: "xs \<turnstile> CUnionL c : ys" and
   cnat_inv[elim!]: "xs \<turnstile> CNat n : ys" and
   carrow_inv[elim!]: "xs \<turnstile> CArrow c1 c2 : ys" and
   cnil_inv[elim!]: "xs \<turnstile> CNil : ys" and
   ccons_inv[elim!]: "xs \<turnstile> CCons c1 c2 : ys"
  
lemma weaken: "\<lbrakk> xs \<turnstile> c : ys; xs |\<subseteq>| xs' \<rbrakk> \<Longrightarrow> \<exists> c'. xs' \<turnstile> c' : ys"
proof (induction xs c ys arbitrary: xs' rule: deduce_le.induct)
  case (union_L v1 v2 xs c vr)
  obtain xs'' where xsp: "xs' = finsert (v1 \<squnion> v2) xs''" using union_L by blast
  obtain c' where IH: "({|v1, v2|} |\<union>| xs') \<turnstile> c' : {|vr|}" using union_L by blast
  have 1: "finsert (v1\<squnion>v2) xs' \<turnstile> CUnionL c' : {|vr|}" 
    using IH ValuesLaurentFSet.union_L[of v1 v2 xs' c' vr] by blast
  have "finsert (v1\<squnion>v2) xs' = xs'" using xsp by simp
  then show ?case using 1 apply (rule_tac x="CUnionL c'" in exI) apply simp done
next
  case (le_arrow xs' xs v1 c1 c2 v1' xs2)
  then show ?case using deduce_le.le_arrow fsubset_trans by smt
qed blast+
  
lemma ax: "v |\<in>| xs \<Longrightarrow> \<exists>c. xs \<turnstile> c : {|v|}"
proof (induction v arbitrary: xs)
  case (VNat x)
  then show ?case by force
next
  case (VArrow v1 v2)
  let ?xs = "{|v1 \<mapsto> v2|}"
  have 1:"all_funs ?xs" by simp
  obtain c1 where 2: "{|v1|} \<turnstile> c1 : dom|`|?xs" using VArrow.IH(1) by auto
  obtain c2 where 3: "cod|`|?xs \<turnstile> c2 : {|v2|}" using VArrow.IH(2) by auto
  have "xs \<turnstile> CArrow c1 c2 : {|v1 \<mapsto> v2|}" using 1 2 3 VArrow.prems by blast
  then show ?case by blast
next
  case (VUnion v1 v2)
  obtain xs' where xs: "xs = finsert (v1\<squnion>v2) xs'" using VUnion.prems by blast
  have 1: "\<exists> c1. xs \<turnstile> c1 : {|v1|}"
  proof -
    obtain c1' where c1p: "{|v1,v2|}|\<union>|xs' \<turnstile> c1' : {|v1|}" using VUnion.IH by blast
    then have "finsert (v1\<squnion>v2) xs' \<turnstile> CUnionL c1' : {|v1|}" by blast
    then show ?thesis using xs apply (rule_tac x="CUnionL c1'" in exI) apply simp done
  qed
  have 2: "\<exists> c2. xs \<turnstile> c2 : {|v2|}"
  proof -
    obtain c2' where c2p: "{|v1,v2|}|\<union>|xs' \<turnstile> c2' : {|v2|}" using VUnion.IH by blast
    then have "finsert (v1\<squnion>v2) xs' \<turnstile> CUnionL c2' : {|v2|}" by blast
    then show ?thesis using xs apply (rule_tac x="CUnionL c2'" in exI) apply simp done
  qed
  show ?case using 1 2 by blast
qed

lemma all_funs_are_funs: "\<lbrakk> all_funs xs; v |\<in>| xs \<rbrakk> \<Longrightarrow> \<exists>v1 v2. v = v1\<mapsto>v2"
  apply (induction xs) apply auto apply (case_tac v) apply auto done
  
lemma union_Le: "\<lbrakk> xs \<turnstile> c : ys; ys = {|vr|}; (v1\<squnion>v2) |\<in>| xs;
                   {|v1,v2|} |\<union>| (xs |-| {|v1\<squnion>v2|}) |\<subseteq>| xs'\<rbrakk> \<Longrightarrow>
                  \<exists>c'. xs' \<turnstile> c' : {|vr|}"
proof (induction xs c ys arbitrary: vr v1 v2 xs' rule: deduce_le.induct)
  case (empty_R xs)
  then have "False" by auto
  then show ?case ..
next
  case (cons_R ys xs c1 v c2)
  then show ?case by auto
next
  case (union_R xs c1 va c2 vb)
  obtain c1 where a: "xs' \<turnstile> c1 : {|va|}" using union_R.IH(1) union_R.prems by blast
  obtain c2 where b: "xs' \<turnstile> c2 : {|vb|}" using union_R.IH(2) union_R.prems by blast
  have "xs' \<turnstile> CUnionR c1 c2 : {|va \<squnion> vb|}" using a b by blast
  then show ?case using union_R by blast
next
  case (union_L va vb xs c v)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  have vab_xs_c: "{|va, vb|} |\<union>| xs \<turnstile> c : {|v|}" using union_L by blast

  have "(v1 \<squnion> v2 = va \<squnion> vb) \<or> (v1 \<squnion> v2 |\<in>| xs \<and> v1 \<squnion> v2 \<noteq> va \<squnion> vb)" using union_L by blast
  then show ?case
  proof
    assume v12_vab: "v1 \<squnion> v2 = va \<squnion> vb" 
    have a: "?xs \<turnstile> c : {|vr|}" using vab_xs_c v12_vab union_L.hyps(1) union_L.prems(1) by auto
    have b: "?xs = {|v1, v2|} |\<union>| (finsert (va \<squnion> vb) xs |-| {|v1 \<squnion> v2|})" using v12_vab by simp 
    show ?thesis using a b by auto
  next
    assume v12_xs: "v1 \<squnion> v2 |\<in>| xs \<and> v1 \<squnion> v2 \<noteq> va \<squnion> vb"
    let ?abxs = "finsert (va \<squnion> vb) xs"
    have "{|v1, v2|} |\<union>| (finsert (va \<squnion> vb) xs |-| {|v1 \<squnion> v2|})
         = {|v1, v2|} |\<union>| (?abxs |-| {|v1 \<squnion> v2|})" 
      using v12_xs by simp
      
        
    have "\<exists>c'. {|v1, v2|} |\<union>| (finsert (va \<squnion> vb) xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|vr|}"
    proof (cases "{|va\<squnion>vb|} |\<inter>| {|v1,v2|} = bot \<and> {|v1\<squnion>v2|} |\<inter>| {|va,vb|} = bot")
      case True
      have 10: "{|v1\<squnion>v2|} |\<inter>| {|va,vb|} = bot" using True by blast
      have 3: "va\<squnion>vb |\<notin>| ?xs" using union_L(1) union_L.prems True by auto 
      have 1: "finsert (va \<squnion> vb) ?xs
               = {|v1, v2|} |\<union>| (finsert (va \<squnion> vb) xs |-| {|v1 \<squnion> v2|})" using v12_xs by auto
      have 4: "v1 \<squnion> v2 |\<in>| {|va, vb|} |\<union>| xs" using union_L.prems v12_xs by auto
      obtain c' where 7: "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|v|}" 
        using union_L.IH[of v v1 v2] 4 by blast
      have 8: "finsert va (finsert vb xs) |-| {|v1 \<squnion> v2|} = finsert va (finsert vb (xs |-| {|v1 \<squnion> v2|}))" 
        using 10 by auto 
      have "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|}) = {|va,vb|}|\<union>| ?xs" 
        using union_L(1) union_L.prems 8 by (simp add: finsert_commute)
      with 7 union_L(4) have "{|va,vb|}|\<union>| ?xs \<turnstile> c' : {|vr|}" by simp
      then have 2: "finsert (va \<squnion> vb) ?xs \<turnstile> CUnionL c' : {|vr|}"
        using 3 ValuesLaurentFSet.union_L by blast
      show ?thesis using 1 2 by (rule_tac x="CUnionL c'" in exI) simp
    next
      case False
      have "{|v1, v2|} |\<union>| (finsert (va \<squnion> vb) xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|vr|}" 
        sorry   
      then show ?thesis by blast
    qed  
    then show ?case by blast
  qed
next
  case (le_nat n)
  then have "False" by auto
  then show ?case ..
next
  case (le_arrow xs v1 c1 c2 v1')
  then have "False" using all_funs_are_funs[of xs "v1\<squnion>v2"] by blast
  then show ?case ..
qed
         
    
    
end