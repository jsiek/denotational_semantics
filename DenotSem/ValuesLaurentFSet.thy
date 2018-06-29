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
  cons_R[intro!]: "\<lbrakk> xs \<turnstile> c1 : ys1; xs \<turnstile> c2 : ys2 \<rbrakk> 
    \<Longrightarrow> xs \<turnstile> CCons c1 c2 : ys1 |\<union>| ys2" |
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
  
lemma union_Le: "\<lbrakk> xs \<turnstile> c : ys;  (v1\<squnion>v2) |\<in>| xs;
                   {|v1,v2|} |\<union>| (xs |-| {|v1\<squnion>v2|}) |\<subseteq>| xs'\<rbrakk> \<Longrightarrow>
                  \<exists>c'. xs' \<turnstile> c' : ys"
proof (induction xs c ys arbitrary: v1 v2 xs' rule: deduce_le.induct)
  case (empty_R xs)
  then show ?case by auto
next
  case (cons_R xs c1 ys1 c2 ys2)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  obtain c1' where c1p: "xs' \<turnstile> c1' : ys1" using cons_R.IH(1) cons_R.prems by blast
  obtain c2' where c2p: "xs' \<turnstile> c2' : ys2" using cons_R.IH(2) cons_R.prems by blast
  have "xs' \<turnstile> CCons c1' c2' : ys1 |\<union>| ys2" using c1p c2p by blast
  then show ?case by meson
next
  case (union_R xs c1 va c2 vb)
  obtain c1 where a: "xs' \<turnstile> c1 : {|va|}" using union_R.IH(1) union_R.prems by blast
  obtain c2 where b: "xs' \<turnstile> c2 : {|vb|}" using union_R.IH(2) union_R.prems by blast
  have "xs' \<turnstile> CUnionR c1 c2 : {|va \<squnion> vb|}" using a b by blast
  then show ?case using union_R by blast
next
  case (union_L va vb xs c v) 
  have "(v1 \<squnion> v2 = va \<squnion> vb) \<or> (v1 \<squnion> v2 |\<in>| xs \<and> v1 \<squnion> v2 \<noteq> va \<squnion> vb)" using union_L by blast
  then show ?case
  proof
    assume 2: "v1 \<squnion> v2 = va \<squnion> vb"
    have 3: "{|va, vb|} |\<union>| xs \<turnstile> c : {|v|}" using union_L by blast      
    show ?thesis
    proof (cases "v1 \<squnion> v2 |\<in>| xs")
      case True
      then have 3: "v1 \<squnion> v2 |\<in>| {|va, vb|} |\<union>| xs" by auto
      have 4: "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|}) |\<subseteq>| xs'"
        using union_L 2 by auto
      obtain c' where cp: "xs' \<turnstile> c' : {|v|}" using union_L.IH 3 4 by blast
      then show ?thesis using union_L(3) by blast
    next
      case False
      then have "{|va, vb|} |\<union>| xs |\<subseteq>| xs'" using union_L 2 by auto
      then show ?thesis using 3 weaken union_L(3) by blast
    qed        
  next
    assume 2: "v1 \<squnion> v2 |\<in>| xs \<and> v1 \<squnion> v2 \<noteq> va \<squnion> vb"     
    have 3: "v1 \<squnion> v2 |\<in>| {|va, vb|} |\<union>| xs" using 2 by auto  
    have 1: "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|}) |\<subseteq>| {|va, vb|} |\<union>| xs'"
      using union_L by auto
    obtain c' where cp: "{|va, vb|} |\<union>| xs' \<turnstile> c' : {|v|}" 
      using union_L.IH 1 3 by blast
    then have "finsert (va\<squnion>vb) xs' \<turnstile> CUnionL c' : {|v|}" by blast
    moreover have "finsert (va\<squnion>vb) xs' = xs'" using union_L 2 by auto
    ultimately show ?thesis using union_L(3) by (rule_tac x="CUnionL c'" in exI) auto 
  qed
next
  case (le_nat n)
  then show ?case by auto
next
  case (le_arrow ys' ys va c1 c2 vb)
  have "ys' |\<subseteq>| xs'" using le_arrow(1) le_arrow(2) le_arrow(8) all_funs_are_funs by auto            
  moreover have "ys' \<turnstile> CArrow c1 c2 : {|va\<mapsto>vb|}" using le_arrow by blast
  ultimately show "\<exists>c'. xs' \<turnstile> c' : {|va\<mapsto>vb|}" using weaken[of ys' "CArrow c1 c2"] by blast
qed

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
    assume IH: "\<forall>m'. (m', fsize ys, size c1, size c2) \<in> less_than <*lex*> less_than <*lex*> less_than \<longrightarrow> ?P m'" and
       m: "m = (fsize ys, size c1, size c2)" and
       c1: "xs \<turnstile> c1 : ys" and c2: "xs |\<union>| ys \<turnstile> c2 : zs"
    from c2 show "\<exists>c3. xs \<turnstile> c3 : zs"
    proof
      assume "c2 = CNil" and zs: "zs = {||}"
      have "xs \<turnstile> CNil : zs" using zs by auto
      then show ?thesis by blast
    next
      fix xsa c2a zs1 c2b zs2
      assume xsa: "xs |\<union>| ys = xsa" and c2: "c2 = CCons c2a c2b" and
        zs: "zs = zs1 |\<union>| zs2" and c2a: "xsa \<turnstile> c2a : zs1" and c2b: "xsa \<turnstile> c2b : zs2"
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
      show ?thesis sorry
    next
      show ?thesis sorry
    qed  
  qed
qed

end