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
  cons_R[intro!]: "\<lbrakk> v |\<notin>| ys; ys \<noteq> {||}; xs \<turnstile> c1 : {|v|}; xs \<turnstile> c2 : ys \<rbrakk> 
    \<Longrightarrow> xs \<turnstile> CCons c1 c2 : finsert v ys" |
  wk_nat[intro!]: "\<lbrakk> VNat n |\<notin>| xs; xs \<turnstile> c : {|v|} \<rbrakk> \<Longrightarrow> finsert (VNat n) xs \<turnstile> CWkNat c : {|v|}" | 
  wk_fun[intro!]: "\<lbrakk> v1\<mapsto>v1' |\<notin>| xs; xs \<turnstile> c : {|v|} \<rbrakk> \<Longrightarrow> finsert (v1\<mapsto>v1') xs \<turnstile> CWkFun c : {|v|}" |
  union_R[intro!]: "\<lbrakk> xs \<turnstile> c1 : {|v1|}; xs \<turnstile> c2 : {|v2|} \<rbrakk> \<Longrightarrow> xs \<turnstile> CUnionR c1 c2 : {|v1\<squnion>v2|}" |
  union_L[intro]:"\<lbrakk> v1\<squnion>v2|\<notin>|xs; {|v1,v2|}|\<union>|xs \<turnstile> c: {|v|}  \<rbrakk>\<Longrightarrow> finsert (v1\<squnion>v2) xs \<turnstile> CUnionL c: {|v|}" | 
  le_nat[intro!]: "{|VNat n|} \<turnstile> CNat n : {|VNat n|}" |
  le_arrow[intro!]: "\<lbrakk> all_funs xs; {|v1|} \<turnstile> c1 : dom|`|xs; cod|`|xs \<turnstile> c2 : {|v1'|} \<rbrakk>
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
  
lemma wk_gen: "\<lbrakk> v |\<notin>| xs; xs \<turnstile> c : {|v'|}\<rbrakk> \<Longrightarrow> \<exists> c'. finsert v xs \<turnstile> c' : {|v'|}"
proof (induction v arbitrary: xs v' c)
  case (VNat n)
  have "finsert (VNat n) xs \<turnstile> CWkNat c : {|v'|}" using VNat wk_nat by blast    
  then show ?case by meson
next
  case (VArrow v1 v2)
  have "finsert (v1\<mapsto>v2) xs \<turnstile> CWkFun c : {|v'|}" using VArrow.prems wk_fun by blast    
  then show ?case  by meson
next
  case (VUnion v1 v2)
  have 1: "xs \<turnstile> c : {|v'|}" using VUnion.prems by simp
  have "\<exists>c'. {|v1,v2|}|\<union>|xs \<turnstile> c' : {|v'|}"
  proof (cases "v1 |\<in>| xs")
    case True then have v1_xs: "v1 |\<in>| xs" .
    show ?thesis
    proof (cases "v2 |\<in>| xs")
      case True  
      then have "xs = {|v1,v2|}|\<union>|xs" using v1_xs by auto
      then show ?thesis using 1 by auto
    next
      case False
      then obtain c' where 2: "finsert v2 xs \<turnstile> c' : {|v'|}" using 1 VUnion.IH(2) by blast
      then show ?thesis using v1_xs 
        by (metis finsert_fminus finsert_fminus_single finsert_is_funion funion_finsert_left 
            funion_finsert_right)
    qed
  next
    case False then have v1_xs: "v1 |\<notin>| xs" .
    obtain c' where 2: "finsert v1 xs \<turnstile> c' : {|v'|}" using v1_xs 1 VUnion.IH(1) by blast
    show ?thesis
    proof (cases "v2 |\<in>| finsert v1 xs")
      case True then have v2_xs: "v2 |\<in>| finsert v1 xs" .
      show ?thesis using v2_xs 2 by (metis finsert_fminus finsert_fminus_single finsert_is_funion
            funion_finsert_left funion_finsert_right)
    next
      case False
      then obtain c'' where 3: "finsert v2 (finsert v1 xs) \<turnstile> c'' : {|v'|}"
        using 2 VUnion.IH(2) by blast 
      then show ?thesis apply (rule_tac x="c''" in exI)
        by (metis finsert_commute finsert_is_funion funion_finsert_left)
    qed
  qed
  then obtain c' where "{|v1,v2|}|\<union>|xs \<turnstile> c' : {|v'|}" by blast
  then have "finsert (v1 \<squnion> v2) xs \<turnstile> CUnionL c' : {|v'|}" using VUnion(3) union_L by blast
  then show ?case by meson
qed
    
lemma ax: "\<exists>c. {|v|} \<turnstile> c : {|v|}"
proof (induction v)
  case (VNat x)
  then show ?case by force
next
  case (VArrow v1 v2)
  let ?xs = "{|v1 \<mapsto> v2|}"
  have 1:"all_funs ?xs" by simp
  obtain c1 where 2: "{|v1|} \<turnstile> c1 : dom|`|?xs" using VArrow.IH(1) by auto
  obtain c2 where 3: "cod|`|?xs \<turnstile> c2 : {|v2|}" using VArrow.IH(2) by auto
  have "{|v1 \<mapsto> v2|} \<turnstile> CArrow c1 c2 : {|v1 \<mapsto> v2|}" using 1 2 3 by blast
  then show ?case by blast
next
  case (VUnion v1 v2)
  have 1: "\<exists> c1. {|v1 \<squnion> v2|} \<turnstile> c1 : {|v1|}"
  proof -
    obtain c1 where "{|v1|} \<turnstile> c1 : {|v1|}" using VUnion.IH(1) by blast
    then obtain c1' where "finsert v2 {|v1|} \<turnstile> c1' : {|v1|}"
      apply (case_tac "v2 |\<in>| {|v1|}") apply force using wk_gen by blast
    then have "{|v1 \<squnion> v2|} \<turnstile> CUnionL c1' : {|v1|}" using union_L by (simp add: finsert_commute)
    then show ?thesis by meson
  qed
  have 2: "\<exists> c2. {|v1 \<squnion> v2|} \<turnstile> c2 : {|v2|}"
  proof -
    obtain c2 where "{|v2|} \<turnstile> c2 : {|v2|}" using VUnion.IH(2) by blast
    then obtain c2' where "finsert v1 {|v2|} \<turnstile> c2' : {|v2|}"
      apply (case_tac "v1 |\<in>| {|v2|}") apply force using wk_gen by blast
    then have "{|v1 \<squnion> v2|} \<turnstile> CUnionL c2' : {|v2|}" using union_L by (simp add: finsert_commute)
    then show ?thesis by meson
  qed
  show ?case using 1 2 by blast
qed

lemma all_funs_are_funs: "\<lbrakk> all_funs xs; v |\<in>| xs \<rbrakk> \<Longrightarrow> \<exists>v1 v2. v = v1\<mapsto>v2"
  apply (induction xs) apply auto apply (case_tac v) apply auto done
  
lemma union_Le: "\<lbrakk> xs \<turnstile> c : ys; ys = {|vr|}; v1\<squnion>v2 |\<in>| xs; v1 |\<notin>| xs; v2 |\<notin>| xs \<rbrakk> \<Longrightarrow>
         \<exists>c'. {|v1,v2|} |\<union>| (xs |-| {|v1\<squnion>v2|})\<turnstile> c' : {|vr|}"
proof (induction xs c ys arbitrary: vr v1 v2 rule: deduce_le.induct)
  case (empty_R xs)
  then have "False" by auto
  then show ?case ..
next
  case (cons_R v ys xs c1 c2)
  then have "False" by auto
  then show ?case ..
next
  case (wk_nat n xs c v)
  let ?v = "VNat n"
  have v12_xs: "v1 \<squnion> v2 |\<in>| xs" using wk_nat by blast
  have v1_xs: "v1 |\<notin>| xs" using wk_nat by blast
  have v2_xs: "v2 |\<notin>| xs" using wk_nat by blast
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  obtain c' where cp: "?xs \<turnstile> c' : {|vr|}"
    using v12_xs v1_xs v2_xs wk_nat by blast
  have "\<exists> c'. finsert ?v ?xs \<turnstile> c' : {|vr|}"
  proof (cases "?v |\<in>| ?xs")
    case True
    then have "finsert (VNat n) ?xs = ?xs" by auto
    then show ?thesis using cp by auto
  next
    case False
    then show ?thesis using cp by blast
  qed
  then obtain c' where 1: "finsert ?v ?xs \<turnstile> c' : {|vr|}" by blast
  have "finsert ?v ({|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})) =
    {|v1, v2|} |\<union>| (finsert ?v xs |-| {|v1 \<squnion> v2|})" by auto
  then have "{|v1, v2|} |\<union>| (finsert ?v xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|vr|}" using 1 by simp
  then show ?case by blast
next
  case (wk_fun va vb xs c v)
  let ?v = "va \<mapsto> vb"
  have v12_xs: "v1 \<squnion> v2 |\<in>| xs" using wk_fun by blast
  have v1_xs: "v1 |\<notin>| xs" using wk_fun by blast
  have v2_xs: "v2 |\<notin>| xs" using wk_fun by blast
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  obtain c' where cp: "?xs \<turnstile> c' : {|vr|}"
    using v12_xs v1_xs v2_xs wk_fun by blast
  have "\<exists> c'. finsert ?v ?xs \<turnstile> c' : {|vr|}"
  proof (cases "?v |\<in>| ?xs")
    case True
    then have "finsert ?v ?xs = ?xs" by auto
    then show ?thesis using cp by auto
  next
    case False
    then show ?thesis using cp by blast
  qed
  then obtain c' where 1: "finsert ?v ?xs \<turnstile> c' : {|vr|}" by blast
  have "finsert ?v ({|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})) =
    {|v1, v2|} |\<union>| (finsert ?v xs |-| {|v1 \<squnion> v2|})" by auto
  then have "{|v1, v2|} |\<union>| (finsert ?v xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|vr|}" using 1 by simp
  then show ?case by blast
next
  case (union_R xs c1 va c2 vb)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})" 
  obtain c1 where a: "?xs \<turnstile> c1 : {|va|}" using union_R.IH(1)[of va v1 v2] union_R.prems by blast
  obtain c2 where b: "?xs \<turnstile> c2 : {|vb|}" using union_R.IH(2)[of vb v1 v2] union_R.prems by blast
  have "?xs \<turnstile> CUnionR c1 c2 : {|va \<squnion> vb|}" using a b by blast
  then show ?case using union_R by blast
next
  case (union_L va vb xs c v)
  let ?xs = "{|v1, v2|} |\<union>| (xs |-| {|v1 \<squnion> v2|})"
  
  have "\<exists>c'. {|v1, v2|} |\<union>| (finsert (va \<squnion> vb) xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|vr|}"
  proof (cases "va \<squnion> vb = v1 \<squnion> v2")
    case True
    then show ?thesis sorry
  next
    case False
    have 3: "va\<squnion>vb |\<notin>| ?xs" using union_L(1) False union_L.prems(3) union_L.prems(4) by blast
    have 1: "finsert (va \<squnion> vb) ?xs
          = {|v1, v2|} |\<union>| (finsert (va \<squnion> vb) xs |-| {|v1 \<squnion> v2|})" using False by auto
    have 4: "v1 \<squnion> v2 |\<in>| {|va, vb|} |\<union>| xs" using union_L.prems False by auto
    have 5: "v1 |\<notin>| {|va, vb|} |\<union>| xs" sorry
    have 6: "v2 |\<notin>| {|va, vb|} |\<union>| xs" sorry
    from union_L.IH[of v v1 v2] 4 5 6 obtain c' where 
      7: "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|}) \<turnstile> c' : {|v|}" by blast
    have 8: "finsert va (finsert vb xs) |-| {|v1 \<squnion> v2|} = finsert va (finsert vb (xs |-| {|v1 \<squnion> v2|}))" sorry
    have "{|v1, v2|} |\<union>| ({|va, vb|} |\<union>| xs |-| {|v1 \<squnion> v2|}) = {|va,vb|}|\<union>| ?xs" 
      using 3 False union_L(1) False union_L.prems 8 by (simp add: finsert_commute)
    with 7 union_L(4) have "{|va,vb|}|\<union>| ?xs \<turnstile> c' : {|vr|}" by simp
    then have 2: "finsert (va \<squnion> vb) ?xs \<turnstile> CUnionL c' : {|vr|}"
       using 3 ValuesLaurentFSet.union_L by blast
    show ?thesis using 1 2 by (rule_tac x="CUnionL c'" in exI) simp
  qed
  then show ?case by blast
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