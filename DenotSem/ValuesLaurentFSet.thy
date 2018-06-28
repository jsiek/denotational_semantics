theory ValuesLaurentFSet
  imports Main "~~/src/HOL/Library/FSet" 
begin

datatype val = VNat nat | VArrow val val (infix "\<mapsto>" 60) | VUnion val val (infix "\<squnion>" 59)
  
abbreviation is_fun :: "val \<Rightarrow> bool" where
  "is_fun v \<equiv> (case v of v1\<mapsto>v2 \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation all_funs :: "val fset \<Rightarrow> bool" where
  "all_funs xs \<equiv> ffold (\<lambda>v b. is_fun v \<and> b) True xs"

fun dom :: "val \<Rightarrow> val" where
  "dom (v\<mapsto>v') = v" 
  
fun cod :: "val \<Rightarrow> val" where
  "cod (v\<mapsto>v') = v'"

datatype coercion = CWkNat coercion | CWkFun coercion 
  | CNat nat | CArrow coercion coercion
  | CUnionR coercion | CUnionL coercion | CNil | CCons coercion coercion

inductive deduce_le :: "val fset \<Rightarrow> coercion \<Rightarrow> val fset \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 56) where
  empty_R[intro!]: "xs \<turnstile> CNil : {||}" |
  cons_R[intro!]: "\<lbrakk> v |\<in>| vs; vs |-| {|v|} \<noteq> {||}; xs \<turnstile> c1 : {|v|}; xs \<turnstile> c2 : vs |-| {|v|} \<rbrakk> 
    \<Longrightarrow> xs \<turnstile> CCons c1 c2 : vs" |
  wk_nat[intro!]: "\<lbrakk> VNat n |\<in>| xs; xs |-| {|VNat n|} \<turnstile> c : {|v|} \<rbrakk> \<Longrightarrow> xs \<turnstile> CWkNat c : {||}" | 
  wk_fun[intro!]: "\<lbrakk> v1\<mapsto>v1' |\<in>| xs; xs |-| {|v1\<mapsto>v1'|} \<turnstile> c : {|v|} \<rbrakk> \<Longrightarrow> xs \<turnstile> CWkFun c : {|v|}" |
    union_R[intro!]: "\<lbrakk> xs \<turnstile> c : {|v1,v2|} |\<union>| (ys |-| {|v1\<squnion>v2|}) \<rbrakk> \<Longrightarrow> xs \<turnstile> CUnionR c : {|v1\<squnion>v2|}" |
    union_L[intro]: "\<lbrakk> {|v1,v2|} |\<union>| (xs |-| {|v1\<squnion>v2|}) \<turnstile> c : ys \<rbrakk> \<Longrightarrow> xs \<turnstile> CUnionL c : {|v1\<squnion>v2|}" | 
  le_nat[intro!]: "{|VNat n|} \<turnstile> CNat n : {|VNat n|}" |
  le_arrow[intro!]: "\<lbrakk> all_funs xs; {|v1|} \<turnstile> c1 : dom|`|xs; cod|`|xs \<turnstile> c2 : {|v1'|} \<rbrakk>
    \<Longrightarrow> xs \<turnstile> CArrow c1 c2 : {|v1 \<mapsto> v1'|}"

inductive_cases
   cwknat_inv[elim!]: "xs \<turnstile> CWkNat c : ys" and
   cwkfun_inv[elim!]: "xs \<turnstile> CWkFun c : ys" and
   cunionr_inv[elim!]: "xs \<turnstile> CUnionR c : ys" and
   cunionl_inv[elim!]: "xs \<turnstile> CUnionL c : ys" and
   cnat_inv[elim!]: "xs \<turnstile> CNat n : ys" and
   carrow_inv[elim!]: "xs \<turnstile> CArrow c1 c2 : ys" and
   cnil_inv[elim!]: "xs \<turnstile> CNil : ys" and
   ccons_inv[elim!]: "xs \<turnstile> CCons c1 c2 : ys"
  
  
    
end