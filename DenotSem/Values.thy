theory Values
  imports Main IntersectionTypes Consistency
begin

section "Values"


(*datatype val = VNat nat | VFun func and
  func = VArrow val val (infix "\<mapsto>" 60) | VUnion func func (infix "\<squnion>" 59)

fun v2t :: "val \<Rightarrow> ty" and f2t :: "func \<Rightarrow> ty" where
  "v2t (VNat n) = TNat n" |
  "v2t (VFun f) = f2t f" |
  "f2t (VArrow v1 v2) = (v2t v1) \<rightarrow> (v2t v2)" |
  "f2t (VUnion f1 f2) = (f2t f1) \<sqinter> (f2t f2)" 

abbreviation fun_app :: "func \<Rightarrow> val \<Rightarrow> val set" (infix "\<bullet>" 80) where
  "f \<bullet> v \<equiv> {v'. f2t f <: v2t v \<rightarrow> v2t v' }"
  
abbreviation is_fun :: "func \<Rightarrow> bool" where
  "is_fun f \<equiv> wf_ty (f2t f)"  

abbreviation val_consis :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "~" 55) where
  "v1 ~ v2 \<equiv> v2t v1 ~ v2t v2"
*)
(*  
fun join :: "val \<Rightarrow> val \<Rightarrow> val" (infix "\<squnion>" 59) where
  "join (VNat n1) (VNat n2) = (if n1 = n2 then VNat n1 else undefined)" |
  "join (VFun f1) (VFun f2) = VFun (f1 \<squnion> f2)"
*)

end