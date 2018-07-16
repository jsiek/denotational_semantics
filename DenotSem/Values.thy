theory Values
  imports Main IntersectionTypes
begin

section "Values"

datatype val = VNat nat | VFun func and
  func = VArrow val val (infix "\<mapsto>" 60) | VUnion func func (infix "\<squnion>" 59)

fun v2t :: "val \<Rightarrow> ty" and f2t :: "func \<Rightarrow> ty" where
  "v2t (VNat n) = TNat n" |
  "v2t (VFun f) = f2t f" |
  "f2t (VArrow v1 v2) = (v2t v1) \<rightarrow> (v2t v2)" |
  "f2t (VUnion f1 f2) = (f2t f1) \<sqinter> (f2t f2)" 
  
fun le_val :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "(VNat n1) \<sqsubseteq> (VNat n2) = (n1 = n2)" |
  "(VNat n1) \<sqsubseteq> (VFun f2) = False" |
  "(VFun f1) \<sqsubseteq> (VNat n2) = False" |
  "(VFun f1) \<sqsubseteq> (VFun f2) = f2t f2 <: f2t f1"

  
  
end