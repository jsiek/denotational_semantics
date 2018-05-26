theory Subst
  imports Lambda
begin
  
fun shift :: "nat \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> exp" ("\<up>") where
  "shift k c (ENat n) = ENat n" |
  "shift k c (EPrim f e1 e2) = EPrim f (shift k c e1) (shift k c e2)" |
  "shift k c (EVar n) = (if c \<le> n then EVar (n + k) else EVar n)" |
  "shift k c (ELam e) = ELam  (shift k (Suc c) e)" |
  "shift k c (EApp e1 e2) = EApp (shift k c e1) (shift k c e2)" |
  "shift k c (EIf e1 e2 e3) = EIf (shift k c e1) (shift k c e2) (shift k c e3)"

fun subst :: "nat \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" ("[_\<mapsto>_]_" [79,79] 78) where
  "subst k v (ENat n) = ENat n" |
  "subst k v (EPrim f e1 e2) = EPrim f (subst k v e1) (subst k v e2)" |
  "subst k v (EVar n) = (if k = n then v else if k < n then EVar (n-1) else EVar n)" |
  "subst k v (ELam e) = ELam  (subst (Suc k) (shift (Suc 0) 0 v) e)" |
  "subst k v (EApp e1 e2) = EApp (subst k v e1) (subst k v e2)" |
  "subst k v (EIf e1 e2 e3) = EIf (subst k v e1) (subst k v e2) (subst k v e3)"

end