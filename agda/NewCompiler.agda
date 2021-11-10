

open import AbstractBindingTree

module NewCompiler where
  open import NewISWIM renaming (AST to AST0; cons to cons0; nil to nil0; ast to ast0)
  open import NewClos1 renaming (AST to AST1; cons to cons1; nil to nil1; ast to ast1)
  open import NewClos2 renaming (AST to AST2; cons to cons2; nil to nil2; ast to ast2)
  open import NewClos3 renaming (AST to AST3; cons to cons3; nil to nil3; ast to ast3)
  open import NewClos4 renaming (AST to AST4; cons to cons4; nil to nil4; ast to ast4)


  annotate : (M : AST0) → AST1
  annotate (` x) = {! ` x  !}
  annotate (lam ABT.⦅ cons (bind (ast N)) nil ⦆) = {!   !}
  annotate (app ABT.⦅ cons (ast M) (cons (ast N) nil) ⦆) = 
    app ABT.⦅ cons1 (ast1 (annotate M)) (cons1 (ast1 (annotate N)) nil1) ⦆
  annotate (prim P x₁ ABT.⦅ x ⦆) = {!   !}
  annotate (pair-op ABT.⦅ x ⦆) = {!   !}
  annotate (fst-op ABT.⦅ x ⦆) = {!   !}
  annotate (snd-op ABT.⦅ x ⦆) = {!   !}
  annotate (tuple n ABT.⦅ x ⦆) = {!   !}
  annotate (get n ABT.⦅ x ⦆) = {!   !}
  annotate (inl-op ABT.⦅ x ⦆) = {!   !}
  annotate (inr-op ABT.⦅ x ⦆) = {!   !}
  annotate (case-op ABT.⦅ x ⦆) = {!   !}

  data annotated : (M : AST1) → Set where
    temp : ∀ M → annotated M

  enclose : (M : AST1) → AST2
  enclose M = {!   !}

  optimize : (M : AST2) → AST2
  optimize M = {!   !}

  concretize : (M : AST2) → AST3
  concretize M = {!   !}

  delay : (M : AST3) → AST4
  delay M = {!   !}

  



