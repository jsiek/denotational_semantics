{-

  Clos3ᵀ: Clos3, intrinsically typed. The output of typed concretize
  (Compiler/Typed/Concretize.agda).

  A closure clos N (M₀ ∷ … ∷ Mₙ₋₁) has closed code N with two
  variables: the argument (variable 0, of type Any) and the tuple of its
  n free variables (variable 1, of type ⟪ tup n ⟫), from which the code
  reads a free variable with get. The closure itself has type ⟪ fun ⟫:
  the length of its environment is hidden in its value. Contexts are
  lists of types (Language/Typed/Type.agda).

-}

module Language.Typed.Clos3 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Language.Typed.Type

open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_)
open import Data.Vec using (Vec)

data Tm (Γ : Ctx) : Ty → Set where
  `_ : ∀ {A} → Γ ∋ A → Tm Γ A
  clos : ∀ {n} → Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → Vec (Tm Γ Any) n → Tm Γ ⟪ fun ⟫
  app : Tm Γ ⟪ fun ⟫ → Tm Γ Any → Tm Γ Any
  lit : (B : Base) → base-rep B → Tm Γ ⟪ base B ⟫
  tuple : ∀ {n} → Vec (Tm Γ Any) n → Tm Γ ⟪ tup n ⟫
  get : ∀ {n} → Fin n → Tm Γ ⟪ tup n ⟫ → Tm Γ Any
  inl inr : Tm Γ Any → Tm Γ ⟪ sum ⟫
  case : Tm Γ ⟪ sum ⟫ → Tm (Any ∷ Γ) Any → Tm (Any ∷ Γ) Any → Tm Γ Any
  prim : (p : Prim) → Tm Γ ⟪ base Int ⟫ → Tm Γ ⟪ base Int ⟫ → Tm Γ ⟪ out-flat p ⟫
  let′ : Tm Γ Any → Tm (Any ∷ Γ) Any → Tm Γ Any
  inject : (G : Flat) → Tm Γ ⟪ G ⟫ → Tm Γ Any
  project : (t : Tag) → Tm Γ Any → Tm Γ ⟪ flat t ⟫
