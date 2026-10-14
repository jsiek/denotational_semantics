{-

  Clos2ᵀ: Clos2, intrinsically typed. The output of typed enclose
  (Compiler/Typed/Enclose.agda).

  A closure clos N (M₀ ∷ … ∷ Mₙ₋₁) has closed code N in a context of
  n + 1 variables: variable 0 is the argument and variable suc i the
  value of Mᵢ, its i-th free variable. Otherwise as ISWIMᵀ
  (Language/Typed/ISWIM.agda).

-}

module Language.Typed.Clos2 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Language.Typed.Type

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec)

data Tm (k : ℕ) : Ty → Set where
  `_ : Fin k → Tm k Any
  clos : ∀ {n} → Tm (suc n) Any → Vec (Tm k Any) n → Tm k ⟪ fun ⟫
  app : Tm k ⟪ fun ⟫ → Tm k Any → Tm k Any
  lit : (B : Base) → base-rep B → Tm k ⟪ base B ⟫
  tuple : ∀ {n} → Vec (Tm k Any) n → Tm k ⟪ tup n ⟫
  get : ∀ {n} → Fin n → Tm k ⟪ tup n ⟫ → Tm k Any
  inl inr : Tm k Any → Tm k ⟪ sum ⟫
  case : Tm k ⟪ sum ⟫ → Tm (suc k) Any → Tm (suc k) Any → Tm k Any
  prim : (p : Prim) → Tm k ⟪ base Int ⟫ → Tm k ⟪ base Int ⟫ → Tm k ⟪ out-flat p ⟫
  let′ : Tm k Any → Tm (suc k) Any → Tm k Any
  inject : (G : Flat) → Tm k ⟪ G ⟫ → Tm k Any
  project : (t : Tag) → Tm k Any → Tm k ⟪ flat t ⟫
