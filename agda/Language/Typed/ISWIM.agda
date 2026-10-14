{-

  ISWIMᵀ: ISWIM with explicit casts, intrinsically typed. The output of
  cast insertion (Compiler/Typed/Cast.agda).

  Tm k A is a term of type A in a context of k variables, each of type
  Any (functions, let and case bind values of type Any). The operations
  take operands of the flat type they need, so a misuse, such as applying
  a tuple, cannot be written; project G is the only operation that can
  fail, and inject G the only way into Any. Every term is well scoped.

-}

module Language.Typed.ISWIM where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Language.Typed.Type

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec)

data Tm (k : ℕ) : Ty → Set where
  `_ : Fin k → Tm k Any
  lam : Tm (suc k) Any → Tm k ⟪ fun ⟫
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
