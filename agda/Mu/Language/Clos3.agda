{-

  Clos3μ: Clos3, intrinsically typed, with recursive types. The output
  of concretize (Mu/Compiler/Concretize.agda).

  A closure clos N Ms, with Ms : All (Tm Γ) Δ its free variables, has
  closed code N with two variables: the argument (variable Z, of type
  A) and the tuple of its free variables (variable S Z, of type tup Δ),
  from which the code reads a free variable with get. The closure has
  type A ⇒ B: the types of its free variables are hidden in its value.

-}

module Mu.Language.Clos3 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Mu.Language.Type
open import Mu.Framework.AllUtil using (All)

open import Data.List using ([]; _∷_)

data Tm (Γ : Ctx) : Type → Set where
  `_ : ∀ {A} → Γ ∋ A → Tm Γ A
  clos : ∀ {Δ A B} → Tm (A ∷ tup Δ ∷ []) B → All (Tm Γ) Δ → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  lit : (B : Base) → base-rep B → Tm Γ (base B)
  tuple : ∀ {Δ} → All (Tm Γ) Δ → Tm Γ (tup Δ)
  get : ∀ {Δ A} → Δ ∋ A → Tm Γ (tup Δ) → Tm Γ A
  inl : ∀ {A B} → Tm Γ A → Tm Γ (A ⊹ B)
  inr : ∀ {A B} → Tm Γ B → Tm Γ (A ⊹ B)
  case : ∀ {A B C} → Tm Γ (A ⊹ B) → Tm (A ∷ Γ) C → Tm (B ∷ Γ) C → Tm Γ C
  prim : (p : Prim) → Tm Γ (base Int) → Tm Γ (base Int) → Tm Γ (out-ty p)
  let′ : ∀ {A B} → Tm Γ A → Tm (A ∷ Γ) B → Tm Γ B
  fold : ∀ {A} → Tm Γ (unroll A) → Tm Γ (μ A)
  unfold : ∀ {A} → Tm Γ (μ A) → Tm Γ (unroll A)
