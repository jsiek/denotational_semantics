{-

  FPC (Plotkin's Fixed Point Calculus): a call-by-value λ-calculus,
  intrinsically typed, with iso-recursive types. The
  source of the FPC compiler (agda/Mu/).

  Tm Γ A is a term of type A in the context Γ (a list of closed types,
  Mu/Language/Type.agda). The constructs are ISWIM's, typed, with
  call-by-value semantics: functions, application, constants, n-ary
  tuples and their components (get, by a typed index into the tuple's
  list of types), binary sums and case, the primitives on integers,
  and let; plus fold and unfold, the two coercions between a recursive
  type μ A and its unfolding A [ μ A ], which do nothing at run time.

  There is no recursion construct and no error: divergence and general
  recursion come through recursive types (ω = λx. unfold x x has type
  (μX. X ⇒ A) ⇒ A, and the call-by-value fixed-point combinator is
  typable the same way), and no operation can fail.

-}

module Mu.Language.FPC where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Mu.Language.Type
open import Mu.Framework.AllUtil using (All)

open import Data.List using (_∷_)

data Tm (Γ : Ctx) : Type → Set where
  `_ : ∀ {A} → Γ ∋ A → Tm Γ A
  lam : ∀ {A B} → Tm (A ∷ Γ) B → Tm Γ (A ⇒ B)
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
