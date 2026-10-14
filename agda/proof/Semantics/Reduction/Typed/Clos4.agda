{-

  The values of the Clos4ᵀ reduction semantics
  (Semantics/Reduction/Typed/Clos4.agda), which reduce to val.

-}

module proof.Semantics.Reduction.Typed.Clos4 where

open import Semantics.Reduction.Typed.Clos4 public
open import Language.Typed.Type
open import Language.Typed.Clos4
open import Semantics.Observation using (Obs; o-error)
open import proof.Framework.Reduction Obs o-error using (val)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Value {Γ} : ∀ {A} → Tm Γ A → Set where
  code : ∀ {n} {N : Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any} → Value (code {Γ} N)
  pack : ∀ {n} {L : Tm Γ (code n)} {M} → Value L → Value M → Value (pack L M)
  lit : ∀ {B c} → Value (lit B c)
  tuple : ∀ {n} {Vs : Vec (Tm Γ Any) n} → All Value Vs → Value (tuple Vs)
  inl : ∀ {V} → Value V → Value (inl V)
  inr : ∀ {V} → Value V → Value (inr V)
  inject : ∀ {G V} → Value V → Value (inject G V)

value-red : ∀ {A} {V : Tm [] A} → Value V → red V ≡ val
values-red : ∀ {n} {Vs : Vec (Tm [] Any) n} → All Value Vs → reds Vs ≡ val
value-red code = refl
value-red (pack v w) rewrite value-red v | value-red w = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
value-red (inject v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl
