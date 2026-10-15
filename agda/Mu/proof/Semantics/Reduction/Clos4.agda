{-

  The values of the Clos4μ reduction semantics
  (Mu/Semantics/Reduction/Clos4.agda), which reduce to val.

-}

module Mu.proof.Semantics.Reduction.Clos4 where

open import Mu.Semantics.Reduction.Clos4 public
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos4
open import Mu.Framework.AllUtil using (All; []; _∷_)
open import Semantics.Observation using (Obs; o-error)
open import Mu.Framework.ReductionAll Obs o-error using (Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (val)

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Value {Γ} : ∀ {A} → Tm Γ A → Set where
  code : ∀ {Δ A B} {N : Tm (A ∷ tup Δ ∷ []) B} → Value (code {Γ} N)
  pack : ∀ {Δ A B} {L : Tm Γ (code Δ A B)} {M} → Value L → Value M → Value (pack L M)
  lit : ∀ {B c} → Value (lit B c)
  tuple : ∀ {Δ} {Vs : All (Tm Γ) Δ} → Each Value Vs → Value (tuple Vs)
  inl : ∀ {A B} {V : Tm Γ A} → Value V → Value (inl {B = B} V)
  inr : ∀ {A B} {V : Tm Γ B} → Value V → Value (inr {A = A} V)
  fold : ∀ {A c} {V : Tm Γ (unroll A {c})} → Value V → Value (fold {A = A} {c} V)

value-red : ∀ {A} {V : Tm [] A} → Value V → red V ≡ val
values-red : ∀ {Δ} {Vs : All (Tm []) Δ} → Each Value Vs → reds Vs ≡ val
value-red code = refl
value-red (pack v w) rewrite value-red v | value-red w = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
value-red (fold v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl
