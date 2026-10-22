{-

  The values of the Clos2μ reduction semantics
  (Mu/Semantics/Reduction/Clos2.agda), which reduce to val and which
  renaming and substitution keep.

-}

module Mu.proof.Semantics.Reduction.Clos2 where

open import Mu.Semantics.Reduction.Clos2 public
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos2
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Observation using (Obs; o-error)
open import Mu.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (val)

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Value {Γ} : ∀ {A} → Tm Γ A → Set where
  clos : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {Vs : All (Tm Γ) Δ} → Each Value Vs → Value (clos N Vs)
  lit : ∀ {B c} → Value (lit B c)
  tuple : ∀ {Δ} {Vs : All (Tm Γ) Δ} → Each Value Vs → Value (tuple Vs)
  inl : ∀ {A B} {V : Tm Γ A} → Value V → Value (inl {B = B} V)
  inr : ∀ {A B} {V : Tm Γ B} → Value V → Value (inr {A = A} V)
  fold : ∀ {A} {V : Tm Γ (unroll A)} → Value V → Value (fold {A = A} V)

value-red : ∀ {A} {V : Tm [] A} → Value V → red V ≡ val
values-red : ∀ {Δ} {Vs : All (Tm []) Δ} → Each Value Vs → reds Vs ≡ val
value-red (clos vs) rewrite values-red vs = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
value-red (fold v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

value-trav : ∀ {𝒦 Γ Δ A} {σ : Sub 𝒦 Γ Δ} {V : Tm Γ A} → Value V → Value (trav 𝒦 σ V)
values-trav : ∀ {𝒦 Γ Δ Δ'} {σ : Sub 𝒦 Γ Δ} {Vs : All (Tm Γ) Δ'} → Each Value Vs → Each Value (travs 𝒦 σ Vs)
value-trav (clos vs) = clos (values-trav vs)
value-trav lit = lit
value-trav (tuple vs) = tuple (values-trav vs)
value-trav (inl v) = inl (value-trav v)
value-trav (inr v) = inr (value-trav v)
value-trav (fold v) = fold (value-trav v)
values-trav [] = []
values-trav (v ∷ vs) = value-trav v ∷ values-trav vs

lookup-travs : ∀ {𝒦 Γ Δ Δ' A} (σ : Sub 𝒦 Γ Δ) (Ms : All (Tm Γ) Δ') (i : Δ' ∋ A) → lookup (travs 𝒦 σ Ms) i ≡ trav 𝒦 σ (lookup Ms i)
lookup-travs σ (M ∷ Ms) Z = refl
lookup-travs σ (M ∷ Ms) (S i) = lookup-travs σ Ms i

{- a variable or a value: what a closure captures, in enclose's and
   optimize's relations; renaming keeps it, and closed it is a value -}
data VV {Γ} : ∀ {A} → Tm Γ A → Set where
  var : ∀ {A} (x : Γ ∋ A) → VV (` x)
  val : ∀ {A} {V : Tm Γ A} → Value V → VV V

vv-wk : ∀ {Γ A B} {M : Tm Γ A} → VV M → VV (ren (S {b = B}) M)
vv-wk (var x) = var _
vv-wk (val v) = val (value-trav v)

vv-value : ∀ {A} {V : Tm [] A} → VV V → Value V
vv-value (val v) = v
