{-

  The values of the Clos3ᵀ reduction semantics
  (Semantics/Reduction/Typed/Clos3.agda), which reduce to val and which
  renaming and substitution keep.

-}

module proof.Semantics.Reduction.Typed.Clos3 where

open import Semantics.Reduction.Typed.Clos3 public
open import Language.Typed.Type
open import Language.Typed.Clos3
open import Semantics.Observation using (Obs; o-error)
open import proof.Framework.Reduction Obs o-error using (val)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([])
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Value {Γ} : ∀ {A} → Tm Γ A → Set where
  clos : ∀ {n} {N} {Vs : Vec (Tm Γ Any) n} → All Value Vs → Value (clos N Vs)
  lit : ∀ {B c} → Value (lit B c)
  tuple : ∀ {n} {Vs : Vec (Tm Γ Any) n} → All Value Vs → Value (tuple Vs)
  inl : ∀ {V} → Value V → Value (inl V)
  inr : ∀ {V} → Value V → Value (inr V)
  inject : ∀ {G V} → Value V → Value (inject G V)

value-red : ∀ {A} {V : Tm [] A} → Value V → red V ≡ val
values-red : ∀ {n} {Vs : Vec (Tm [] Any) n} → All Value Vs → reds Vs ≡ val
value-red (clos vs) rewrite values-red vs = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
value-red (inject v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

value-trav : ∀ {𝒦 Γ Δ A} {σ : Sub 𝒦 Γ Δ} {V : Tm Γ A} → Value V → Value (trav 𝒦 σ V)
values-trav : ∀ {𝒦 Γ Δ n} {σ : Sub 𝒦 Γ Δ} {Vs : Vec (Tm Γ Any) n} → All Value Vs → All Value (travs 𝒦 σ Vs)
value-trav (clos vs) = clos (values-trav vs)
value-trav lit = lit
value-trav (tuple vs) = tuple (values-trav vs)
value-trav (inl v) = inl (value-trav v)
value-trav (inr v) = inr (value-trav v)
value-trav (inject v) = inject (value-trav v)
values-trav [] = []
values-trav (v ∷ vs) = value-trav v ∷ values-trav vs

lookup-travs : ∀ {𝒦 Γ Δ n} (σ : Sub 𝒦 Γ Δ) (Ms : Vec (Tm Γ Any) n) i → lookup (travs 𝒦 σ Ms) i ≡ trav 𝒦 σ (lookup Ms i)
lookup-travs σ (M ∷ Ms) zero = refl
lookup-travs σ (M ∷ Ms) (suc i) = lookup-travs σ Ms i
