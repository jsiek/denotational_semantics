{-

  The lemmas about the reduction of heterogeneous vectors
  (Mu/Framework/ReductionAll.agda), as proof/Framework/ReductionVec.agda
  for vectors: each element with a property (Each); and how the
  target's operands answer the source's, the first and then the rest,
  related pointwise (ans-∷). And a reduction on terms of every type, as
  one on pairs of a type and a term (redΣ), which is equivalent (pairs):
  for a target machine whose states do not say the type of the term they
  decode to.

-}

module Mu.proof.Framework.ReductionAll (Obs : Set) (o-error : Obs) where

open import proof.Framework.Reduction Obs o-error hiding (Each)
open import Mu.Framework.ReductionAll Obs o-error public
open import Mu.Framework.AllUtil using (All; []; _∷_; All₂; lookup)
open import Framework.Membership using (_∋_; Z; S)

open import Framework.Smallstep Obs using (Equivalent)

open import Data.List using (List; _∷_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

private
  variable
    X : Set
    P : X → Set

{- each element with the property Q -}
infixr 5 _∷_
data Each {X : Set} {P : X → Set} (Q : ∀ {A} → P A → Set) : ∀ {Δ} → All P Δ → Set where
  [] : Each Q []
  _∷_ : ∀ {A Δ p ps} → Q {A} p → Each Q {Δ} ps → Each Q (p ∷ ps)

each-lookup : ∀ {Q : ∀ {A} → P A → Set} {Δ A} {ps : All P Δ} → Each Q ps → (x : Δ ∋ A) → Q (lookup ps x)
each-lookup (q ∷ qs) Z = q
each-lookup (q ∷ qs) (S x) = each-lookup qs x

module _ {X : Set} {P₁ P₂ : X → Set} {red : ∀ {A} → P₂ A → Red (P₂ A)} {Val : ∀ {A} → P₂ A → Set}
  {R : ∀ {A} → P₁ A → P₂ A → Set}
  (reds : ∀ {Δ} → All P₂ Δ → Red (All P₂ Δ))
  (reds-∷ : ∀ {A Δ} (M : P₂ A) (Ms : All P₂ Δ) → reds (M ∷ Ms) ≡ red-∷ M Ms (red M) (reds Ms))
  (val-red : ∀ {A} {V : P₂ A} → Val V → red V ≡ val) where

  ans-∷ : ∀ {A Δ M M' r r'} {Ms : All P₁ Δ} {Ms' : All P₂ Δ} → All₂ R Ms Ms'
    → Ans red Val (R {A}) M r M' → Ans reds (Each Val) (All₂ R) Ms r' Ms'
    → Ans reds (Each Val) (All₂ R) (M ∷ Ms) (red-∷ M Ms r r') (M' ∷ Ms')
  ans-∷ rs a as = ans-in (frame _ (λ X → reds-∷ X _)) (_∷ rs) a
    λ v m → ans-in (frame {g = λ Xs → _ ∷ Xs} _ (λ Xs → trans (reds-∷ _ Xs) (val-in (val-red v)))) (m ∷_) as
      λ vs ms → val ε (v ∷ vs) (m ∷ ms)

{- a reduction on terms of every type, on pairs of a type and a term -}
module _ {Ty : Set} {T : Ty → Set} (obs : ∀ {B} → T B → Obs) (red : ∀ {B} → T B → Red (T B)) where

  obsΣ : Σ Ty T → Obs
  obsΣ (B , M) = obs M

  redΣ : Σ Ty T → Red (Σ Ty T)
  redΣ (B , M) = step-in (B ,_) (red M) val

  pairs : ∀ {B} (M : T B) → Equivalent (reduction obs red M) (reduction obsΣ redΣ (B , M))
  pairs {B} M = red-equivalent {Val = λ P → redΣ P ≡ val} (λ v → v) R sim (λ { refl _ _ → refl }) refl
    where
    R : T B → Σ Ty T → Set
    R M P = P ≡ (B , M)
    sim : ∀ {M P} → R M P → Ans redΣ (λ P → redΣ P ≡ val) R M (red M) P
    sim {M} refl with red M in e
    ... | val = val ε (cong (λ r → step-in (B ,_) r val) e) refl
    ... | error = error ε (cong (λ r → step-in (B ,_) r val) e)
    ... | to N = to (one (cong (λ r → step-in (B ,_) r val) e)) refl
