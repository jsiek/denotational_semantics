{-

  Relations between the values of two interpreters of ISWIMμ
  (Mu/Semantics/Interp/Values.agda, with codes C₁ and C₂), for the
  proofs of the passes, as proof/Semantics/Interp/Typed/Rel.agda: values
  are related (_≈_) when they have the same shape, codes are related by
  Code, and a closure of code c and environment vs is related to one of
  code c' and environment ws when vs is related pointwise to some vs'
  and Clo relates c, vs', c' and ws (Same Code: c and c' are related by
  Code and ws is vs'; optimize also drops some of vs'). Related values
  are observed alike, and the operations on them give related results.

-}

open import Mu.Language.Type using (Ctx; Type)

module Mu.proof.Semantics.Interp.Rel {C₁ C₂ : Ctx → Type → Type → Set} where

open import Framework.Primitives using (base-rep)
open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import Mu.Framework.AllUtil using (All; []; _∷_; All₂; lookup₂)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.Interp.Clock using (Result; RelResult)
import Mu.Semantics.Interp.Values as V
private
  module S = V C₁
  module T = V C₂

open import Data.Bool using (true; false)
open import Data.Integer using (_≟_)
import Data.List as List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (does)

{- a closure relation that relates the codes and keeps the environment -}
data Same (Code : ∀ {Δ A B} → C₁ Δ A B → C₂ Δ A B → Set)
  : ∀ {Δ Δ' A B} → C₁ Δ A B → All T.Val Δ → C₂ Δ' A B → All T.Val Δ' → Set where
  same : ∀ {Δ A B} {c : C₁ Δ A B} {c' vs} → Code c c' → Same Code c vs c' vs

module Rel (Code : ∀ {Δ A B} → C₁ Δ A B → C₂ Δ A B → Set)
           (Clo : ∀ {Δ Δ' A B} → C₁ Δ A B → All T.Val Δ → C₂ Δ' A B → All T.Val Δ' → Set) where

  infix 4 _≈_
  data _≈_ : ∀ {A} → S.Val A → T.Val A → Set where
    code≈ : ∀ {Δ A B} {c : C₁ Δ A B} {c'} → Code c c' → S.code c ≈ T.code c'
    pack≈ : ∀ {Δ Δ' A B} {c : C₁ Δ A B} {c' : C₂ Δ' A B} {vs vs' ws} → All₂ _≈_ vs vs' → Clo c vs' c' ws
      → S.pack (S.code c) (S.tup vs) ≈ T.pack (T.code c') (T.tup ws)
    const≈ : ∀ {B} {k : base-rep B} → S.const k ≈ T.const k
    tup≈ : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → S.tup vs ≈ T.tup ws
    inl≈ : ∀ {A B v w} → v ≈ w → S.inl {A} {B} v ≈ T.inl w
    inr≈ : ∀ {A B v w} → v ≈ w → S.inr {A} {B} v ≈ T.inr w
    fold≈ : ∀ {A c v w} → v ≈ w → S.fold {A} {c} v ≈ T.fold w

  obs≈ : ∀ {A} {v : S.Val A} {w} → v ≈ w → S.obs v ≡ T.obs w
  obs≈* : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → S.obs-all vs ≡ T.obs-all ws
  obs≈ (code≈ _) = refl
  obs≈ (pack≈ _ _) = refl
  obs≈ const≈ = refl
  obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
  obs≈ (inl≈ r) = cong o-inl (obs≈ r)
  obs≈ (inr≈ r) = cong o-inr (obs≈ r)
  obs≈ (fold≈ r) = obs≈ r
  obs≈* [] = refl
  obs≈* (r ∷ rs) = cong₂ List._∷_ (obs≈ r) (obs≈* rs)

  δ≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → S.δ p v₁ v₂ ≈ T.δ p w₁ w₂
  δ≈ sub const≈ const≈ = const≈
  δ≈ eq (const≈ {k = n}) (const≈ {k = m}) with does (n ≟ m)
  ... | true = inl≈ (tup≈ [])
  ... | false = inr≈ (tup≈ [])

  nth≈ : ∀ {Δ A} (i : Δ ∋ A) {v w} → v ≈ w → S.nth i v ≈ T.nth i w
  nth≈ i (tup≈ rs) = lookup₂ rs i

  unfold≈ : ∀ {A c} {v : S.Val (μ A {c})} {w} → v ≈ w → S.unfold-v v ≈ T.unfold-v w
  unfold≈ (fold≈ r) = r

  either≈ : ∀ {A B} {X Y : Set} {R : X → Y → Set} {u : S.Val (A ⊹ B)} {u'} {f₁ f₂ g₁ g₂}
    → u ≈ u' → (∀ {v w} → v ≈ w → RelResult R (f₁ v) (g₁ w)) → (∀ {v w} → v ≈ w → RelResult R (f₂ v) (g₂ w))
    → RelResult R (S.either {X = Result X} u f₁ f₂) (T.either {X = Result Y} u' g₁ g₂)
  either≈ (inl≈ r) h₁ h₂ = h₁ r
  either≈ (inr≈ r) h₁ h₂ = h₂ r
