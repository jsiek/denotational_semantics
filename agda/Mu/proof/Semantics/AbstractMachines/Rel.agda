{-

  The relation between the values of two CEK machines
  (Mu/Semantics/AbstractMachines/Values.agda, with codes C₁ and C₂) for a pass that
  maps the code of each closure by f (enclose, concretize, delay), as
  proof/Semantics/ClockedInterpreters/Rel.agda for the interpreters: values are
  related (_≈_) when they have the same shape, except that a closure of
  code c is related to one of code f c, with related environments.
  Related values are observed alike, and primitives give related values.

-}

open import Mu.Language.Type using (Ctx; Type)

module Mu.proof.Semantics.AbstractMachines.Rel {C₁ C₂ : Ctx → Type → Type → Set} (f : ∀ {Δ A B} → C₁ Δ A B → C₂ Δ A B) where

open import Framework.Primitives using (base-rep)
open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import Mu.Framework.AllUtil using (All; []; _∷_; All₂)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
import Mu.Semantics.AbstractMachines.Values as V
private
  module S = V C₁
  module T = V C₂

open import Data.Bool using (true; false)
open import Data.Integer using (_≟_)
import Data.List as List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (does)

infix 4 _≈_
data _≈_ : ∀ {A} → S.Val A → T.Val A → Set where
  clos≈ : ∀ {Δ A B} {c : C₁ Δ A B} {vs ws} → All₂ _≈_ vs ws → S.pack (S.code c) (S.tup vs) ≈ T.pack (T.code (f c)) (T.tup ws)
  const≈ : ∀ {B} {c : base-rep B} → S.const c ≈ T.const c
  tup≈ : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → S.tup vs ≈ T.tup ws
  inl≈ : ∀ {A B v w} → v ≈ w → S.inl {A} {B} v ≈ T.inl w
  inr≈ : ∀ {A B v w} → v ≈ w → S.inr {A} {B} v ≈ T.inr w
  fold≈ : ∀ {A v w} → v ≈ w → S.fold {A} v ≈ T.fold w

obs≈ : ∀ {A} {v : S.Val A} {w} → v ≈ w → S.obs v ≡ T.obs w
obs≈* : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → S.obs-all vs ≡ T.obs-all ws
obs≈ (clos≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (fold≈ r) = obs≈ r
obs≈* [] = refl
obs≈* (r ∷ rs) = cong₂ List._∷_ (obs≈ r) (obs≈* rs)

δ≈ : ∀ p n m → S.δᵀ p n m ≈ T.δᵀ p n m
δ≈ sub n m = const≈
δ≈ eq n m with does (n ≟ m)
... | true = inl≈ (tup≈ [])
... | false = inr≈ (tup≈ [])
