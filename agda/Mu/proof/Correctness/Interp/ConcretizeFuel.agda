{-

  Correctness of concretize (Clos2μ → Clos3μ), clock for clock, as for
  typed concretize (proof/Correctness/Interp/ConcretizeFuel.agda; see
  the design note in Semantics/Interp/Clock.agda). Each Clos2μ variable
  x lives in Clos3μ where φ x says (a variable, or a component of a
  tuple held in a variable), so environments are related through φ
  (Env≈); a closure of N and vs is related to one of concretize fv-ref N
  and related values (Rel, Same).

-}

module Mu.proof.Correctness.Interp.ConcretizeFuel where

open import Data.List using ([]; _∷_)
open import Mu.Language.Type
open import Mu.Language.Clos2
import Mu.Language.Clos3 as C3
open import Mu.Compiler.Concretize
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂; lookup₂)
open import proof.Semantics.Interp.Clock
import Mu.Semantics.Interp.Clos2 as S
import Mu.Semantics.Interp.Clos3 as T
open import Mu.proof.Semantics.Interp.Rel {λ Δ A B → Tm (A ∷ Δ) B} {λ Δ A B → C3.Tm (A ∷ tup Δ ∷ []) B}

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Code : ∀ {Δ A B} → Tm (A ∷ Δ) B → C3.Tm (A ∷ tup Δ ∷ []) B → Set
Code N N' = concretize fv-ref N ≡ N'

open Rel Code (Same Code)

{- the value at a reference -}
deref : ∀ {Γ A} → Ref Γ A → T.Env Γ → T.Val A
deref (var x) ρ = lookup ρ x
deref (prj i x) ρ = T.nth i (lookup ρ x)

Env≈ : ∀ {Γ Γ'} → Refs Γ Γ' → S.Env Γ → T.Env Γ' → Set
Env≈ φ ρ₁ ρ₂ = ∀ {A} (x : _ ∋ A) → lookup ρ₁ x ≈ deref (φ x) ρ₂

env-ext : ∀ {Γ Γ' B} {φ : Refs Γ Γ'} {ρ₁ ρ₂ v w} → v ≈ w → Env≈ φ ρ₁ ρ₂ → Env≈ (ext-ref {B = B} φ) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext r E Z = r
env-ext {φ = φ} r E (S x) with φ x | E x
... | var y | e = e
... | prj i y | e = e

ref≈ : ∀ ck {Γ A v} (a : Ref Γ A) {ρ} → v ≈ deref a ρ → RelResult _≈_ (ret v) (T.eval ck ρ (ref-tm a))
ref≈ ck (var x) r = ret r
ref≈ ck (prj i x) r = ret r

run≈ : ∀ ck {Γ Γ' A} (M : Tm Γ A) {φ : Refs Γ Γ'} {ρ₁ ρ₂} → Env≈ φ ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (concretize φ M))
runs≈ : ∀ ck {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) {φ : Refs Γ Γ'} {ρ₁ ρ₂} → Env≈ φ ρ₁ ρ₂
  → RelResult (All₂ _≈_) (S.evals ck ρ₁ Ms) (T.evals ck ρ₂ (concs φ Ms))
call≈ : ∀ ck {A B} {f : S.Val (A ⇒ B)} {g v w} → f ≈ g → v ≈ w → RelResult _≈_ (S.call ck f v) (T.call ck g w)

run≈ ck (` x) {φ} E = ref≈ ck (φ x) (E x)
run≈ ck (clos N Ms) E = bind-rel (runs≈ ck Ms E) λ vs → ret (pack≈ vs (same refl))
run≈ ck (app L M) E = bind-rel (run≈ ck L E) λ f → bind-rel (run≈ ck M E) λ w → call≈ ck f w
run≈ ck (lit B c) E = ret const≈
run≈ ck (tuple Ms) E = bind-rel (runs≈ ck Ms E) λ vs → ret (tup≈ vs)
run≈ ck (get i M) E = bind-rel (run≈ ck M E) λ v → ret (nth≈ i v)
run≈ ck (inl M) E = bind-rel (run≈ ck M E) λ v → ret (inl≈ v)
run≈ ck (inr M) E = bind-rel (run≈ ck M E) λ v → ret (inr≈ v)
run≈ ck (case L M N) E =
  bind-rel (run≈ ck L E) λ u → either≈ u (λ v → run≈ ck M (env-ext v E)) (λ v → run≈ ck N (env-ext v E))
run≈ ck (prim p L M) E = bind-rel (run≈ ck L E) λ v → bind-rel (run≈ ck M E) λ w → ret (δ≈ p v w)
run≈ ck (let′ M N) E = bind-rel (run≈ ck M E) λ v → run≈ ck N (env-ext v E)
run≈ ck (fold M) E = bind-rel (run≈ ck M E) λ v → ret (fold≈ v)
run≈ ck (unfold M) E = bind-rel (run≈ ck M E) λ v → ret (unfold≈ v)

runs≈ ck [] E = ret []
runs≈ ck (M ∷ Ms) E = bind-rel (run≈ ck M E) λ v → bind-rel (runs≈ ck Ms E) λ vs → ret (v ∷ vs)

call≈ zero f w = timeout
call≈ (suc ck) (pack≈ {c = N} rs (same refl)) w = run≈ ck N λ { Z → w ; (S i) → lookup₂ rs i }

concretize-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (concretize-program M))
concretize-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M λ ()
