{-

  Correctness of enclose (ISWIMμ → Clos2μ), clock for clock, as for
  typed enclose (proof/Correctness/Interp/EncloseFuel.agda; see the
  design note in Semantics/Interp/Clock.agda): a term and its
  enclosure, in related environments, both time out or return related
  values, for every clock (neither errs). A closure captures every
  variable of its context in order, so an ISWIMμ closure of N and ρ is
  related to the Clos2μ closure of enclose N and an environment related
  to ρ (Rel, Same).

-}

module Mu.proof.Correctness.Interp.EncloseFuel where

open import Mu.Language.Type
open import Data.List using ([]; _∷_)
open import Mu.Language.ISWIM
import Mu.Language.Clos2 as C2
open import Mu.Compiler.Enclose
open import Mu.Framework.AllUtil using (All; []; _∷_; tab; lookup; All₂; lookup₂; tab-lookup₂)
open import proof.Semantics.Interp.Clock
import Mu.Semantics.Interp.ISWIM as S
import Mu.Semantics.Interp.Clos2 as T
open import Mu.proof.Semantics.Interp.Rel {λ Δ A B → Tm (A ∷ Δ) B} {λ Δ A B → C2.Tm (A ∷ Δ) B}

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Code : ∀ {Δ A B} → Tm (A ∷ Δ) B → C2.Tm (A ∷ Δ) B → Set
Code N N' = enclose N ≡ N'

open Rel Code (Same Code)

{- the captured variables evaluate to the environment -}
evals-vars : ∀ ck {Γ Δ} (f : ∀ {C} → Δ ∋ C → Γ ∋ C) (ρ : T.Env Γ)
  → T.evals ck ρ (tab (λ x → C2.` f x)) ≡ ret (tab (λ x → lookup ρ (f x)))
evals-vars ck {Δ = []} f ρ = refl
evals-vars ck {Δ = _ ∷ Δ} f ρ rewrite evals-vars ck (λ x → f (S x)) ρ = refl

run≈ : ∀ ck {Γ A} (M : Tm Γ A) {ρ₁ ρ₂} → All₂ _≈_ ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (enclose M))
runs≈ : ∀ ck {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ₁ ρ₂} → All₂ _≈_ ρ₁ ρ₂
  → RelResult (All₂ _≈_) (S.evals ck ρ₁ Ms) (T.evals ck ρ₂ (encs Ms))
call≈ : ∀ ck {A B} {f : S.Val (A ⇒ B)} {g v w} → f ≈ g → v ≈ w → RelResult _≈_ (S.call ck f v) (T.call ck g w)

run≈ ck (` x) ρ = ret (lookup₂ ρ x)
run≈ ck (lam N) {ρ₂ = ρ₂} ρ rewrite evals-vars ck (λ x → x) ρ₂ = ret (pack≈ (tab-lookup₂ ρ) (same refl))
run≈ ck (app L M) ρ = bind-rel (run≈ ck L ρ) λ f → bind-rel (run≈ ck M ρ) λ w → call≈ ck f w
run≈ ck (lit B c) ρ = ret const≈
run≈ ck (tuple Ms) ρ = bind-rel (runs≈ ck Ms ρ) λ vs → ret (tup≈ vs)
run≈ ck (get i M) ρ = bind-rel (run≈ ck M ρ) λ v → ret (nth≈ i v)
run≈ ck (inl M) ρ = bind-rel (run≈ ck M ρ) λ v → ret (inl≈ v)
run≈ ck (inr M) ρ = bind-rel (run≈ ck M ρ) λ v → ret (inr≈ v)
run≈ ck (case L M N) ρ =
  bind-rel (run≈ ck L ρ) λ u → either≈ u (λ v → run≈ ck M (v ∷ ρ)) (λ v → run≈ ck N (v ∷ ρ))
run≈ ck (prim p L M) ρ = bind-rel (run≈ ck L ρ) λ v → bind-rel (run≈ ck M ρ) λ w → ret (δ≈ p v w)
run≈ ck (let′ M N) ρ = bind-rel (run≈ ck M ρ) λ v → run≈ ck N (v ∷ ρ)
run≈ ck (fold M) ρ = bind-rel (run≈ ck M ρ) λ v → ret (fold≈ v)
run≈ ck (unfold M) ρ = bind-rel (run≈ ck M ρ) λ v → ret (unfold≈ v)

runs≈ ck [] ρ = ret []
runs≈ ck (M ∷ Ms) ρ = bind-rel (run≈ ck M ρ) λ v → bind-rel (runs≈ ck Ms ρ) λ vs → ret (v ∷ vs)

call≈ zero f w = timeout
call≈ (suc ck) (pack≈ {c = N} ρ (same refl)) w = run≈ ck N (w ∷ ρ)

enclose-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (enclose M))
enclose-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M []
