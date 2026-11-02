{-

  Correctness of split (EnvClosμ → PairClosμ), clock for clock, as for typed
  split (proof/Correctness/Interp/SplitFuel.agda; see the design note in
  Semantics/Interp/Clock.agda): clos N Ms becomes
  pair (code N') (tuple Ms'), and app becomes callc, which calls as app
  does. The pass renames variables (the identity for a program), so
  environments are related through the renaming (Env≈); a closure of N
  and vs is related to a pack of the code split N and related values
  (Rel, Same).

-}

module Mu.proof.Correctness.ClockedInterpreters.SplitFuel where

open import Data.List using ([]; _∷_)
open import Mu.Language.Type
open import Mu.Language.EnvClos
import Mu.Language.PairClos as C4
open import Mu.Compiler.Split
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂)
open import proof.Semantics.Interp.Clock
import Mu.Semantics.ClockedInterpreters.EnvClos as S
import Mu.Semantics.ClockedInterpreters.PairClos as T
open import Mu.proof.Semantics.ClockedInterpreters.Rel {λ Δ A B → Tm (A ∷ tup Δ ∷ []) B} {λ Δ A B → C4.Tm (A ∷ tup Δ ∷ []) B}

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

Code : ∀ {Δ A B} → Tm (A ∷ tup Δ ∷ []) B → C4.Tm (A ∷ tup Δ ∷ []) B → Set
Code N N' = split (λ x → x) N ≡ N'

open Rel Code (Same Code)

Env≈ : ∀ {Γ Δ} → Ren Γ Δ → S.Env Γ → T.Env Δ → Set
Env≈ r ρ₁ ρ₂ = ∀ {A} (x : _ ∋ A) → lookup ρ₁ x ≈ lookup ρ₂ (r x)

env-ext : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ₁ ρ₂ v w} → v ≈ w → Env≈ r ρ₁ ρ₂ → Env≈ (ext {B = B} r) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext v E Z = v
env-ext v E (S x) = E x

run≈ : ∀ ck {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ₁ ρ₂} → Env≈ r ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (split r M))
runs≈ : ∀ ck {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') {r : Ren Γ Δ} {ρ₁ ρ₂} → Env≈ r ρ₁ ρ₂
  → RelResult (All₂ _≈_) (S.evals ck ρ₁ Ms) (T.evals ck ρ₂ (splits r Ms))
call≈ : ∀ ck {A B} {f : S.Val (A ⇒ B)} {g v w} → f ≈ g → v ≈ w → RelResult _≈_ (S.call ck f v) (T.call ck g w)

run≈ ck (` x) E = ret (E x)
run≈ ck (clos N Ms) {r} {ρ₂ = ρ₂} E = subst (RelResult _≈_ _) (sym (bind-assoc (T.evals ck ρ₂ (splits r Ms))))
  (bind-rel (runs≈ ck Ms E) λ vs → ret (pack≈ vs (same refl)))
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
call≈ (suc ck) (pack≈ {c = N} rs (same refl)) w = run≈ ck N λ { Z → w ; (S Z) → tup≈ rs }

split-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (split-program M))
split-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M λ ()
