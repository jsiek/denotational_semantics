{-

  Correctness of prune (Closμ → Closμ), clock for clock, as for
  typed prune (proof/Correctness/Interp/PruneFuel.agda; see the
  design note in Semantics/Interp/Clock.agda).

  The pass renames the variables a term uses, so environments agree
  through the renaming r on them (Agree). A closure of N and vs is
  related to one of N, renamed by squeeze, and the values of vs that fl
  keeps (Opt), when N uses only kept ones (cov); a dropped free variable
  is a variable, which the target does not evaluate, but whose value in
  the target environment is related (Sel).

-}

module Mu.proof.Correctness.ClockedInterpreters.PruneFuel where

open import Data.List using ([]; _∷_)
open import Mu.Language.Type
open import Mu.Language.Clos
open import Mu.Compiler.Prune
open import Mu.Framework.AllUtil
  using (All; []; _∷_; lookup; Flags; kept; select; Kept; squeeze; ∨-l; ∨-r; All₂; lookup₂; Thin; keep; drop; thin-lookup)
open import proof.Semantics.Interp.Clock
import Mu.Semantics.ClockedInterpreters.Clos as C
open import Mu.proof.Semantics.ClockedInterpreters.Rel {λ Δ A B → Tm (A ∷ Δ) B} {λ Δ A B → Tm (A ∷ Δ) B}

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary.Decidable using (fromWitness)

data Opt : ∀ {Δ Δ' A B} → Tm (A ∷ Δ) B → All C.Val Δ → Tm (A ∷ Δ') B → All C.Val Δ' → Set where
  opt≈ : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {vs} (fl : Flags Δ) (cov : ∀ {C} (x : (A ∷ Δ) ∋ C) → T (uses N x) → Kept fl x)
    → Opt N vs (opt N λ x t → squeeze fl x (cov x t)) (select fl vs)

open Rel (λ _ _ → ⊥) Opt

Agree : ∀ {Γ Γ'} (u : ∀ {C} → Γ ∋ C → Bool) → Ren u Γ' → C.Env Γ → C.Env Γ' → Set
Agree u r ρ₁ ρ₂ = ∀ {C} x (t : T (u {C} x)) → lookup ρ₁ x ≈ lookup ρ₂ (r x t)

ext-agree : ∀ {Γ Γ' A} {u : ∀ {C} → (A ∷ Γ) ∋ C → Bool} {r : Ren (λ x → u (S x)) Γ'} {ρ₁ ρ₂ v w}
  → v ≈ w → Agree (λ x → u (S x)) r ρ₁ ρ₂ → Agree u (ext {u = u} r) (v ∷ ρ₁) (w ∷ ρ₂)
ext-agree vw ag Z _ = vw
ext-agree vw ag (S x) t = ag x t

{- ws are the values of vs' that fl keeps, for some vs' related to vs -}
Sel : ∀ {Δ} (fl : Flags Δ) → All C.Val Δ → All C.Val (kept fl) → Set
Sel fl vs ws = Σ[ vs' ∈ _ ] All₂ _≈_ vs vs' × select fl vs' ≡ ws

pw-thin : ∀ {Δ} (fl : Flags Δ) {vs vs' : All C.Val Δ} → All₂ _≈_ vs vs' → Thin _≈_ fl vs (select fl vs')
pw-thin [] [] = []
pw-thin (true ∷ fl) (r ∷ rs) = keep r (pw-thin fl rs)
pw-thin (false ∷ fl) (r ∷ rs) = drop (pw-thin fl rs)

run≈ : ∀ ck {Γ Γ' A} (M : Tm Γ A) {r : Ren (uses M) Γ'} {ρ₁ ρ₂} → Agree (uses M) r ρ₁ ρ₂
  → RelResult _≈_ (C.eval ck ρ₁ M) (C.eval ck ρ₂ (opt M r))
runs≈ : ∀ ck {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} {ρ₁ ρ₂} → Agree (usesA Ms) r ρ₁ ρ₂
  → RelResult (All₂ _≈_) (C.evals ck ρ₁ Ms) (C.evals ck ρ₂ (opts Ms r))
sel≈ : ∀ ck {Γ Γ' Δ} (u : ∀ {C} → Δ ∋ C → Bool) (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} {ρ₁ ρ₂}
  → Agree (usesA Ms) r ρ₁ ρ₂
  → RelResult (Sel (flags u Ms)) (C.evals ck ρ₁ Ms) (C.evals ck ρ₂ (select (flags u Ms) (opts Ms r)))
call≈ : ∀ ck {A B} {f : C.Val (A ⇒ B)} {g v w} → f ≈ g → v ≈ w → RelResult _≈_ (C.call ck f v) (C.call ck g w)

run≈ ck (` x) ag = ret (ag x (fromWitness refl))
run≈ ck (clos N Ms) ag =
  bind-rel (sel≈ ck (λ x → uses N (S x)) Ms ag) λ { (_ , rs , refl) → ret (pack≈ rs (opt≈ _ (covers N Ms))) }
run≈ ck (app L M) ag =
  bind-rel (run≈ ck L λ x t → ag x (∨-l _ t)) λ f →
  bind-rel (run≈ ck M λ x t → ag x (∨-r (uses L x) t)) λ w → call≈ ck f w
run≈ ck (lit B c) ag = ret const≈
run≈ ck (tuple Ms) ag = bind-rel (runs≈ ck Ms ag) λ vs → ret (tup≈ vs)
run≈ ck (get i M) ag = bind-rel (run≈ ck M ag) λ v → ret (nth≈ i v)
run≈ ck (inl M) ag = bind-rel (run≈ ck M ag) λ v → ret (inl≈ v)
run≈ ck (inr M) ag = bind-rel (run≈ ck M ag) λ v → ret (inr≈ v)
run≈ ck (case L M N) ag =
  bind-rel (run≈ ck L λ x t → ag x (∨-l _ t)) λ u → either≈ u
    (λ v → run≈ ck M (ext-agree {u = uses M} v λ x t → ag x (∨-r (uses L x) (∨-l (uses N (S x)) t))))
    (λ v → run≈ ck N (ext-agree {u = uses N} v λ x t → ag x (∨-r (uses L x) (∨-r (uses M (S x)) t))))
run≈ ck (prim p L M) ag =
  bind-rel (run≈ ck L λ x t → ag x (∨-l _ t)) λ v →
  bind-rel (run≈ ck M λ x t → ag x (∨-r (uses L x) t)) λ w → ret (δ≈ p v w)
run≈ ck (let′ M N) ag =
  bind-rel (run≈ ck M λ x t → ag x (∨-l _ t)) λ v →
  run≈ ck N (ext-agree {u = uses N} v λ x t → ag x (∨-r (uses M x) t))
run≈ ck (fold M) ag = bind-rel (run≈ ck M ag) λ v → ret (fold≈ v)
run≈ ck (unfold M) ag = bind-rel (run≈ ck M ag) λ v → ret (unfold≈ v)

runs≈ ck [] ag = ret []
runs≈ ck (M ∷ Ms) ag =
  bind-rel (run≈ ck M λ x t → ag x (∨-l _ t)) λ v →
  bind-rel (runs≈ ck Ms λ x t → ag x (∨-r (uses M x) t)) λ vs → ret (v ∷ vs)

sel≈ ck u [] ag = ret ([] , [] , refl)
sel≈ ck u (M ∷ Ms) ag with keep? M (u Z) | fl-ok M (u Z)
... | true | _ =
  bind-rel (run≈ ck M λ x t → ag x (∨-l _ t)) λ v →
  bind-rel (sel≈ ck (λ x → u (S x)) Ms λ x t → ag x (∨-r (uses M x) t)) λ
    { (vs' , rs , refl) → ret (_ ∷ vs' , v ∷ rs , refl) }
... | false | var-fv {x} =
  subst (RelResult _ _) (bind-ret _) (bind-rel (sel≈ ck (λ x → u (S x)) Ms λ y t → ag y (∨-r (uses (` x) y) t)) λ
    { (vs' , rs , e) → ret (_ ∷ vs' , ag x (∨-l (usesA Ms x) (fromWitness refl)) ∷ rs , e) })

call≈ zero f w = timeout
call≈ (suc ck) (pack≈ {c = N} rs (opt≈ fl cov)) w = run≈ ck N λ x t → thin-lookup w (pw-thin fl rs) x (cov x t)

prune-correct : ∀ {A} (M : Tm [] A) → Equivalent (C.sem M) (C.sem (prune-program M))
prune-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M λ ()
