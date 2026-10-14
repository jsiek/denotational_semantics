{-

  Correctness of typed concretize (Clos2ᵀ → Clos3ᵀ), clock for clock
  (see the design note in Semantics/Interp/Clock.agda). Each Clos2ᵀ
  variable x lives in Clos3ᵀ where φ x says (a variable, or a component
  of a tuple held in a variable), so environments are related through
  φ (Env≈); a closure of N and vs is related to one of
  concretize fv-ref N and related values (Rel, Same).

-}

module proof.Correctness.Interp.ConcretizeFuel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Language.Typed.Type
open import Language.Typed.Clos2
import Language.Typed.Clos3 as C3
open import Compiler.Concretize
open import proof.Semantics.Interp.Clock
open import Framework.Lookup using (_!_)
import Semantics.Interp.Typed.Clos2 as S
import Semantics.Interp.Typed.Clos3 as T
open import proof.Semantics.Interp.Typed.Rel {λ k → Tm (suc k) Any} {λ n → C3.Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any}

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

Code : ∀ {n} → Tm (suc n) Any → C3.Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → Set
Code N N' = concretize fv-ref N ≡ N'

open Rel Code (Same Code)

{- the value at a reference -}
deref : ∀ {Γ} → Ref Γ → T.Env Γ → T.Val Any
deref (var x) ρ = ρ ! x
deref (prj i x) ρ = T.nth i (ρ ! x)

Env≈ : ∀ {k Γ} → (Fin k → Ref Γ) → S.Env k → T.Env Γ → Set
Env≈ φ ρ₁ ρ₂ = ∀ x → V.lookup ρ₁ x ≈ deref (φ x) ρ₂

env-ext : ∀ {k Γ} {φ : Fin k → Ref Γ} {ρ₁ ρ₂ v w} → v ≈ w → Env≈ φ ρ₁ ρ₂ → Env≈ (ext-ref φ) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext {φ = φ} r E zero = r
env-ext {φ = φ} r E (suc x) with φ x | E x
... | var y | e = e
... | prj i y | e = e

ref≈ : ∀ ck {Γ v} (a : Ref Γ) {ρ} → v ≈ deref a ρ → RelResult _≈_ (ret v) (T.eval ck ρ (ref-tm a))
ref≈ ck (var x) r = ret r
ref≈ ck (prj i x) r = ret r

run≈ : ∀ ck {k Γ A} (M : Tm k A) {φ : Fin k → Ref Γ} {ρ₁ ρ₂} → Env≈ φ ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (concretize φ M))
runs≈ : ∀ ck {k Γ n} (Ms : Vec (Tm k Any) n) {φ : Fin k → Ref Γ} {ρ₁ ρ₂} → Env≈ φ ρ₁ ρ₂
  → RelResult (Pointwise _≈_) (S.evals ck ρ₁ Ms) (T.evals ck ρ₂ (concs φ Ms))
call≈ : ∀ ck {f g v w} → f ≈ g → v ≈ w → RelResult _≈_ (S.call ck f v) (T.call ck g w)

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
run≈ ck (inject G M) E = bind-rel (run≈ ck M E) λ v → ret (dyn≈ v)
run≈ ck (project t M) E = bind-rel (run≈ ck M E) (project≈ t)

runs≈ ck [] E = ret []
runs≈ ck (M ∷ Ms) E = bind-rel (run≈ ck M E) λ v → bind-rel (runs≈ ck Ms E) λ vs → ret (v ∷ vs)

call≈ zero f w = timeout
call≈ (suc ck) (pack≈ {c = N} rs (same refl)) w = run≈ ck N λ { zero → w ; (suc i) → lookup rs i }

concretize-correct : ∀ (M : Tm 0 Any) → Equivalent (S.sem M) (T.sem (concretize-program M))
concretize-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M λ ()
