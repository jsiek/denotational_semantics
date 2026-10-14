{-

  Correctness of typed delay (Clos3ᵀ → Clos4ᵀ), clock for clock (see
  the design note in Semantics/Interp/Clock.agda): clos N Ms becomes
  pack (code N') (tuple Ms'), and app becomes callc, which calls as app
  does. The pass renames variables (the identity for a program), so
  environments are related through the renaming (Env≈); a closure of N
  and vs is related to a pack of the code delay N and related values
  (Rel, Same).

-}

module proof.Correctness.Interp.Typed.DelayFuel where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Language.Typed.Type
open import Language.Typed.Clos3
import Language.Typed.Clos4 as C4
open import Compiler.Typed.Delay
open import proof.Semantics.Interp.Clock
open import Framework.Lookup using (_!_)
import Semantics.Interp.Typed.Clos3 as S
import Semantics.Interp.Typed.Clos4 as T
open import proof.Semantics.Interp.Typed.Rel
  {λ n → Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any} {λ n → C4.Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any}

open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

Code : ∀ {n} → Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → C4.Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → Set
Code N N' = delay (λ x → x) N ≡ N'

open Rel Code (Same Code)

Env≈ : ∀ {Γ Δ} → Ren Γ Δ → S.Env Γ → T.Env Δ → Set
Env≈ r ρ₁ ρ₂ = ∀ {A} (x : _ ∋ A) → ρ₁ ! x ≈ ρ₂ ! r x

env-ext : ∀ {Γ Δ} {r : Ren Γ Δ} {ρ₁ ρ₂ v w} → v ≈ w → Env≈ r ρ₁ ρ₂ → Env≈ (ext {B = Any} r) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext v E Z = v
env-ext v E (S x) = E x

run≈ : ∀ ck {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ₁ ρ₂} → Env≈ r ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (delay r M))
runs≈ : ∀ ck {Γ Δ n} (Ms : Vec (Tm Γ Any) n) {r : Ren Γ Δ} {ρ₁ ρ₂} → Env≈ r ρ₁ ρ₂
  → RelResult (Pointwise _≈_) (S.evals ck ρ₁ Ms) (T.evals ck ρ₂ (delays r Ms))
call≈ : ∀ ck {f g v w} → f ≈ g → v ≈ w → RelResult _≈_ (S.call ck f v) (T.call ck g w)

run≈ ck (` x) E = ret (E x)
run≈ ck (clos N Ms) {r} {ρ₂ = ρ₂} E = subst (RelResult _≈_ _) (sym (bind-assoc (T.evals ck ρ₂ (delays r Ms))))
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
run≈ ck (inject G M) E = bind-rel (run≈ ck M E) λ v → ret (dyn≈ v)
run≈ ck (project t M) E = bind-rel (run≈ ck M E) (project≈ t)

runs≈ ck [] E = ret []
runs≈ ck (M ∷ Ms) E = bind-rel (run≈ ck M E) λ v → bind-rel (runs≈ ck Ms E) λ vs → ret (v ∷ vs)

call≈ zero f w = timeout
call≈ (suc ck) (pack≈ {c = N} rs (same refl)) w = run≈ ck N λ { Z → w ; (S Z) → tup≈ rs }

delay-correct : ∀ (M : Tm [] Any) → Equivalent (S.sem M) (T.sem (delay-program M))
delay-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M λ ()
