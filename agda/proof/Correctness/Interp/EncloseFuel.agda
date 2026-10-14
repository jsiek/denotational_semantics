{-

  Correctness of typed enclose (ISWIMᵀ → Clos2ᵀ), clock for clock (see
  the design note in Semantics/Interp/Clock.agda): a term and its
  enclosure, in related environments, both time out, both error (at the
  same project), or return related values, for every clock. A closure
  captures every variable of its context in order, so an ISWIMᵀ closure
  of N and ρ is related to the Clos2ᵀ closure of enclose N and an
  environment related to ρ (Rel, Same).

-}

module proof.Correctness.Interp.EncloseFuel where

open import Data.Nat using (ℕ; zero; suc)
open import Language.Typed.Type
open import Language.Typed.ISWIM
import Language.Typed.Clos2 as C2
open import Compiler.Enclose
open import proof.Semantics.Interp.Clock
import Semantics.Interp.Typed.ISWIM as S
import Semantics.Interp.Typed.Clos2 as T
open import proof.Semantics.Interp.Typed.Rel {λ k → Tm (suc k) Any} {λ k → C2.Tm (suc k) Any}

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; tabulate)
import Data.Vec as V
open import Data.Vec.Properties using (tabulate∘lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Code : ∀ {n} → Tm (suc n) Any → C2.Tm (suc n) Any → Set
Code N N' = enclose N ≡ N'

open Rel Code (Same Code)

{- the captured variables evaluate to the environment -}
evals-vars : ∀ ck {k n} (f : Fin n → Fin k) (ρ : T.Env k)
  → T.evals ck ρ (tabulate (λ i → C2.` f i)) ≡ ret (tabulate (λ i → V.lookup ρ (f i)))
evals-vars ck {n = zero} f ρ = refl
evals-vars ck {n = suc n} f ρ rewrite evals-vars ck (λ i → f (suc i)) ρ = refl

run≈ : ∀ ck {k A} (M : Tm k A) {ρ₁ ρ₂} → Pointwise _≈_ ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (enclose M))
runs≈ : ∀ ck {k n} (Ms : Vec (Tm k Any) n) {ρ₁ ρ₂} → Pointwise _≈_ ρ₁ ρ₂
  → RelResult (Pointwise _≈_) (S.evals ck ρ₁ Ms) (T.evals ck ρ₂ (encs Ms))
call≈ : ∀ ck {f g v w} → f ≈ g → v ≈ w → RelResult _≈_ (S.call ck f v) (T.call ck g w)

run≈ ck (` x) ρ = ret (lookup ρ x)
run≈ ck (lam N) {ρ₂ = ρ₂} ρ rewrite evals-vars ck (λ i → i) ρ₂ | tabulate∘lookup ρ₂ = ret (pack≈ ρ (same refl))
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
run≈ ck (inject G M) ρ = bind-rel (run≈ ck M ρ) λ v → ret (dyn≈ v)
run≈ ck (project t M) ρ = bind-rel (run≈ ck M ρ) (project≈ t)

runs≈ ck [] ρ = ret []
runs≈ ck (M ∷ Ms) ρ = bind-rel (run≈ ck M ρ) λ v → bind-rel (runs≈ ck Ms ρ) λ vs → ret (v ∷ vs)

call≈ zero f w = timeout
call≈ (suc ck) (pack≈ {c = N} ρ (same refl)) w = run≈ ck N (w ∷ ρ)

enclose-correct : ∀ (M : Tm 0 Any) → Equivalent (S.sem M) (T.sem (enclose M))
enclose-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M []
