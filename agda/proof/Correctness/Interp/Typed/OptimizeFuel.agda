{-

  Correctness of typed optimize (Clos2ᵀ → Clos2ᵀ), clock for clock (see
  the design note in Semantics/Interp/Clock.agda).

  The pass renames variables, so environments agree through the
  renaming r on the variables that a term uses (Agree). A closure of N
  and vs is related to one of opt (squeeze fl) N and the values of vs
  that fl keeps (Opt), when N uses only kept ones; a dropped free
  variable is a variable, which the target does not evaluate, but whose
  value in the target environment is related (Sel).

-}

module proof.Correctness.Interp.Typed.OptimizeFuel where

open import Data.Nat using (ℕ; zero; suc)
open import Language.Typed.Type
open import Language.Typed.Clos2
open import Compiler.Typed.Optimize
open import Framework.VecSelect
open import proof.Framework.VecSelect
open import proof.Semantics.Interp.Clock
import Semantics.Interp.Typed.Clos2 as C
open import proof.Semantics.Interp.Typed.Rel {λ k → Tm (suc k) Any} {λ k → Tm (suc k) Any}

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary.Decidable using (fromWitness)

data Opt : ∀ {n m} → Tm (suc n) Any → Vec (C.Val Any) n → Tm (suc m) Any → Vec (C.Val Any) m → Set where
  opt≈ : ∀ {n N vs} (fl : Vec Bool n) → (∀ x → T (uses N x) → Kept fl x)
    → Opt N vs (opt (squeeze fl) N) (select fl vs)

open Rel (λ _ _ → ⊥) Opt

Agree : ∀ {k k'} → (Fin k → Bool) → (Fin k → Fin k') → C.Env k → C.Env k' → Set
Agree u r ρ₁ ρ₂ = ∀ x → T (u x) → V.lookup ρ₁ x ≈ V.lookup ρ₂ (r x)

ext-agree : ∀ {k k' u r ρ₁ ρ₂ v w} → v ≈ w → Agree {k} {k'} (λ x → u (suc x)) r ρ₁ ρ₂ → Agree u (ext r) (v ∷ ρ₁) (w ∷ ρ₂)
ext-agree vw ag zero _ = vw
ext-agree vw ag (suc x) t = ag x t

{- ws are the values of vs' that fl keeps, for some vs' related to vs -}
Sel : ∀ {n} (fl : Vec Bool n) → Vec (C.Val Any) n → Vec (C.Val Any) (count fl) → Set
Sel fl vs ws = Σ[ vs' ∈ _ ] Pointwise (_≈_ {Any}) vs vs' × select fl vs' ≡ ws

pw-thin : ∀ {n} (fl : Vec Bool n) {vs vs'} → Pointwise (_≈_ {Any}) vs vs' → Thin _≈_ fl vs (select fl vs')
pw-thin [] [] = []
pw-thin (true ∷ fl) (r ∷ rs) = keep r (pw-thin fl rs)
pw-thin (false ∷ fl) (r ∷ rs) = drop (pw-thin fl rs)

run≈ : ∀ ck {k k' A} (M : Tm k A) {r : Fin k → Fin k'} {ρ₁ ρ₂} → Agree (uses M) r ρ₁ ρ₂
  → RelResult _≈_ (C.eval ck ρ₁ M) (C.eval ck ρ₂ (opt r M))
runs≈ : ∀ ck {k k' n} (Ms : Vec (Tm k Any) n) {r : Fin k → Fin k'} {ρ₁ ρ₂} → Agree (usesV Ms) r ρ₁ ρ₂
  → RelResult (Pointwise _≈_) (C.evals ck ρ₁ Ms) (C.evals ck ρ₂ (opts r Ms))
sel≈ : ∀ ck {k k' n} (u : Fin n → Bool) (Ms : Vec (Tm k Any) n) {r : Fin k → Fin k'} {ρ₁ ρ₂}
  → Agree (usesV Ms) r ρ₁ ρ₂
  → RelResult (Sel (flags u Ms)) (C.evals ck ρ₁ Ms) (C.evals ck ρ₂ (select (flags u Ms) (opts r Ms)))
call≈ : ∀ ck {f g v w} → f ≈ g → v ≈ w → RelResult _≈_ (C.call ck f v) (C.call ck g w)

run≈ ck (` x) ag = ret (ag x (fromWitness refl))
run≈ ck (clos N Ms) ag =
  bind-rel (sel≈ ck (λ i → uses N (suc i)) Ms ag) λ { (_ , rs , refl) →
    ret (pack≈ rs (opt≈ _ (covers {N = N} {Ms} (flags-ok (λ i → uses N (suc i)) Ms)))) }
run≈ ck (app L M) ag =
  bind-rel (run≈ ck L (subL ag)) λ f → bind-rel (run≈ ck M (subR ag)) λ w → call≈ ck f w
run≈ ck (lit B c) ag = ret const≈
run≈ ck (tuple Ms) ag = bind-rel (runs≈ ck Ms ag) λ vs → ret (tup≈ vs)
run≈ ck (get i M) ag = bind-rel (run≈ ck M ag) λ v → ret (nth≈ i v)
run≈ ck (inl M) ag = bind-rel (run≈ ck M ag) λ v → ret (inl≈ v)
run≈ ck (inr M) ag = bind-rel (run≈ ck M ag) λ v → ret (inr≈ v)
run≈ ck (case L M N) ag =
  bind-rel (run≈ ck L (subL ag)) λ u → either≈ u
    (λ v → run≈ ck M (ext-agree v (subL (subR {u = uses L} ag))))
    (λ v → run≈ ck N (ext-agree v (subR (subR {u = uses L} ag))))
run≈ ck (prim p L M) ag =
  bind-rel (run≈ ck L (subL ag)) λ v → bind-rel (run≈ ck M (subR ag)) λ w → ret (δ≈ p v w)
run≈ ck (let′ M N) ag = bind-rel (run≈ ck M (subL ag)) λ v → run≈ ck N (ext-agree v (subR ag))
run≈ ck (inject G M) ag = bind-rel (run≈ ck M ag) λ v → ret (dyn≈ v)
run≈ ck (project t M) ag = bind-rel (run≈ ck M ag) (project≈ t)

runs≈ ck [] ag = ret []
runs≈ ck (M ∷ Ms) ag =
  bind-rel (run≈ ck M (subL ag)) λ v → bind-rel (runs≈ ck Ms (subR ag)) λ vs → ret (v ∷ vs)

sel≈ ck u [] ag = ret ([] , [] , refl)
sel≈ ck u (M ∷ Ms) ag with keep? M (u zero) | flags-ok u (M ∷ Ms) zero
... | true | kept =
  bind-rel (run≈ ck M (subL ag)) λ v → bind-rel (sel≈ ck (λ i → u (suc i)) Ms (subR ag)) λ
    { (vs' , rs , refl) → ret (_ ∷ vs' , v ∷ rs , refl) }
... | false | var {x = x} _ =
  subst (RelResult _ _) (bind-ret _) (bind-rel (sel≈ ck (λ i → u (suc i)) Ms (subR ag)) λ
    { (vs' , rs , e) → ret (_ ∷ vs' , subL {u = uses (` x)} ag x (fromWitness refl) ∷ rs , e) })

call≈ zero f w = timeout
call≈ (suc ck) (pack≈ {c = N} rs (opt≈ fl cov)) w =
  run≈ ck N λ x u → thin-lookup w (pw-thin fl rs) x (cov x u)

optimize-correct : ∀ (M : Tm 0 Any) → Equivalent (C.sem M) (C.sem (optimize-program M))
optimize-correct M = clocked _≈_ obs≈ λ ck → run≈ ck M λ ()
