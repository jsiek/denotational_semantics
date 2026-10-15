{-

  Correctness of typed optimize (Clos2ᵀ → Clos2ᵀ) in the graph model
  with errors (Semantics/GraphErr/Typed/Clos2.agda).

  ⟦ M ⟧ ρ ≃ ⟦ opt r M ⟧ ρ' when ρ and ρ' agree through r on the
  variables that M uses (Agree), and ρ holds values on all variables in
  scope (Vals). Every case but the closure is a congruence. A closure
  binds its free variables left to right: a kept one on both sides
  (≫=-≃), a dropped one, a variable, only in the source, where it is a
  set of values, so its bind is the left unit (≫=-val-β). The bound
  sets are related by the selection (Thin), so the environments of the
  codes agree through squeeze on the variables the code uses.

-}

module proof.Correctness.GraphErr.OptimizeCorrect where

open import proof.Framework.GraphModel.ErrorPrelude
open import Language.Typed.Type
open import Language.Typed.Clos2
open import proof.Semantics.GraphErr.Typed.Clos2
  using (⟦_⟧; ⟦_⟧s; fv-env; appᵗ-≃; getᵗ-≃; caseᵗ-≃; primᵗ-≃; projectᵗ-≃; ⌊⌋-≃; fv-env-nth)
open import Compiler.Optimize
open import Framework.VecSelect
open import proof.Framework.VecSelect

open import Data.Bool using (Bool; T)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Relation.Nullary.Decidable using (fromWitness)

Vals : ∀ k → Env Value → Set
Vals k ρ = ∀ (x : Fin k) → Val (ρ (toℕ x))

Agree : ∀ {k k'} → (Fin k → Bool) → (Fin k → Fin k') → Env Value → Env Value → Set
Agree u r ρ ρ' = ∀ x → T (u x) → ρ (toℕ x) ≃ ρ' (toℕ (r x))

{- under a binder -}
ext-agree : ∀ {k k' u r ρ ρ' X X'} → X ≃ X' → Agree {k} {k'} (λ x → u (suc x)) r ρ ρ' → Agree u (ext r) (X • ρ) (X' • ρ')
ext-agree X≃ ag zero _ = X≃
ext-agree X≃ ag (suc x) t = ag x t

ext-vals : ∀ {k ρ X} → Val X → Vals k ρ → Vals (suc k) (X • ρ)
ext-vals v V zero = v
ext-vals v V (suc x) = V x

{- the environment of the code of a closure -}
vec : ∀ n → Results (𝒫 Value) (replicate n ■) → Vec (𝒫 Value) n
vec zero _ = []
vec (suc n) ⟨ X , Xs ⟩ = X ∷ vec n Xs

code-env : ∀ n Xs Y (x : Fin (suc n)) → (Y • fv-env n Xs) (toℕ x) ≡ lookup (Y ∷ vec n Xs) x
code-env n Xs Y zero = refl
code-env (suc n) ⟨ X , Xs ⟩ Y (suc zero) = refl
code-env (suc n) ⟨ X , Xs ⟩ Y (suc (suc i)) = code-env n Xs X (suc i)

opt-ok : ∀ {k k' A} (M : Tm k A) {r : Fin k → Fin k'} {ρ ρ'} → Vals k ρ → Agree (uses M) r ρ ρ' → ⟦ M ⟧ ρ ≃ ⟦ opt r M ⟧ ρ'
opts-ok : ∀ {k k' n} (Ms : Vec (Tm k Any) n) {r : Fin k → Fin k'} {ρ ρ'} → Vals k ρ → Agree (usesV Ms) r ρ ρ'
  → ∀ i → nthD (⟦ Ms ⟧s ρ) i ≃ nthD (⟦ opts r Ms ⟧s ρ') i

{- binding the free variables and binding the kept ones -}
binds-ok : ∀ {k k' n} (fl : Vec Bool n) (Ms : Vec (Tm k Any) n) {u : Fin n → Bool} {r : Fin k → Fin k'} {ρ ρ' K K'}
  → (∀ i → Fl (u i) (lookup fl i) (lookup Ms i)) → Vals k ρ → Agree (usesV Ms) r ρ ρ'
  → (∀ {Xs Ys} → AllVal n Xs → Thin _≃_ fl (vec n Xs) (vec _ Ys) → K Xs ≃ K' Ys)
  → binds n (⟦ Ms ⟧s ρ) K ≃ binds (count fl) (⟦ select fl (opts r Ms) ⟧s ρ') K'
binds-ok [] [] s V ag h = h (λ ()) []
binds-ok (b ∷ fl) (M ∷ Ms) {r = r} {ρ} {ρ'} {K} {K'} s V ag h with s zero
... | kept = ≫=-≃ {F = λ X → binds _ (⟦ Ms ⟧s ρ) (λ Xs → K ⟨ X , Xs ⟩)} {λ Y → binds _ (⟦ select fl (opts r Ms) ⟧s ρ') (λ Ys → K' ⟨ Y , Ys ⟩)}
    M≃ λ c _ → binds-ok fl Ms (λ i → s (suc i)) V (subR ag)
      λ vs th → h (λ { zero → ⌊⌋-val c ; (suc i) → vs i }) (keep (⌊⌋-≃ M≃) th)
  where M≃ = opt-ok M V (subL ag)
... | var {x = x} _ = ≃-trans (≫=-val-β {F = λ X → binds _ (⟦ Ms ⟧s ρ) (λ Xs → K ⟨ X , Xs ⟩)} (V x))
    (binds-ok fl Ms (λ i → s (suc i)) V (subR ag)
      λ vs th → h (λ { zero → ⌊⌋-val (Val⇒Conv (V x)) ; (suc i) → vs i }) (drop th))

opt-ok (` x) V ag = ag x (fromWitness refl)
opt-ok (clos {n} N Ms) V ag =
  binds-ok (keeps N Ms) Ms s V ag λ {Xs} {Ys} vs th → Λᵐ-≃ λ W ne _ nW →
    opt-ok N {squeeze (keeps N Ms)} (ext-vals (noerr-val W ne nW) λ i → subst Val (sym (fv-env-nth n Xs i)) (vs i))
      λ x u → subst₂ _≃_ (sym (code-env n Xs (mem W) x)) (sym (code-env _ Ys (mem W) (squeeze (keeps N Ms) x)))
                (thin-lookup ≃-refl th x (covers {N = N} {Ms} s x u))
  where s = flags-ok (λ i → uses N (suc i)) Ms
opt-ok (app L M) V ag = appᵗ-≃ (opt-ok L V (subL ag)) (opt-ok M V (subR ag))
opt-ok (lit B c) V ag = ≃-refl
opt-ok (tuple {n = n} Ms) V ag = 𝒯ᵐ-≃ n (opts-ok Ms V ag)
opt-ok (get i M) V ag = getᵗ-≃ i (opt-ok M V ag)
opt-ok (inl M) V ag = inlᵐ-≃ (opt-ok M V ag)
opt-ok (inr M) V ag = inrᵐ-≃ (opt-ok M V ag)
opt-ok (case L M N) {r} {ρ} {ρ'} V ag =
  caseᵗ-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ opt (ext r) M ⟧ (X • ρ')} {λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ opt (ext r) N ⟧ (X • ρ')}
    (opt-ok L V (subL ag))
    (λ W ne _ nW → opt-ok M (ext-vals (noerr-val W ne nW) V) (ext-agree ≃-refl (subL (subR {u = uses L} ag))))
    (λ W ne _ nW → opt-ok N (ext-vals (noerr-val W ne nW) V) (ext-agree ≃-refl (subR (subR {u = uses L} ag))))
opt-ok (prim p L M) V ag = primᵗ-≃ p (opt-ok L V (subL ag)) (opt-ok M V (subR ag))
opt-ok (let′ M N) {r} {ρ} {ρ'} V ag =
  ≫=-≃ {F = λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ opt (ext r) N ⟧ (X • ρ')} M≃
    (λ c _ → opt-ok N (ext-vals (⌊⌋-val c) V) (ext-agree (⌊⌋-≃ M≃) (subR ag)))
  where M≃ = opt-ok M V (subL ag)
opt-ok (inject G M) V ag = opt-ok M V ag
opt-ok (project G M) V ag = projectᵗ-≃ (λ k → k) _ (opt-ok M V ag)

opts-ok (M ∷ Ms) V ag zero = opt-ok M V (subL ag)
opts-ok (M ∷ Ms) V ag (suc i) = opts-ok Ms V (subR ag) i

{- The end theorem: closed programs ------------------------------------------------}

optimize-correct : ∀ (M : Tm 0 Any) → ⟦ M ⟧ ρ₀ ≃ ⟦ optimize-program M ⟧ ρ₀
optimize-correct M = opt-ok M (λ ()) (λ ())
