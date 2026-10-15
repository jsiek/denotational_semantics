{-

  Correctness of typed enclose (ISWIMᵀ → Clos2ᵀ) in the graph model with
  errors (Semantics/GraphErr/Typed/{ISWIM,Clos2}.agda).

  ⟦ M ⟧ ρ ≃ ⟦ enclose M ⟧₂ ρ' when the environments agree on the k
  variables in scope and ρ' holds values there (Rel). Every case but
  the function is a congruence, as no typed operator checks a kind but
  project, which is the same on both sides. A function becomes a closure
  that binds all k variables of its context: since they are values, the
  binds are their left unit (binds-val-≃), and the code's environment
  fv-env k agrees with ρ' below k, so the bodies are related under the
  binder (Λᵐ-≃).

-}

module proof.Correctness.GraphErr.EncloseCorrect where

open import proof.Framework.GraphModel.ErrorPrelude
open import Language.Typed.Type
open import Language.Typed.ISWIM
import Language.Typed.Clos2 as T
open import Semantics.GraphErr.Typed.ISWIM
open import proof.Semantics.GraphErr.Typed.Clos2
  using (appᵗ-≃; getᵗ-≃; caseᵗ-≃; primᵗ-≃; projectᵗ-≃; ⌊⌋-≃; binds-val-≃; fv-env-nth; fv-env)
  renaming (⟦_⟧ to ⟦_⟧₂; ⟦_⟧s to ⟦_⟧s₂)
open import Compiler.Enclose

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (suc)
open import Data.Vec using (Vec; []; _∷_; tabulate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

{- the environments agree on the variables in scope, values in ρ' -}
Rel : ∀ k → Env Value → Env Value → Set
Rel k ρ ρ' = ∀ (x : Fin k) → ρ (toℕ x) ≃ ρ' (toℕ x) × Val (ρ' (toℕ x))

ext : ∀ {k ρ ρ' X X'} → X ≃ X' → Val X' → Rel k ρ ρ' → Rel (suc k) (X • ρ) (X' • ρ')
ext X≃ v r zero = ⟨ X≃ , v ⟩
ext X≃ v r (suc x) = r x

tab-nth : ∀ {k n} (f : Fin n → T.Tm k Any) ρ i → nthD (⟦ tabulate f ⟧s₂ ρ) i ≡ ⟦ f i ⟧₂ ρ
tab-nth f ρ zero = refl
tab-nth f ρ (suc i) = tab-nth (λ j → f (suc j)) ρ i

enc : ∀ {k A} (M : Tm k A) {ρ ρ'} → Rel k ρ ρ' → ⟦ M ⟧ ρ ≃ ⟦ enclose M ⟧₂ ρ'
encs-nth : ∀ {k n} (Ms : Vec (Tm k Any) n) {ρ ρ'} → Rel k ρ ρ'
  → ∀ i → nthD (⟦ Ms ⟧s ρ) i ≃ nthD (⟦ encs Ms ⟧s₂ ρ') i

enc (` x) r = proj₁ (r x)
enc {k} (lam N) {ρ} {ρ'} r =
  ≃-sym (binds-val-≃ k (λ i → Val-≃ (≃-reflexive (sym (tab-nth T.`_ ρ' i))) (proj₂ (r i)))
    λ {Xs} Xs≃ → Λᵐ-≃ λ V ne _ nV → ≃-sym (enc N (ext ≃-refl (noerr-val V ne nV) λ x →
      let e = ≃-trans (≃-reflexive (sym (tab-nth T.`_ ρ' x)))
                (≃-trans (≃-sym (Xs≃ x)) (≃-reflexive (sym (fv-env-nth k Xs x)))) in
      ⟨ ≃-trans (proj₁ (r x)) e , Val-≃ e (proj₂ (r x)) ⟩)))
enc (app L M) r = appᵗ-≃ (enc L r) (enc M r)
enc (lit B c) r = ≃-refl
enc (tuple {n = n} Ms) r = 𝒯ᵐ-≃ n (encs-nth Ms r)
enc (get i M) r = getᵗ-≃ i (enc M r)
enc (inl M) r = inlᵐ-≃ (enc M r)
enc (inr M) r = inrᵐ-≃ (enc M r)
enc (case L M N) {ρ} {ρ'} r =
  caseᵗ-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ enclose M ⟧₂ (X • ρ')} {λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ enclose N ⟧₂ (X • ρ')}
    (enc L r) (λ V ne _ nV → enc M (ext ≃-refl (noerr-val V ne nV) r)) (λ V ne _ nV → enc N (ext ≃-refl (noerr-val V ne nV) r))
enc (prim p L M) r = primᵗ-≃ p (enc L r) (enc M r)
enc (let′ M N) {ρ} {ρ'} r =
  ≫=-≃ {F = λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ enclose N ⟧₂ (X • ρ')} (enc M r)
    (λ _ c → enc N (ext (⌊⌋-≃ (enc M r)) (⌊⌋-val c) r))
enc (inject G M) r = enc M r
enc (project G M) r = projectᵗ-≃ (λ k → k) _ (enc M r)

encs-nth (M ∷ Ms) r zero = enc M r
encs-nth (M ∷ Ms) r (suc i) = encs-nth Ms r i

{- The end theorem: closed programs ------------------------------------------------}

enclose-correct : ∀ (M : Tm 0 Any) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct M = enc M (λ ())
