{-

  Correctness of typed enclose (ISWIMᵀ → Clos2ᵀ) in the graph model
  (Semantics/Graph/Typed/{ISWIM,Clos2}.agda).

  ⟦ M ⟧ ρ ≃ ⟦ enclose M ⟧₂ ρ' when the environments agree on the k
  variables in scope and ρ' is nonempty there (Rel). Every case but the
  function is a congruence. A function becomes a closure that captures
  all k variables of its context: they are nonempty, so its guard holds,
  and the code's environment fv-env k agrees with ρ' below k.

-}

module proof.Correctness.Graph.EncloseCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Language.Typed.Type
open import Language.Typed.ISWIM
import Language.Typed.Clos2 as T
open import Semantics.Graph.Typed.ISWIM
open import proof.Semantics.Graph.Typed.Ops using (project-≃)
open import proof.Semantics.Graph.Typed.Clos2 using (fv-env-nth; fv-env) renaming (⟦_⟧ to ⟦_⟧₂; ⟦_⟧s to ⟦_⟧s₂)
open import Compiler.Enclose

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc)
open import Data.Vec using (Vec; []; _∷_; tabulate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

Rel : ∀ k → Env Value → Env Value → Set
Rel k ρ ρ' = ∀ (x : Fin k) → ρ (toℕ x) ≃ ρ' (toℕ x) × nonempty (ρ' (toℕ x))

ext : ∀ {k ρ ρ' X} → nonempty X → Rel k ρ ρ' → Rel (suc k) (X • ρ) (X • ρ')
ext ne r zero = ⟨ ≃-refl , ne ⟩
ext ne r (suc x) = r x

tab-nth : ∀ {k n} (f : Fin n → T.Tm k Any) ρ i → nthD (⟦ tabulate f ⟧s₂ ρ) i ≡ ⟦ f i ⟧₂ ρ
tab-nth f ρ zero = refl
tab-nth f ρ (suc i) = tab-nth (λ j → f (suc j)) ρ i

enc : ∀ {k A} (M : Tm k A) {ρ ρ'} → Rel k ρ ρ' → ⟦ M ⟧ ρ ≃ ⟦ enclose M ⟧₂ ρ'
encs-nth : ∀ {k n} (Ms : Vec (Tm k Any) n) {ρ ρ'} → Rel k ρ ρ'
  → ∀ i → nthD (⟦ Ms ⟧s ρ) i ≃ nthD (⟦ encs Ms ⟧s₂ ρ') i

enc (` x) r = proj₁ (r x)
enc {k} (lam N) {ρ} {ρ'} r =
  ⟨ (λ w w∈ → ⟨ ne , proj₁ body w w∈ ⟩) , (λ { w ⟨ _ , w∈ ⟩ → proj₂ body w w∈ }) ⟩
  where
  Ds = ⟦ tabulate T.`_ ⟧s₂ ρ'
  fv≡ : ∀ x → fv-env k Ds (toℕ x) ≡ ρ' (toℕ x)
  fv≡ x = trans (fv-env-nth k Ds x) (tab-nth T.`_ ρ' x)
  ne = λ i → subst nonempty (sym (tab-nth T.`_ ρ' i)) (proj₂ (r i))
  body = Λ-≃ λ V neV _ → enc N (ext (E≢[]⇒nonempty-mem neV) λ x →
           ⟨ ≃-trans (proj₁ (r x)) (≃-reflexive (sym (fv≡ x))) , subst nonempty (sym (fv≡ x)) (proj₂ (r x)) ⟩)
enc (app L M) r = ⋆-≃ (enc L r) (enc M r)
enc (lit B c) r = ≃-refl
enc (tuple {n = n} Ms) r = 𝒯-≃ n (encs-nth Ms r)
enc (get i M) r = proj-≃ i (enc M r)
enc (inl M) r = inl-≃ (enc M r)
enc (inr M) r = inr-≃ (enc M r)
enc (case L M N) {ρ} {ρ'} r =
  𝒞-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ enclose M ⟧₂ (X • ρ')} {λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ enclose N ⟧₂ (X • ρ')}
    (enc L r) (λ v V _ → enc M (ext ⟨ v , here refl ⟩ r)) (λ v V _ → enc N (ext ⟨ v , here refl ⟩ r))
enc (prim p L M) r = primD-≃ p (enc L r) (enc M r)
enc (let′ M N) {ρ} {ρ'} r =
  letD-≃ {F = λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ enclose N ⟧₂ (X • ρ')} (enc M r)
    (λ V neV _ → enc N (ext (E≢[]⇒nonempty-mem neV) r))
enc (inject G M) r = enc M r
enc (project t M) r = project-≃ _ t (enc M r)

encs-nth (M ∷ Ms) r zero = enc M r
encs-nth (M ∷ Ms) r (suc i) = encs-nth Ms r i

enclose-correct : ∀ (M : Tm 0 Any) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct M = enc M (λ ())
