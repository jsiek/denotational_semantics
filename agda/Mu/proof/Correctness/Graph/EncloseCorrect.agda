{-

  Correctness of enclose (ISWIMμ → Clos2μ) in the graph model
  (Mu/Semantics/Graph/{ISWIM,Clos2}.agda), as for typed enclose
  (proof/Correctness/Graph/EncloseCorrect.agda).

  ⟦ M ⟧ ρ ≃ ⟦ enclose M ⟧₂ ρ' when the environments agree on the
  variables in scope and ρ' is nonempty there (Rel). Every case but the
  function is a congruence (fold and unfold are the identity). A
  function becomes a closure that captures all variables of its
  context: they are nonempty, so its guard holds, and the code's
  environment fv-env agrees with ρ' on them.

-}

module Mu.proof.Correctness.Graph.EncloseCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Mu.Language.Type
open import Mu.Language.ISWIM
import Mu.Language.Clos2 as T
open import Mu.Semantics.Graph.ISWIM
open import Mu.proof.Semantics.Graph.Clos2 using (fv-env) renaming (⟦_⟧ to ⟦_⟧₂; ⟦_⟧s to ⟦_⟧s₂)
open import Mu.Framework.AllUtil using (All; []; _∷_; tab; pos)
open import Mu.Compiler.Enclose

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

Rel : Ctx → Env Value → Env Value → Set
Rel Γ ρ ρ' = ∀ {C} (x : Γ ∋ C) → ρ (idx x) ≃ ρ' (idx x) × nonempty (ρ' (idx x))

ext : ∀ {Γ A ρ ρ' X} → nonempty X → Rel Γ ρ ρ' → Rel (A ∷ Γ) (X • ρ) (X • ρ')
ext ne r Z = ⟨ ≃-refl , ne ⟩
ext ne r (S x) = r x

{- the free variables of a closure built by tab -}
tab-fv : ∀ {Γ Δ C} (f : ∀ {A} → Δ ∋ A → T.Tm Γ A) ρ (x : Δ ∋ C)
  → fv-env (length Δ) (⟦ tab f ⟧s₂ ρ) (idx x) ≡ ⟦ f x ⟧₂ ρ
tab-fv f ρ Z = refl
tab-fv f ρ (S x) = tab-fv (λ y → f (S y)) ρ x

tab-ne : ∀ {Γ Δ} (f : ∀ {A} → Δ ∋ A → T.Tm Γ A) ρ → (∀ {A} (x : Δ ∋ A) → nonempty (⟦ f x ⟧₂ ρ))
  → ∀ i → nonempty (nthD (⟦ tab f ⟧s₂ ρ) i)
tab-ne {Δ = A ∷ Δ} f ρ ne zero = ne Z
tab-ne {Δ = A ∷ Δ} f ρ ne (suc i) = tab-ne (λ y → f (S y)) ρ (λ x → ne (S x)) i

enc : ∀ {Γ A} (M : Tm Γ A) {ρ ρ'} → Rel Γ ρ ρ' → ⟦ M ⟧ ρ ≃ ⟦ enclose M ⟧₂ ρ'
encs-nth : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ ρ'} → Rel Γ ρ ρ'
  → ∀ i → nthD (⟦ Ms ⟧s ρ) i ≃ nthD (⟦ encs Ms ⟧s₂ ρ') i

enc (` x) r = proj₁ (r x)
enc {Γ} (lam N) {ρ} {ρ'} r =
  ⟨ (λ w w∈ → ⟨ ne , proj₁ body w w∈ ⟩) , (λ { w ⟨ _ , w∈ ⟩ → proj₂ body w w∈ }) ⟩
  where
  ne = tab-ne T.`_ ρ' (λ x → proj₂ (r x))
  body = Λ-≃ λ V neV _ → enc N (ext (E≢[]⇒nonempty-mem neV) λ x →
           ⟨ ≃-trans (proj₁ (r x)) (≃-reflexive (sym (tab-fv T.`_ ρ' x))) , subst nonempty (sym (tab-fv T.`_ ρ' x)) (proj₂ (r x)) ⟩)
enc (app L M) r = ⋆-≃ (enc L r) (enc M r)
enc (lit B c) r = ≃-refl
enc (tuple {Δ} Ms) r = 𝒯-≃ (length Δ) (encs-nth Ms r)
enc (get i M) r = proj-≃ (pos i) (enc M r)
enc (inl M) r = inl-≃ (enc M r)
enc (inr M) r = inr-≃ (enc M r)
enc (case L M N) {ρ} {ρ'} r =
  𝒞-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ enclose M ⟧₂ (X • ρ')} {λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ enclose N ⟧₂ (X • ρ')}
    (enc L r) (λ v V _ → enc M (ext ⟨ v , here refl ⟩ r)) (λ v V _ → enc N (ext ⟨ v , here refl ⟩ r))
enc (prim p L M) r = primD-≃ p (enc L r) (enc M r)
enc (let′ M N) {ρ} {ρ'} r =
  letD-≃ {F = λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ enclose N ⟧₂ (X • ρ')} (enc M r)
    (λ V neV _ → enc N (ext (E≢[]⇒nonempty-mem neV) r))
enc (fold M) r = enc M r
enc (unfold M) r = enc M r

encs-nth (M ∷ Ms) r zero = enc M r
encs-nth (M ∷ Ms) r (suc i) = encs-nth Ms r i

enclose-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct M = enc M (λ ())
