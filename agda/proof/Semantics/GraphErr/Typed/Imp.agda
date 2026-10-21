{-

  Lemmas about the semantics of Impᵀ and CFGᵀ in the graph model with
  errors (Semantics/GraphErr/Typed/{Imp,CFG}.agda): letᵗ, the binding of
  a slot, is a congruence, and is the bind of its body when the body is
  monotone and finitary (as letᵐ is, ErrorMonad); a continuation, a bind
  (K⟨_⟩), commutes with a typed case (as with 𝒞ᵐ, case-law).

-}

module proof.Semantics.GraphErr.Typed.Imp where

open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.OpsBase using (Mono₁; Finitary)
open import proof.Framework.GraphModel.Ops using (𝒞)
open import Semantics.GraphErr.Typed.Ops using (caseᵗ)
open import Semantics.GraphErr.Typed.Imp using (letᵗ)

open import Data.Maybe using (nothing; just)
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

letᵗ-≃ : ∀ {D D' F F'} → D ≃ D' → BodyEq F F' → letᵗ D F ≃ letᵗ D' F'
letᵗ-≃ {D} {D'} {F} {F'} D≃ F≃ = ≃-trans (≃-sym (letᵐ-unfold {D} {F})) (≃-trans (letᵐ-≃ D≃ F≃) (letᵐ-unfold {D'} {F'}))

letᵗ-≫= : ∀ {D G} → Mono₁ G → Con D → (Conv D → Finitary G ⌊ D ⌋) → letᵗ D G ≃ (D ≫= G)
letᵗ-≫= {D} {G} m c f = ≃-trans (≃-sym (letᵐ-unfold {D} {G})) (letᵐ-≫= m c f)

case-lawᵗ : ∀ k → KOK k → ∀ {A F₁ F₂} → Con A → Mono₁ F₁ → Mono₁ F₂
  → K⟨ k ⟩ (caseᵗ A F₁ F₂) ≃ caseᵗ A (λ X → K⟨ k ⟩ (F₁ X)) (λ X → K⟨ k ⟩ (F₂ X))
case-lawᵗ nothing _ cA m₁ m₂ = ≃-refl
case-lawᵗ (just G) ⟨ mG , fG ⟩ {A} {F₁} {F₂} cA m₁ m₂ =
  ≃-trans (≫=-assoc {A} {λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩} mG)
    (≫=-cong {A} {λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩ ≫= G}
      {λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ Y → F₁ Y ≫= G) , ⟨ (λ Y → F₂ Y ≫= G) , ptt ⟩ ⟩ ⟩}
      λ _ → 𝒞-≫= {⌊ A ⌋ ⇂ ValPayload} {F₁} {F₂} {G} (Con-⊆ cA (λ d d∈ → proj₁ (proj₁ d∈))) m₁ m₂ mG fG)
