{-

  The guard (Framework/GraphModel/TypedGuard.agda) is Good: monotone,
  consistent (its result is part of its operand) and continuous (an
  element and the witness come from one finite approximation).

-}

module proof.Framework.GraphModel.TypedGuard where

open import Framework.GraphModel.TypedGuard public

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ContinuityBase

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (refl)

guardᵖ-good : ∀ P → Good ⊤ (■ ∷ []) (λ Ds → guardᵖ P (proj₁ Ds))
guardᵖ-good P = mk-good
  (λ { _ _ ⟨ lift D⊆ , _ ⟩ → lift λ { w ⟨ ⟨ d , ⟨ d∈ , p ⟩ ⟩ , w∈ ⟩ → ⟨ ⟨ d , ⟨ D⊆ d d∈ , p ⟩ ⟩ , D⊆ w w∈ ⟩ } })
  (λ { _ _ ⟨ lift D~ , _ ⟩ → lift λ u w u∈ w∈ → D~ u w (proj₂ u∈) (proj₂ w∈) })
  (λ { ⟨ E , _ ⟩ NE ⟨ ⟨ m , c ⟩ , _ ⟩ w ⟨ ⟨ d , ⟨ d∈ , p ⟩ ⟩ , w∈ ⟩ →
    let ⟨ a , V⊆ ⟩ = many E NE m c (d ∷ w ∷ []) (λ { _ (here refl) → d∈ ; _ (there (here refl)) → w∈ })
    in done (λ ρ → guardᵖ P (E ρ)) a w ⟨ ⟨ d , ⟨ V⊆ d (here refl) , p ⟩ ⟩ , V⊆ w (there (here refl)) ⟩ })

guardᵖ-≃ : ∀ P {D D'} → D ≃ D' → guardᵖ P D ≃ guardᵖ P D'
guardᵖ-≃ P D≃ = mono-≃ (mono (guardᵖ-good P)) ⟨ lift D≃ , ptt ⟩
