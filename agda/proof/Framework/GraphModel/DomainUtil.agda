{-

  Facts about the graph model's operators and finite sets of values:
  finite witnesses of cdr, and the empty tuple; with the facts about
  values for any graph-model semantics (DomainUtilBase.agda).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (refl)

module proof.Framework.GraphModel.DomainUtil where

open import proof.Framework.GraphModel.DomainUtilBase public

{- finitely many elements of L whose cdrs cover the list FV -}
cdr-witness : ∀ {L} FV → mem FV ⊆ cdr ⟨ L , ptt ⟩
  → Σ[ P ∈ List Value ] mem P ⊆ L × mem FV ⊆ cdr ⟨ mem P , ptt ⟩
cdr-witness [] _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
cdr-witness (fv ∷ FV) FV⊆ with FV⊆ fv (here refl) | cdr-witness FV (λ d d∈ → FV⊆ d (there d∈))
... | ⟨ u , u∈ ⟩ | ⟨ P , ⟨ P⊆ , FV⊆P ⟩ ⟩ = ⟨ ⦅ u , fv ⦆ ∷ P , ⟨ P⊆′ , FV⊆′ ⟩ ⟩
  where
  P⊆′ : mem (⦅ u , fv ⦆ ∷ P) ⊆ _
  P⊆′ _ (here refl) = u∈
  P⊆′ d (there d∈) = P⊆ d d∈
  FV⊆′ : mem (fv ∷ FV) ⊆ cdr ⟨ mem (⦅ u , fv ⦆ ∷ P) , ptt ⟩
  FV⊆′ _ (here refl) = ⟨ u , here refl ⟩
  FV⊆′ d (there d∈) = let ⟨ u′ , i ⟩ = FV⊆P d d∈ in ⟨ u′ , there i ⟩

{- the empty tuple has only the observation ⟨⟩, whatever its operands -}
𝒯0-flat : ∀ {Ds Es} v → v ∈ 𝒯 0 Ds → v ∈ 𝒯 0 Es × Flat v
𝒯0-flat ⟨⟩ tt = ⟨ tt , flat-⟨⟩ ⟩

