{-

  The semantics of Clos3μ (Mu/Language/Clos3.agda) in the graph model,
  as that of Clos3ᵀ (Semantics/Graph/Typed/Clos3.agda): a closure is its
  code, a closed function of the tuple of its free variables and of the
  argument, applied to that tuple; fold and unfold are the identity.

-}

module Mu.Semantics.Graph.Clos3 where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Semantics.Graph.Prim using (primD)
open import Mu.Language.Type
open import Mu.Language.Clos3
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ Δ} → All (Tm Γ) Δ → Env Value → Results (𝒫 Value) (replicate (length Δ) ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ clos {Δ} N Ms ⟧ ρ =
  ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧ (Y • X • λ _ → ⌈ ⟨⟩ ⌉)) , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 (length Δ) (⟦ Ms ⟧s ρ) , ptt ⟩ ⟩
⟦ app L M ⟧ ρ = ⋆ ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ lit B c ⟧ ρ = ℬ B c ptt
⟦ tuple {Δ} Ms ⟧ ρ = 𝒯 (length Δ) (⟦ Ms ⟧s ρ)
⟦ get i M ⟧ ρ = proj (pos i) ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inl M ⟧ ρ = inlD ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inr M ⟧ ρ = inrD ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ case L M N ⟧ ρ = 𝒞 ⟨ ⟦ L ⟧ ρ , ⟨ (λ X → ⟦ M ⟧ (X • ρ)) , ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩ ⟩ ⟩
⟦ prim p L M ⟧ ρ = primD p ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ let′ M N ⟧ ρ = ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ fold M ⟧ ρ = ⟦ M ⟧ ρ
⟦ unfold M ⟧ ρ = ⟦ M ⟧ ρ

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
