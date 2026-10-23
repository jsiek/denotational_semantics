{-

  The semantics of FlatClosμ (Mu/Language/FlatClos.agda) in the graph model,
  as that of Clos4ᵀ (Semantics/Graph/Typed/Clos4.agda): code is a closed
  function of two arguments, a closure the pair of code and
  environment, and callc applies the closure's code (car) to its
  environment (cdr) and the argument; fold and unfold are the identity.

-}

module Mu.Semantics.GraphModel.FlatClos where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Semantics.Graph.Prim using (primD)
open import Mu.Language.Type
open import Mu.Language.FlatClos
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ Δ} → All (Tm Γ) Δ → Env Value → Results (𝒫 Value) (replicate (length Δ) ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ code N ⟧ ρ = Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧ (Y • X • λ _ → ⌈ ⟨⟩ ⌉)) , ptt ⟩) , ptt ⟩
⟦ pack L M ⟧ ρ = pair ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ callc L M ⟧ ρ = ⋆ ⟨ ⋆ ⟨ car ⟨ ⟦ L ⟧ ρ , ptt ⟩ , ⟨ cdr ⟨ ⟦ L ⟧ ρ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
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
