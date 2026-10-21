{-

  The semantics of ISWIMμ (Mu/Language/ISWIM.agda) in the graph model,
  as that of ISWIMᵀ (Semantics/Graph/Typed/ISWIM.agda): fold and unfold
  are the identity (a value of a recursive type is a value of its
  unfolding), and there is no project. Recursion needs no fixed point:
  self-application, through a recursive type, gives it, as in untyped
  ISWIM. Variable x is position idx x of the environment; component i
  of a tuple is its position pos i.

-}

module Mu.Semantics.Graph.ISWIM where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Semantics.Graph.Prim using (primD)
open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ Δ} → All (Tm Γ) Δ → Env Value → Results (𝒫 Value) (replicate (length Δ) ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ lam N ⟧ ρ = Λ ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩
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
