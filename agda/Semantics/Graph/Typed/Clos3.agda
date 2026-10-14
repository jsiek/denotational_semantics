{-

  The semantics of Clos3ᵀ (Language/Typed/Clos3.agda) in the graph model,
  as that of Clos3 (Untyped/Semantics/Graph/Clos3Iswim.agda): a closure is its
  code, a closed function of the tuple of its free variables and of the
  argument, applied to that tuple; otherwise as ISWIMᵀ. Variable x is
  position idx x of the environment.

-}

module Semantics.Graph.Typed.Clos3 where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Framework.GraphModel.Env using (Env)
open import Semantics.Graph.Prim using (primD)
open import Semantics.Graph.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Clos3

open import Data.List using (replicate)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ n} → Vec (Tm Γ Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ clos {n = n} N Ms ⟧ ρ =
  ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧ (Y • X • λ _ → init)) , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 n (⟦ Ms ⟧s ρ) , ptt ⟩ ⟩
⟦ app L M ⟧ ρ = ⋆ ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ lit B c ⟧ ρ = ℬ B c ptt
⟦ tuple {n = n} Ms ⟧ ρ = 𝒯 n (⟦ Ms ⟧s ρ)
⟦ get i M ⟧ ρ = proj i ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inl M ⟧ ρ = inlD ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inr M ⟧ ρ = inrD ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ case L M N ⟧ ρ = 𝒞 ⟨ ⟦ L ⟧ ρ , ⟨ (λ X → ⟦ M ⟧ (X • ρ)) , ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩ ⟩ ⟩
⟦ prim p L M ⟧ ρ = primD p ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ let′ M N ⟧ ρ = ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ inject G M ⟧ ρ = ⟦ M ⟧ ρ
⟦ project t M ⟧ ρ = projectᵍ fun₂ t (⟦ M ⟧ ρ)

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
