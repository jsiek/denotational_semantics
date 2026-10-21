{-

  The semantics of Clos4ᵀ (Language/Typed/Clos4.agda) in the graph model,
  as that of Clos4 (Untyped/Semantics/Graph/Clos4Iswim.agda): code is a closed
  function of two arguments, a closure the pair of code and environment,
  and callc applies the closure's code (car) to its environment (cdr) and
  the argument. A value of type ⟪ fun ⟫ is a pair, so project tests a
  function as a pair (fun₄).

-}

module Semantics.Graph.Typed.Clos4 where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Semantics.Graph.Prim using (primD)
open import Semantics.Graph.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Clos4

open import Data.List using (replicate)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ n} → Vec (Tm Γ Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ code N ⟧ ρ = Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧ (Y • X • λ _ → init)) , ptt ⟩) , ptt ⟩
⟦ pack L M ⟧ ρ = pair ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ callc L M ⟧ ρ = ⋆ ⟨ ⋆ ⟨ car ⟨ ⟦ L ⟧ ρ , ptt ⟩ , ⟨ cdr ⟨ ⟦ L ⟧ ρ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ lit B c ⟧ ρ = ℬ B c ptt
⟦ tuple {n = n} Ms ⟧ ρ = 𝒯 n (⟦ Ms ⟧s ρ)
⟦ get i M ⟧ ρ = proj i ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inl M ⟧ ρ = inlD ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inr M ⟧ ρ = inrD ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ case L M N ⟧ ρ = 𝒞 ⟨ ⟦ L ⟧ ρ , ⟨ (λ X → ⟦ M ⟧ (X • ρ)) , ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩ ⟩ ⟩
⟦ prim p L M ⟧ ρ = primD p ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ let′ M N ⟧ ρ = ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ inject G M ⟧ ρ = ⟦ M ⟧ ρ
⟦ project t M ⟧ ρ = projectᵍ fun₄ t (⟦ M ⟧ ρ)

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
