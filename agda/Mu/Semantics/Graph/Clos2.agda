{-

  The semantics of Clos2μ (Mu/Language/Clos2.agda) in the graph model,
  as that of Clos2ᵀ (Semantics/Graph/Typed/Clos2.agda): a closure is
  strict in its free variables (guard-n) and is the function of the
  argument whose body sees the argument and the meanings of the free
  variables; otherwise as ISWIMμ (Mu/Semantics/Graph/ISWIM.agda).

-}

module Mu.Semantics.Graph.Clos2 where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Semantics.Graph.Prim using (primD)
open import Mu.Language.Type
open import Mu.Language.Clos2
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (length; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the environment of the code of a closure: its free variables -}
fv-env : ∀ n → Results (𝒫 Value) (replicate n ■) → Env Value
fv-env zero _ _ = ⌈ ⟨⟩ ⌉
fv-env (suc n) ⟨ X , Xs ⟩ zero = X
fv-env (suc n) ⟨ X , Xs ⟩ (suc i) = fv-env n Xs i

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ Δ} → All (Tm Γ) Δ → Env Value → Results (𝒫 Value) (replicate (length Δ) ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ clos {Δ} N Ms ⟧ ρ =
  guard-n (length Δ) (⟦ Ms ⟧s ρ) (Λ ⟨ (λ Y → ⟦ N ⟧ (Y • fv-env (length Δ) (⟦ Ms ⟧s ρ))) , ptt ⟩)
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
