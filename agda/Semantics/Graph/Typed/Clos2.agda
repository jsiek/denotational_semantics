{-

  The semantics of Clos2ᵀ (Language/Typed/Clos2.agda) in the graph model,
  as that of Clos2 (Semantics/Graph/Clos2Iswim.agda): a closure is strict
  in its free variables (guard-n) and is the function of the argument
  whose body sees the argument and the meanings of the free variables;
  otherwise as ISWIMᵀ (Semantics/Graph/Typed/ISWIM.agda).

-}

module Semantics.Graph.Typed.Clos2 where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Framework.GraphModel.Env using (Env)
open import Semantics.Graph.Prim using (primD)
open import Semantics.Graph.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Clos2

open import Data.Fin using (toℕ)
open import Data.List using (replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the environment of the code of a closure: its free variables -}
fv-env : ∀ n → Results (𝒫 Value) (replicate n ■) → Env Value
fv-env zero _ _ = init
fv-env (suc n) ⟨ X , Xs ⟩ zero = X
fv-env (suc n) ⟨ X , Xs ⟩ (suc i) = fv-env n Xs i

⟦_⟧ : ∀ {k A} → Tm k A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {k n} → Vec (Tm k Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (toℕ x)
⟦ clos {n = n} N Ms ⟧ ρ = guard-n n (⟦ Ms ⟧s ρ) (Λ ⟨ (λ Y → ⟦ N ⟧ (Y • fv-env n (⟦ Ms ⟧s ρ))) , ptt ⟩)
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
