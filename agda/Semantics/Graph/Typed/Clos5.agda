{-

  The semantics of Clos5ᵀ (Language/Typed/Clos5.agda) in the graph model,
  as that of Clos4ᵀ (Semantics/Graph/Typed/Clos4.agda), given a table T of
  the meanings of the global definitions: fun-ref f means T f. The
  definitions of a program are given meaning newest first, each with the
  table of the older ones (tables, Semantics/Graph/Typed/Ops.agda), and
  main with the table of all of them.

-}

module Semantics.Graph.Typed.Clos5 where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Framework.GraphModel.Env using (Env)
open import Semantics.Graph.Prim using (primD)
open import Semantics.Graph.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Clos5

open import Data.List using (List; replicate)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧[_] : ∀ {Σ Γ A} → Tm Σ Γ A → Table Σ → Env Value → 𝒫 Value
⟦_⟧s[_] : ∀ {Σ Γ n} → Vec (Tm Σ Γ Any) n → Table Σ → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧[ T ] ρ = ρ (idx x)
⟦ fun-ref f ⟧[ T ] ρ = T f
⟦ pack L M ⟧[ T ] ρ = pair ⟨ ⟦ L ⟧[ T ] ρ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ callc L M ⟧[ T ] ρ =
  ⋆ ⟨ ⋆ ⟨ car ⟨ ⟦ L ⟧[ T ] ρ , ptt ⟩ , ⟨ cdr ⟨ ⟦ L ⟧[ T ] ρ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ lit B c ⟧[ T ] ρ = ℬ B c ptt
⟦ tuple {n = n} Ms ⟧[ T ] ρ = 𝒯 n (⟦ Ms ⟧s[ T ] ρ)
⟦ get i M ⟧[ T ] ρ = proj i ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ inl M ⟧[ T ] ρ = inlD ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ inr M ⟧[ T ] ρ = inrD ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ case L M N ⟧[ T ] ρ =
  𝒞 ⟨ ⟦ L ⟧[ T ] ρ , ⟨ (λ X → ⟦ M ⟧[ T ] (X • ρ)) , ⟨ (λ X → ⟦ N ⟧[ T ] (X • ρ)) , ptt ⟩ ⟩ ⟩
⟦ prim p L M ⟧[ T ] ρ = primD p ⟨ ⟦ L ⟧[ T ] ρ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ let′ M N ⟧[ T ] ρ = ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧[ T ] (X • ρ)) , ptt ⟩ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ inject G M ⟧[ T ] ρ = ⟦ M ⟧[ T ] ρ
⟦ project t M ⟧[ T ] ρ = projectᵍ fun₄ t (⟦ M ⟧[ T ] ρ)

⟦ [] ⟧s[ T ] ρ = ptt
⟦ M ∷ Ms ⟧s[ T ] ρ = ⟨ ⟦ M ⟧[ T ] ρ , ⟦ Ms ⟧s[ T ] ρ ⟩

{- the function whose code is N, given the table T: it takes the tuple of
   its free variables X and then the argument Y -}
code′ : ∀ {Σ} → Table Σ → ∀ {n} → Code Σ n → 𝒫 Value
code′ T N = Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧[ T ] (Y • X • λ _ → init)) , ptt ⟩) , ptt ⟩

table : ∀ {Σ} → All (Code Σ) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds M ⟧ₚ = ⟦ M ⟧[ table ds ] (λ _ → init)
