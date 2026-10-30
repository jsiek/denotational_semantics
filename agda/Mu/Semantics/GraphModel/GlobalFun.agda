{-

  The semantics of GlobalFunμ (Mu/Language/GlobalFun.agda) in the graph model,
  as that of PairClosμ (Mu/Semantics/GraphModel/PairClos.agda), given a table T of
  the meanings of the global definitions: fun-ref f means T f. The
  definitions of a program are given meaning newest first, each with
  the table of the older ones (tables, Mu/Semantics/GraphModel/Ops.agda), and
  main with the table of all of them.

-}

module Mu.Semantics.GraphModel.GlobalFun where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD; pair to pairD)
open import Semantics.Graph.Prim using (primD)
open import Mu.Semantics.GraphModel.Ops
open import Mu.Language.Type
open import Mu.Language.GlobalFun
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (List; length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧[_] : ∀ {Σ Γ A} → Tm Σ Γ A → Table Σ → Env Value → 𝒫 Value
⟦_⟧s[_] : ∀ {Σ Γ Δ} → All (Tm Σ Γ) Δ → Table Σ → Env Value → Results (𝒫 Value) (replicate (length Δ) ■)

⟦ ` x ⟧[ T ] ρ = ρ (idx x)
⟦ fun-ref f ⟧[ T ] ρ = T f
⟦ pair L M ⟧[ T ] ρ = pairD ⟨ ⟦ L ⟧[ T ] ρ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ callc L M ⟧[ T ] ρ =
  ⋆ ⟨ ⋆ ⟨ car ⟨ ⟦ L ⟧[ T ] ρ , ptt ⟩ , ⟨ cdr ⟨ ⟦ L ⟧[ T ] ρ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ lit B c ⟧[ T ] ρ = ℬ B c ptt
⟦ tuple {Δ} Ms ⟧[ T ] ρ = 𝒯 (length Δ) (⟦ Ms ⟧s[ T ] ρ)
⟦ get i M ⟧[ T ] ρ = proj (pos i) ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ inl M ⟧[ T ] ρ = inlD ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ inr M ⟧[ T ] ρ = inrD ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ case L M N ⟧[ T ] ρ =
  𝒞 ⟨ ⟦ L ⟧[ T ] ρ , ⟨ (λ X → ⟦ M ⟧[ T ] (X • ρ)) , ⟨ (λ X → ⟦ N ⟧[ T ] (X • ρ)) , ptt ⟩ ⟩ ⟩
⟦ prim p L M ⟧[ T ] ρ = primD p ⟨ ⟦ L ⟧[ T ] ρ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ let′ M N ⟧[ T ] ρ = ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧[ T ] (X • ρ)) , ptt ⟩ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ fold M ⟧[ T ] ρ = ⟦ M ⟧[ T ] ρ
⟦ unfold M ⟧[ T ] ρ = ⟦ M ⟧[ T ] ρ

⟦ [] ⟧s[ T ] ρ = ptt
⟦ M ∷ Ms ⟧s[ T ] ρ = ⟨ ⟦ M ⟧[ T ] ρ , ⟦ Ms ⟧s[ T ] ρ ⟩

{- the function whose code is N, given the table T: it takes the tuple of
   its free variables X and then the argument Y -}
code′ : ∀ {Σ} → Table Σ → ∀ {s} → Code Σ s → 𝒫 Value
code′ T N = Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧[ T ] (Y • X • λ _ → init)) , ptt ⟩) , ptt ⟩

table : ∀ {Σ} → All (Code Σ) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : ∀ {A} → Program A → 𝒫 Value
⟦ program ds M ⟧ₚ = ⟦ M ⟧[ table ds ] (λ _ → init)
