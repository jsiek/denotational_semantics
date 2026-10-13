module proof.Semantics.Graph.Clos3Iswim where

open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Language.Clos3
open import Semantics.Graph.Clos3Iswim public hiding (⟦_⟧; init)

open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)

{- The semantics of Semantics/Graph/Clos3Iswim.agda as an instance of
   the generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there, with the monotonicity and
   consistency of its operators. -}

𝕆-Clos3-mono : 𝕆-monotone sig 𝕆-Clos3
𝕆-Clos3-mono (clos-op x) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ = 
    ⋆-mono ⟨ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 x Ds , ptt ⟩ ⟩ 
            ⟨ Λ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 x Ds' , ptt ⟩ ⟩ 
            ⟨ Λ-mono ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ 
                     ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩ 
                     ⟨ (λ D D' D⊆ → Λ-mono ⟨ F D , ptt ⟩ 
                                           ⟨ F' D' , ptt ⟩ 
                                           ⟨ F~ D D' D⊆ , ptt ⟩) , ptt ⟩ 
            , ⟨ 𝒯-mono x Ds Ds' Ds~ , ptt ⟩ ⟩
𝕆-Clos3-mono app = ⋆-mono
𝕆-Clos3-mono (lit B k) _ _ _ = lift (λ d z → z)
𝕆-Clos3-mono (tuple x) = 𝒯-mono x
𝕆-Clos3-mono (get x) = proj-mono x
𝕆-Clos3-mono inl-op = inl-mono
𝕆-Clos3-mono inr-op = inr-mono
𝕆-Clos3-mono case-op = 𝒞-mono
𝕆-Clos3-mono (prim p) = primD-mono p
𝕆-Clos3-mono let-op ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆-mono ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
         ⟨ Λ-mono ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩

𝕆-Clos3-consis : 𝕆-consistent _~_ sig 𝕆-Clos3
𝕆-Clos3-consis (clos-op x) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ =
    ⋆-consis ⟨ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 x Ds , ptt ⟩ ⟩
            ⟨ Λ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 x Ds' , ptt ⟩ ⟩
            ⟨ Λ-consis ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩
                ⟨ (λ D D' D~ → Λ-consis ⟨ F D , ptt ⟩ ⟨ F' D' , ptt ⟩ ⟨ F~ D D' D~ , ptt ⟩) , ptt ⟩
            , ⟨ 𝒯-consis x Ds Ds' Ds~ , ptt ⟩ ⟩
𝕆-Clos3-consis app = ⋆-consis
𝕆-Clos3-consis (lit B k) = ℬ-consis B k
𝕆-Clos3-consis (tuple x) = 𝒯-consis x
𝕆-Clos3-consis (get x) = proj-consis x
𝕆-Clos3-consis inl-op = inl-consis
𝕆-Clos3-consis inr-op = inr-consis
𝕆-Clos3-consis case-op = 𝒞-consis
𝕆-Clos3-consis (prim p) = primD-consis p
𝕆-Clos3-consis let-op ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆-consis ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
           ⟨ Λ-consis ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos3-Semantics : Semantics
  Clos3-Semantics = record { interp-op = 𝕆-Clos3 ;
                             mono-op = 𝕆-Clos3-mono ;
                             error = ω }
open Semantics {{...}} public

{- a consistent environment gives a consistent denotation -}
Clos3-con : ∀ M {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
Clos3-con M = ⟦⟧-pres (Every _~_) 𝕆-Clos3-consis (Con-⌈⌉ ω) M
