module proof.Compiler.Model.Graph.Sem.Clos4Iswim where

open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Compiler.Model.Graph.Prim
open import Compiler.Lang.Clos4
open import Compiler.Model.Graph.Sem.Clos4Iswim public hiding (⟦_⟧; init)

open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)

{- The semantics of Compiler/Model/Graph/Sem/Clos4Iswim.agda as an instance of
   the generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there, with the monotonicity and
   consistency of its operators. -}

𝕆-Clos4-mono : 𝕆-monotone sig 𝕆-Clos4
𝕆-Clos4-mono fun-op ⟨ F1 , _ ⟩ ⟨ F2 , _ ⟩  ⟨ F~ , _ ⟩ = 
  Λ-mono ⟨ (λ X → Λ ⟨ (F1 X) , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ (F2 X) , ptt ⟩) , ptt ⟩
         ⟨ (λ X1 X2 X~ → Λ-mono ⟨ (F1 X1) , ptt ⟩ ⟨ (F2 X2) , ptt ⟩ 
                                ⟨ (F~ X1 X2 X~) , ptt ⟩) , ptt ⟩
𝕆-Clos4-mono app ⟨ L1 , ⟨ M1 , ⟨ N1 , _ ⟩ ⟩ ⟩ 
                 ⟨ L2 , ⟨ M2 , ⟨ N2 , _ ⟩ ⟩ ⟩ ⟨ L~ , ⟨ M~ , ⟨ N~ , _ ⟩ ⟩ ⟩ = 
  ⋆-mono ⟨ ⋆ ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ , ⟨ N1 , ptt ⟩ ⟩
         ⟨ ⋆ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ , ⟨ N2 , ptt ⟩ ⟩
         ⟨ ⋆-mono ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩  ⟨ L~ , ⟨ M~ , ptt ⟩ ⟩ 
         , ⟨ N~ , ptt ⟩ ⟩
𝕆-Clos4-mono (lit B k) _ _ _ = lift (λ d d∈ → d∈)
𝕆-Clos4-mono pair-op = pair-mono
𝕆-Clos4-mono fst-op = car-mono
𝕆-Clos4-mono snd-op = cdr-mono
𝕆-Clos4-mono (tuple x) = 𝒯-mono x
𝕆-Clos4-mono (get x) = proj-mono x
𝕆-Clos4-mono inl-op = inl-mono
𝕆-Clos4-mono inr-op = inr-mono
𝕆-Clos4-mono case-op = 𝒞-mono
𝕆-Clos4-mono (prim p) = primD-mono p
𝕆-Clos4-mono let-op ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆-mono ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
         ⟨ Λ-mono ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩

𝕆-Clos4-consis : 𝕆-consistent _~_ sig 𝕆-Clos4
𝕆-Clos4-consis fun-op ⟨ F1 , _ ⟩ ⟨ F2 , _ ⟩  ⟨ F~ , _ ⟩ = 
  Λ-consis ⟨ (λ X → Λ ⟨ (F1 X) , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ (F2 X) , ptt ⟩) , ptt ⟩
         ⟨ (λ X1 X2 X~ → Λ-consis ⟨ (F1 X1) , ptt ⟩ ⟨ (F2 X2) , ptt ⟩ 
                                ⟨ (F~ X1 X2 X~) , ptt ⟩) , ptt ⟩
𝕆-Clos4-consis app ⟨ L1 , ⟨ M1 , ⟨ N1 , _ ⟩ ⟩ ⟩ 
                 ⟨ L2 , ⟨ M2 , ⟨ N2 , _ ⟩ ⟩ ⟩ ⟨ L~ , ⟨ M~ , ⟨ N~ , _ ⟩ ⟩ ⟩ = 
  ⋆-consis ⟨ ⋆ ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ , ⟨ N1 , ptt ⟩ ⟩
         ⟨ ⋆ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ , ⟨ N2 , ptt ⟩ ⟩
         ⟨ ⋆-consis ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩  ⟨ L~ , ⟨ M~ , ptt ⟩ ⟩ 
         , ⟨ N~ , ptt ⟩ ⟩
𝕆-Clos4-consis (lit B k) = ℬ-consis B k
𝕆-Clos4-consis pair-op = pair-consis
𝕆-Clos4-consis fst-op = car-consis
𝕆-Clos4-consis snd-op = cdr-consis
𝕆-Clos4-consis (tuple x) = 𝒯-consis x
𝕆-Clos4-consis (get x) = proj-consis x
𝕆-Clos4-consis inl-op = inl-consis
𝕆-Clos4-consis inr-op = inr-consis
𝕆-Clos4-consis case-op = 𝒞-consis
𝕆-Clos4-consis (prim p) = primD-consis p
𝕆-Clos4-consis let-op ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆-consis ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
           ⟨ Λ-consis ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos4-Semantics : Semantics
  Clos4-Semantics = record { interp-op = 𝕆-Clos4 ;
                                  mono-op = 𝕆-Clos4-mono ;
                                  error = ω }
open Semantics {{...}} public

{- a consistent environment gives a consistent denotation -}
Clos4-con : ∀ M {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
Clos4-con M = ⟦⟧-pres (Every _~_) 𝕆-Clos4-consis (Con-⌈⌉ ω) M
