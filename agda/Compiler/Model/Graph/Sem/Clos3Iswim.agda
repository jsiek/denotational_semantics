module Compiler.Model.Graph.Sem.Clos3Iswim where
{-

 In this intermediate semantics all functions take two parameters,
   so application have two operands and
 This semantics is after the 'delay' pass,
   and before the 'globalize' pass.

-}

open import NewDOpSig
open import SetsAsPredicates
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3

open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)

𝕆-Clos3 : DOpSig (𝒫 Value) sig
𝕆-Clos3 (clos-op n) ⟨ F , Ds ⟩ = 
  ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ 
     , ⟨ 𝒯 n Ds 
     , ptt ⟩ ⟩
𝕆-Clos3 app = ⋆
𝕆-Clos3 (lit B k) = ℬ B k
𝕆-Clos3 (tuple n) = 𝒯 n
𝕆-Clos3 (get i) = proj i
𝕆-Clos3 inl-op = inl
𝕆-Clos3 inr-op = inr
𝕆-Clos3 case-op = 𝒞
𝕆-Clos3 (prim p) = primD p

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


open import NewSemantics Op sig public

instance
  Clos3-Semantics : Semantics
  Clos3-Semantics = record { interp-op = 𝕆-Clos3 ;
                             mono-op = 𝕆-Clos3-mono ;
                             error = ω }
open Semantics {{...}} public
