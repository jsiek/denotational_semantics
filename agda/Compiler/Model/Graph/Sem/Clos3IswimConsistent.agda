{-# OPTIONS --safe #-}

module Compiler.Model.Graph.Sem.Clos3IswimConsistent where
{-

 Consistency of the Clos3 operators.

-}

open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3
open import Compiler.Model.Graph.Sem.Clos3Iswim

open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

𝕆-Clos3-consis : 𝕆-consistent _~_ sig 𝕆-Clos3
{- a closure applies its code to the tuple of its free variables -}
𝕆-Clos3-consis (clos-op n) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ =
  ⋆-consis ⟨ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 n Ds , ptt ⟩ ⟩
           ⟨ Λ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 n Ds' , ptt ⟩ ⟩
           ⟨ Λ-consis ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩
                      ⟨ (λ X X' X~ → Λ-consis ⟨ F X , ptt ⟩ ⟨ F' X' , ptt ⟩
                                               ⟨ F~ X X' X~ , ptt ⟩) , ptt ⟩
           , ⟨ 𝒯-consis n Ds Ds' Ds~ , ptt ⟩ ⟩
𝕆-Clos3-consis app = ⋆-consis
𝕆-Clos3-consis (lit B k) = ℬ-consis B k
𝕆-Clos3-consis (tuple x) = 𝒯-consis x
𝕆-Clos3-consis (get x) = proj-consis x
𝕆-Clos3-consis inl-op = ℒ-consis
𝕆-Clos3-consis inr-op = ℛ-consis
𝕆-Clos3-consis case-op = 𝒞-consis
