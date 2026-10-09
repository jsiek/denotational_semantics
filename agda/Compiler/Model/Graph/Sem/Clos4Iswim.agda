module Compiler.Model.Graph.Sem.Clos4Iswim where
{-

 In this intermediate semantics all functions take two parameters,
   so application have two operands and
 This semantics is after the 'delay' pass,
   and before the 'globalize' pass.

-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos4

open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning


𝕆-Clos4 : DOpSig (𝒫 Value) sig
𝕆-Clos4 fun-op ⟨ F , _ ⟩ = Λ ⟨ (λ X → Λ ⟨ (λ Y → F X Y) , ptt ⟩) , ptt ⟩
𝕆-Clos4 app ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ = ⋆ ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩
𝕆-Clos4 (lit B k) = ℬ B k
𝕆-Clos4 pair-op = pair
𝕆-Clos4 fst-op = car
𝕆-Clos4 snd-op = cdr
𝕆-Clos4 (tuple x) = 𝒯 x
𝕆-Clos4 (get x) = proj x
𝕆-Clos4 inl-op = ℒ
𝕆-Clos4 inr-op = ℛ
𝕆-Clos4 case-op = 𝒞

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
𝕆-Clos4-mono inl-op = ℒ-mono
𝕆-Clos4-mono inr-op = ℛ-mono
𝕆-Clos4-mono case-op = 𝒞-mono

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
𝕆-Clos4-consis inl-op = ℒ-consis
𝕆-Clos4-consis inr-op = ℛ-consis
𝕆-Clos4-consis case-op = 𝒞-consis

open import Fold2 Op sig
open import NewSemantics Op sig public

instance
  Clos4-Semantics : Semantics
  Clos4-Semantics = record { interp-op = 𝕆-Clos4 ;
                                  mono-op = 𝕆-Clos4-mono ;
                                  error = ω }
open Semantics {{...}} public
