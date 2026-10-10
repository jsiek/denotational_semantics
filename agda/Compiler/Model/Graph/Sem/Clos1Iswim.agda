{-# OPTIONS --safe #-}
module Compiler.Model.Graph.Sem.Clos1Iswim where
{-

 In this intermediate semantics a closure's body sees the surrounding
   environment directly, so a closure denotes the function of its argument
   given by its body. Like tuples, closures are strict: a closure has no
   values unless each of its listed free variables has one.
 This semantics is after the 'annotate' pass,
   and before the 'enclose' pass.

-}

open import Primitives
open import abt.ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import SetsAsPredicates
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos1

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

𝕆-Clos1 : DOpSig (𝒫 Value) sig
𝕆-Clos1 (clos-op n) ⟨ F , Ds ⟩ = guard-n n Ds (Λ ⟨ F , ptt ⟩)
𝕆-Clos1 app = ⋆
𝕆-Clos1 (lit B k) = ℬ B k
𝕆-Clos1 (tuple n) = 𝒯 n
𝕆-Clos1 (get i) = proj i
𝕆-Clos1 inl-op = ℒ
𝕆-Clos1 inr-op = ℛ
𝕆-Clos1 case-op = 𝒞

𝕆-Clos1-mono : 𝕆-monotone sig 𝕆-Clos1
𝕆-Clos1-mono (clos-op n) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ = lift G
  where
  Λ⊆ = lower (Λ-mono ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩)
  G : guard-n n Ds (Λ ⟨ F , ptt ⟩) ⊆ guard-n n Ds' (Λ ⟨ F' , ptt ⟩)
  G w ⟨ ne , w∈ ⟩ =
    ⟨ (λ i → ⟨ proj₁ (ne i) , nthD-mono Ds Ds' Ds~ i _ (proj₂ (ne i)) ⟩) , Λ⊆ w w∈ ⟩
𝕆-Clos1-mono app = ⋆-mono
𝕆-Clos1-mono (lit B k) _ _ _ = lift (λ d z → z)
𝕆-Clos1-mono (tuple x) = 𝒯-mono x
𝕆-Clos1-mono (get x) = proj-mono x
𝕆-Clos1-mono inl-op = ℒ-mono
𝕆-Clos1-mono inr-op = ℛ-mono
𝕆-Clos1-mono case-op = 𝒞-mono

open import abt.Fold2 Op sig
open import NewSemantics Op sig public

instance
  Clos1-Semantics : Semantics
  Clos1-Semantics = record { interp-op = 𝕆-Clos1 ;
                             mono-op = 𝕆-Clos1-mono ;
                             error = ω }
open Semantics {{...}} public
