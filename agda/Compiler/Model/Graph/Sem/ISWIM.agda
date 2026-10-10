{-# OPTIONS --safe #-}
module Compiler.Model.Graph.Sem.ISWIM where
{-

 The graph-model semantics of ISWIM. A function denotes the function of
   its argument given by its body, which sees the surrounding environment.
 This semantics is before the 'annotate' pass.

-}

open import Primitives
open import abt.ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import SetsAsPredicates
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.ISWIM

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

𝕆-ISWIM : DOpSig (𝒫 Value) sig
𝕆-ISWIM lam = Λ
𝕆-ISWIM app = ⋆
𝕆-ISWIM (lit B k) = ℬ B k
𝕆-ISWIM (tuple n) = 𝒯 n
𝕆-ISWIM (get i) = proj i
𝕆-ISWIM inl-op = ℒ
𝕆-ISWIM inr-op = ℛ
𝕆-ISWIM case-op = 𝒞

𝕆-ISWIM-mono : 𝕆-monotone sig 𝕆-ISWIM
𝕆-ISWIM-mono lam = Λ-mono
𝕆-ISWIM-mono app = ⋆-mono
𝕆-ISWIM-mono (lit B k) _ _ _ = lift (λ d z → z)
𝕆-ISWIM-mono (tuple x) = 𝒯-mono x
𝕆-ISWIM-mono (get x) = proj-mono x
𝕆-ISWIM-mono inl-op = ℒ-mono
𝕆-ISWIM-mono inr-op = ℛ-mono
𝕆-ISWIM-mono case-op = 𝒞-mono

open import abt.Fold2 Op sig
open import NewSemantics Op sig public

instance
  ISWIM-Semantics : Semantics
  ISWIM-Semantics = record { interp-op = 𝕆-ISWIM ;
                             mono-op = 𝕆-ISWIM-mono ;
                             error = ω }
open Semantics {{...}} public
