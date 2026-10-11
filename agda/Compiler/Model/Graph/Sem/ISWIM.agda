module Compiler.Model.Graph.Sem.ISWIM where
{-

 The graph-model semantics of ISWIM. A function denotes the function of
   its argument given by its body, which sees the surrounding environment.
 This semantics is before the 'enclose' pass.

-}

open import NewDOpSig
open import SetsAsPredicates
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.ISWIM

open import Level renaming (zero to lzero; suc to lsuc)

𝕆-ISWIM : DOpSig (𝒫 Value) sig
𝕆-ISWIM lam = Λ
𝕆-ISWIM app = ⋆
𝕆-ISWIM (lit B k) = ℬ B k
𝕆-ISWIM (tuple n) = 𝒯 n
𝕆-ISWIM (get i) = proj i
𝕆-ISWIM inl-op = inl
𝕆-ISWIM inr-op = inr
𝕆-ISWIM case-op = 𝒞
𝕆-ISWIM (prim p) = primD p

𝕆-ISWIM-mono : 𝕆-monotone sig 𝕆-ISWIM
𝕆-ISWIM-mono lam = Λ-mono
𝕆-ISWIM-mono app = ⋆-mono
𝕆-ISWIM-mono (lit B k) _ _ _ = lift (λ d z → z)
𝕆-ISWIM-mono (tuple x) = 𝒯-mono x
𝕆-ISWIM-mono (get x) = proj-mono x
𝕆-ISWIM-mono inl-op = inl-mono
𝕆-ISWIM-mono inr-op = inr-mono
𝕆-ISWIM-mono case-op = 𝒞-mono
𝕆-ISWIM-mono (prim p) = primD-mono p

open import NewSemantics Op sig public

instance
  ISWIM-Semantics : Semantics
  ISWIM-Semantics = record { interp-op = 𝕆-ISWIM ;
                             mono-op = 𝕆-ISWIM-mono ;
                             error = ω }
open Semantics {{...}} public
