module Semantics.GraphErr.Clos3 where
{-

 The semantics of Clos3 in the graph model with errors: that of
   Semantics/Graph/Clos3Iswim.agda, with the error-propagating operators
   (Framework/GraphModel/ErrorOps.agda). A closure evaluates the tuple of
   its free variables (left to right, an error if one of them is) and is
   its code, a closed function of two arguments, applied to that tuple;
   an application checks its operator before its argument, as the
   machine (Semantics/CEK/Clos3.agda) does.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorOps
open import Semantics.GraphErr.Prim
open import Language.Clos3
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

𝕆-Clos3ᵉ : DOpSig (𝒫 Value) sig
𝕆-Clos3ᵉ (clos-op n) = closᵉ n
𝕆-Clos3ᵉ app = ⋆ᵉ
𝕆-Clos3ᵉ (lit B k) = ℬ B k
𝕆-Clos3ᵉ (tuple n) = 𝒯ᵉ n
𝕆-Clos3ᵉ (get i) = projᵉ i
𝕆-Clos3ᵉ inl-op = inlᵉ
𝕆-Clos3ᵉ inr-op = inrᵉ
𝕆-Clos3ᵉ case-op = 𝒞ᵉ
𝕆-Clos3ᵉ (prim p) = primᵉ p
𝕆-Clos3ᵉ let-op = letᵉ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos3ᵉ init ρ M
