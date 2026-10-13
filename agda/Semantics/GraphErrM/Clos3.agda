module Semantics.GraphErrM.Clos3 where
{-

 The semantics of Clos3 in the monadic graph model with errors (a pilot): that of
   Semantics/Graph/Clos3Iswim.agda, with the error-propagating operators
   (Framework/GraphModel/ErrorMonad.agda). A closure evaluates the tuple of
   its free variables (left to right, an error if one of them is) and is
   its code, a closed function of two arguments, applied to that tuple;
   an application checks its operator before its argument, as the
   machine (Semantics/CEK/Clos3.agda) does.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErrM.Prim
open import Language.Clos3
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

𝕆-Clos3ᵐ : DOpSig (𝒫 Value) sig
𝕆-Clos3ᵐ (clos-op n) = closᵐ n
𝕆-Clos3ᵐ app = ⋆ᵐ
𝕆-Clos3ᵐ (lit B k) = ℬ B k
𝕆-Clos3ᵐ (tuple n) = 𝒯ᵐ n
𝕆-Clos3ᵐ (get i) = projᵐ i
𝕆-Clos3ᵐ inl-op = inlᵐ
𝕆-Clos3ᵐ inr-op = inrᵐ
𝕆-Clos3ᵐ case-op = 𝒞ᵐ
𝕆-Clos3ᵐ (prim p) = primᵐ p
𝕆-Clos3ᵐ let-op = letᵐ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos3ᵐ init ρ M
