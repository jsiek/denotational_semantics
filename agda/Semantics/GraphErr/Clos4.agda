module Semantics.GraphErr.Clos4 where
{-

 The semantics of Clos4 in the graph model with errors: that of
   Semantics/Graph/Clos4Iswim.agda, with the error-propagating operators
   (Framework/GraphModel/ErrorOps.agda). A closure is a pair of code and
   environment; fst and snd are errors on a value that is not a pair; a
   call evaluates its code, environment and argument left to right and
   only then checks that the code is code (the late check), as the
   machine (Semantics/CEK/Clos4.agda) does.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorOps
open import Semantics.GraphErr.Prim
open import Language.Clos4
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

𝕆-Clos4ᵉ : DOpSig (𝒫 Value) sig
𝕆-Clos4ᵉ fun-op = ΛΛᵉ
𝕆-Clos4ᵉ app = callᵉ
𝕆-Clos4ᵉ (lit B k) = ℬ B k
𝕆-Clos4ᵉ pair-op = pairᵉ
𝕆-Clos4ᵉ fst-op = carᵉ
𝕆-Clos4ᵉ snd-op = cdrᵉ
𝕆-Clos4ᵉ (tuple n) = 𝒯ᵉ n
𝕆-Clos4ᵉ (get i) = projᵉ i
𝕆-Clos4ᵉ inl-op = inlᵉ
𝕆-Clos4ᵉ inr-op = inrᵉ
𝕆-Clos4ᵉ case-op = 𝒞ᵉ
𝕆-Clos4ᵉ (prim p) = primᵉ p
𝕆-Clos4ᵉ let-op = letᵉ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos4ᵉ init ρ M
