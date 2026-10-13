module Semantics.GraphErr.ISWIM where
{-

 The semantics of ISWIM in the graph model with errors: the graph model
   of Semantics/Graph/ISWIM.agda, with the error-propagating operators
   (Framework/GraphModel/ErrorOps.agda). A program that stops with an
   error denotes a set that holds ω; one that diverges, the empty set.
 Evaluation order is that of the machine (Semantics/CEK/ISWIM.agda):
   left to right, and an application checks its operator before it
   evaluates its argument.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorOps
open import Semantics.GraphErr.Prim
open import Language.ISWIM
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

𝕆-ISWIMᵉ : DOpSig (𝒫 Value) sig
𝕆-ISWIMᵉ lam = Λᵉ
𝕆-ISWIMᵉ app = ⋆ᵉ
𝕆-ISWIMᵉ (lit B k) = ℬ B k
𝕆-ISWIMᵉ (tuple n) = 𝒯ᵉ n
𝕆-ISWIMᵉ (get i) = projᵉ i
𝕆-ISWIMᵉ inl-op = inlᵉ
𝕆-ISWIMᵉ inr-op = inrᵉ
𝕆-ISWIMᵉ case-op = 𝒞ᵉ
𝕆-ISWIMᵉ (prim p) = primᵉ p
{- let x = M in N means (λx. N) M -}
𝕆-ISWIMᵉ let-op = letᵉ

{- the meaning of a term in an environment: the operators, folded over
   the term; a variable not in scope (under a clear) means {ω}, an error,
   as a free variable is in the machine -}
init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-ISWIMᵉ init ρ M
