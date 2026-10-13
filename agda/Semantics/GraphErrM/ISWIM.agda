module Semantics.GraphErrM.ISWIM where
{-

 The semantics of ISWIM in the monadic graph model with errors (a
   pilot): the graph model's operators (Semantics/Graph/ISWIM.agda) as
   kernels under the error monad (Framework/GraphModel/ErrorMonad.agda).
   A program that stops with an error denotes a set that holds ω; one
   that diverges, the empty set. Evaluation order is that of the machine
   (Semantics/CEK/ISWIM.agda): the nesting of the binds.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErrM.Prim
open import Language.ISWIM
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

𝕆-ISWIMᵐ : DOpSig (𝒫 Value) sig
𝕆-ISWIMᵐ lam = Λᵐ
𝕆-ISWIMᵐ app = ⋆ᵐ
𝕆-ISWIMᵐ (lit B k) = ℬ B k
𝕆-ISWIMᵐ (tuple n) = 𝒯ᵐ n
𝕆-ISWIMᵐ (get i) = projᵐ i
𝕆-ISWIMᵐ inl-op = inlᵐ
𝕆-ISWIMᵐ inr-op = inrᵐ
𝕆-ISWIMᵐ case-op = 𝒞ᵐ
𝕆-ISWIMᵐ (prim p) = primᵐ p
{- let x = M in N means (λx. N) M -}
𝕆-ISWIMᵐ let-op = letᵐ

{- a variable not in scope means {ω}, an error -}
init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-ISWIMᵐ init ρ M
