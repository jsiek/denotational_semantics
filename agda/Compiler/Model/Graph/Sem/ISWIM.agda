module Compiler.Model.Graph.Sem.ISWIM where
{-

 The graph-model semantics of ISWIM. A function denotes the function of
   its argument given by its body, which sees the surrounding environment.
 This semantics is before the 'enclose' pass.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Compiler.Model.Graph.Prim
open import Compiler.Lang.ISWIM
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)


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

{- the meaning of a term in an environment: the operators, folded over the
   term; a variable means what the environment gives it, and a variable
   not in scope (under a clear) means {ω} -}
init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-ISWIM init ρ M
