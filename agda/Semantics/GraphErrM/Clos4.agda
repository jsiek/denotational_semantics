module Semantics.GraphErrM.Clos4 where
{-

 The semantics of Clos4 in the monadic graph model with errors (a pilot): that of
   Semantics/Graph/Clos4Iswim.agda, with the error-propagating operators
   (Framework/GraphModel/ErrorMonad.agda). A closure is a pair of code and
   environment; fst and snd are errors on a value that is not a pair; a
   call evaluates its code, environment and argument left to right and
   only then checks that the code is code (the late check), as the
   machine (Semantics/CEK/Clos4.agda) does.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErrM.Prim
open import Language.Clos4
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

𝕆-Clos4ᵐ : DOpSig (𝒫 Value) sig
𝕆-Clos4ᵐ fun-op = ΛΛᵐ
𝕆-Clos4ᵐ app = callᵐ
𝕆-Clos4ᵐ (lit B k) = ℬ B k
𝕆-Clos4ᵐ pair-op = pairᵐ
𝕆-Clos4ᵐ fst-op = carᵐ
𝕆-Clos4ᵐ snd-op = cdrᵐ
𝕆-Clos4ᵐ (tuple n) = 𝒯ᵐ n
𝕆-Clos4ᵐ (get i) = projᵐ i
𝕆-Clos4ᵐ inl-op = inlᵐ
𝕆-Clos4ᵐ inr-op = inrᵐ
𝕆-Clos4ᵐ case-op = 𝒞ᵐ
𝕆-Clos4ᵐ (prim p) = primᵐ p
𝕆-Clos4ᵐ let-op = letᵐ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos4ᵐ init ρ M
