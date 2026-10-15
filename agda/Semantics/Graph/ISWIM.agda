module Semantics.Graph.ISWIM where
{-

 The graph-model semantics of ISWIM. A function denotes the function of
   its argument given by its body, which sees the surrounding environment.
 This semantics is before the 'enclose' pass.

-}

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops
open import Semantics.Graph.Prim
open import Language.ISWIM
open import Framework.abt.Fold2 Op sig using (fold)

open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)


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
{- let x = M in N means (λx. N) M -}
𝕆-ISWIM let-op ⟨ D , ⟨ F , _ ⟩ ⟩ = ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

{- the meaning of a term in an environment: the operators, folded over the
   term; a variable means what the environment gives it, and a variable
   not in scope (under a clear) means {ω} -}
init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-ISWIM init ρ M
