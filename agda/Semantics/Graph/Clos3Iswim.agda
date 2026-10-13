module Semantics.Graph.Clos3Iswim where
{-

 In this intermediate semantics all functions take two parameters,
   so application have two operands and
 This semantics is after the 'delay' pass,
   and before the 'globalize' pass.

-}

open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Semantics.Graph.Prim
open import Language.Clos3
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)

𝕆-Clos3 : DOpSig (𝒫 Value) sig
𝕆-Clos3 (clos-op n) ⟨ F , Ds ⟩ = 
  ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ 
     , ⟨ 𝒯 n Ds 
     , ptt ⟩ ⟩
𝕆-Clos3 app = ⋆
𝕆-Clos3 (lit B k) = ℬ B k
𝕆-Clos3 (tuple n) = 𝒯 n
𝕆-Clos3 (get i) = proj i
𝕆-Clos3 inl-op = inl
𝕆-Clos3 inr-op = inr
𝕆-Clos3 case-op = 𝒞
𝕆-Clos3 (prim p) = primD p

{- the meaning of a term in an environment: the operators, folded over the
   term; a variable means what the environment gives it, and a variable
   not in scope (under a clear) means {ω} -}
init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos3 init ρ M
