module Compiler.Model.Graph.Sem.Clos4Iswim where
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
open import Compiler.Model.Graph.Prim
open import Compiler.Lang.Clos4
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)


𝕆-Clos4 : DOpSig (𝒫 Value) sig
𝕆-Clos4 fun-op ⟨ F , _ ⟩ = Λ ⟨ (λ X → Λ ⟨ (λ Y → F X Y) , ptt ⟩) , ptt ⟩
𝕆-Clos4 app ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ = ⋆ ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩
𝕆-Clos4 (lit B k) = ℬ B k
𝕆-Clos4 pair-op = pair
𝕆-Clos4 fst-op = car
𝕆-Clos4 snd-op = cdr
𝕆-Clos4 (tuple x) = 𝒯 x
𝕆-Clos4 (get x) = proj x
𝕆-Clos4 inl-op = inl
𝕆-Clos4 inr-op = inr
𝕆-Clos4 case-op = 𝒞
𝕆-Clos4 (prim p) = primD p
{- let x = M in N means (λx. N) M -}
𝕆-Clos4 let-op ⟨ D , ⟨ F , _ ⟩ ⟩ = ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

{- the meaning of a term in an environment: the operators, folded over the
   term; a variable means what the environment gives it, and a variable
   not in scope (under a clear) means {ω} -}
init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos4 init ρ M
