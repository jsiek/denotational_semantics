module Semantics.GraphErr.Clos2 where
{-

 The semantics of Clos2 in the graph model with errors: that of
   Semantics/Graph/Clos2Iswim.agda, with the error-propagating operators
   (Framework/GraphModel/ErrorOps.agda). A closure evaluates its free
   variables left to right (as the machine, Semantics/CEK/Clos2.agda,
   does): it is an error if one of them is, and otherwise binds them
   like a nested let; its body is applied directly to their
   denotations, and the result is a function of the argument.

-}

open import Framework.Syntax.SigUtil
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorOps
open import Semantics.GraphErr.Prim
open import Language.Clos2
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- apply a curried function of n sets to the denotations of the free variables -}
apply-n : ∀ n {b} → Result (𝒫 Value) (ν-n n b) → Results (𝒫 Value) (replicate n ■)
  → Result (𝒫 Value) b
apply-n zero F _ = F
apply-n (suc n) F ⟨ D , Ds ⟩ = apply-n n (F D) Ds

𝕆-Clos2ᵉ : DOpSig (𝒫 Value) sig
𝕆-Clos2ᵉ (clos-op n) ⟨ F , Ds ⟩ = guardᵉ-n n Ds (Λᵉ ⟨ apply-n n F Ds , ptt ⟩)
𝕆-Clos2ᵉ app = ⋆ᵉ
𝕆-Clos2ᵉ (lit B k) = ℬ B k
𝕆-Clos2ᵉ (tuple n) = 𝒯ᵉ n
𝕆-Clos2ᵉ (get i) = projᵉ i
𝕆-Clos2ᵉ inl-op = inlᵉ
𝕆-Clos2ᵉ inr-op = inrᵉ
𝕆-Clos2ᵉ case-op = 𝒞ᵉ
𝕆-Clos2ᵉ (prim p) = primᵉ p
{- let x = M in N means (λx. N) M -}
𝕆-Clos2ᵉ let-op = letᵉ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos2ᵉ init ρ M
