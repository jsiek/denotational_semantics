module Semantics.GraphErrM.Clos2 where
{-

 The semantics of Clos2 in the monadic graph model with errors (a
   pilot): a closure binds its free variables left to right, and is a
   function (Λᵐ) of the argument, whose body sees the values of the free
   variables.

-}

open import Framework.Syntax.SigUtil
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErrM.Prim
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

𝕆-Clos2ᵐ : DOpSig (𝒫 Value) sig
𝕆-Clos2ᵐ (clos-op n) ⟨ F , Ds ⟩ = binds n Ds (λ Xs → Λᵐ ⟨ apply-n n F Xs , ptt ⟩)
𝕆-Clos2ᵐ app = ⋆ᵐ
𝕆-Clos2ᵐ (lit B k) = ℬ B k
𝕆-Clos2ᵐ (tuple n) = 𝒯ᵐ n
𝕆-Clos2ᵐ (get i) = projᵐ i
𝕆-Clos2ᵐ inl-op = inlᵐ
𝕆-Clos2ᵐ inr-op = inrᵐ
𝕆-Clos2ᵐ case-op = 𝒞ᵐ
𝕆-Clos2ᵐ (prim p) = primᵐ p
𝕆-Clos2ᵐ let-op = letᵐ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos2ᵐ init ρ M
