module Untyped.Semantics.Graph.Clos2Iswim where
{-

 In this intermediate semantics a closure binds its free variables like a
   nested let: its body is applied directly to the denotations of the free
   variable expressions, and the result is a function of the argument.
   Like tuples, closures are strict: a closure has no values unless each
   of its free variables has one.
 This semantics is after the 'enclose' pass,
   and before the 'concretize' pass.

-}

open import Framework.Syntax.SigUtil
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Semantics.Graph.Prim
open import Untyped.Language.Clos2
open import Framework.GraphModel.Env using (Env)
open import Framework.abt.Fold2 Op sig using (fold)

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)

{- apply a curried function of n sets to the denotations of the free variables -}
apply-n : ∀ n {b} → Result (𝒫 Value) (ν-n n b) → Results (𝒫 Value) (replicate n ■)
  → Result (𝒫 Value) b
apply-n zero F _ = F
apply-n (suc n) F ⟨ D , Ds ⟩ = apply-n n (F D) Ds

𝕆-Clos2 : DOpSig (𝒫 Value) sig
𝕆-Clos2 (clos-op n) ⟨ F , Ds ⟩ = guard-n n Ds (Λ ⟨ apply-n n F Ds , ptt ⟩)
𝕆-Clos2 app = ⋆
𝕆-Clos2 (lit B k) = ℬ B k
𝕆-Clos2 (tuple n) = 𝒯 n
𝕆-Clos2 (get i) = proj i
𝕆-Clos2 inl-op = inl
𝕆-Clos2 inr-op = inr
𝕆-Clos2 case-op = 𝒞
𝕆-Clos2 (prim p) = primD p
{- let x = M in N means (λx. N) M -}
𝕆-Clos2 let-op ⟨ D , ⟨ F , _ ⟩ ⟩ = ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

{- the meaning of a term in an environment: the operators, folded over the
   term; a variable means what the environment gives it, and a variable
   not in scope (under a clear) means {ω} -}
init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧ : AST → Env Value → 𝒫 Value
⟦ M ⟧ ρ = fold 𝕆-Clos2 init ρ M
