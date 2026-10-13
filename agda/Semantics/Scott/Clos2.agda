{-

  The Scott-domain semantics of Clos2. A closure binds its free variables
  like a nested let: its body is applied to the meanings of the free
  variable expressions, and the result is a (strict) function of the
  argument. Like tuples, closures are strict: a closure is ⊥ unless each
  of its free variables is defined. This semantics is after the 'enclose'
  pass, and before the 'concretize' pass.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Data.List using (List; []; _∷_; replicate)
open import Data.Fin using (Fin)
open import Framework.abt.Sig using (Sig; ■; ν; ∁)
open import Framework.Syntax.SigUtil using (ν-n)
import Language.Clos2 as C

module Semantics.Scott.Clos2
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe
open import Framework.Scott.Ops pt fe pe
open import Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe

{- apply the meaning of a body under n binders to the meanings of n
   arguments -}
apply-n : (n : ℕ) {b : Sig} → DCPO[ Res (ν-n n b) ×₁ Ress (replicate n ■) , Res b ]
apply-n zero {b} = fst₁ (Res b) 𝟙ᵈ
apply-n (succ n) {b} =
 ∘₁ ((𝔻 ⟹₁ Res (ν-n n b)) ×₁ (𝔻 ×₁ Ress (replicate n ■))) (Res (ν-n n b) ×₁ Ress (replicate n ■)) (Res b)
   (pair₁ ((𝔻 ⟹₁ Res (ν-n n b)) ×₁ (𝔻 ×₁ Ress (replicate n ■))) (Res (ν-n n b)) (Ress (replicate n ■))
      (∘₁ ((𝔻 ⟹₁ Res (ν-n n b)) ×₁ (𝔻 ×₁ Ress (replicate n ■))) ((𝔻 ⟹₁ Res (ν-n n b)) ×₁ 𝔻) (Res (ν-n n b))
         (pair₁ ((𝔻 ⟹₁ Res (ν-n n b)) ×₁ (𝔻 ×₁ Ress (replicate n ■))) (𝔻 ⟹₁ Res (ν-n n b)) 𝔻
            (fst₁ (𝔻 ⟹₁ Res (ν-n n b)) (𝔻 ×₁ Ress (replicate n ■)))
            (∘₁ ((𝔻 ⟹₁ Res (ν-n n b)) ×₁ (𝔻 ×₁ Ress (replicate n ■))) (𝔻 ×₁ Ress (replicate n ■)) 𝔻
               (snd₁ (𝔻 ⟹₁ Res (ν-n n b)) (𝔻 ×₁ Ress (replicate n ■))) (fst₁ 𝔻 (Ress (replicate n ■)))))
         (eval₁ 𝔻 (Res (ν-n n b))))
      (∘₁ ((𝔻 ⟹₁ Res (ν-n n b)) ×₁ (𝔻 ×₁ Ress (replicate n ■))) (𝔻 ×₁ Ress (replicate n ■)) (Ress (replicate n ■))
         (snd₁ (𝔻 ⟹₁ Res (ν-n n b)) (𝔻 ×₁ Ress (replicate n ■))) (snd₁ 𝔻 (Ress (replicate n ■)))))
   (apply-n n {b})

{- a closure: guard n (the free variables) (Λ (the body applied to them)) -}
closᶜ : (n : ℕ) → DCPO[ Res (ν-n n (ν ■)) ×₁ Ress (replicate n ■) , 𝔻 ]
closᶜ n =
 ∘₁ (Res (ν-n n (ν ■)) ×₁ Ress (replicate n ■)) ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻
   (pair₁ (Res (ν-n n (ν ■)) ×₁ Ress (replicate n ■)) (𝔻 ⟹₁ 𝔻) 𝔻
      (∘₁ (Res (ν-n n (ν ■)) ×₁ Ress (replicate n ■)) (Ress (replicate n ■)) (𝔻 ⟹₁ 𝔻)
         (snd₁ (Res (ν-n n (ν ■))) (Ress (replicate n ■)))
         (∘₁ (Ress (replicate n ■)) (Pow (Fin n) 𝔻) (𝔻 ⟹₁ 𝔻) (toPow n) (guard n)))
      (∘₁ (Res (ν-n n (ν ■)) ×₁ Ress (replicate n ■)) (𝔻 ⟹₁ 𝔻) 𝔻 (apply-n n {ν ■}) Λ))
   (eval₁ 𝔻 𝔻)

𝕆-Clos2 : SemOps C.Op C.sig
𝕆-Clos2 (C.clos-op n) = closᶜ n
𝕆-Clos2 C.app = binary app
𝕆-Clos2 (C.lit B k) = const₁ 𝟙ᵈ 𝔻 (const B k)
𝕆-Clos2 (C.tuple n) = tupleᶜ n
𝕆-Clos2 (C.get i) = unary (proj i)
𝕆-Clos2 C.inl-op = unary inl
𝕆-Clos2 C.inr-op = unary inr
𝕆-Clos2 C.case-op = caseᶜ
𝕆-Clos2 (C.prim p) = binary (primD p)

{- the meaning of a term: the operators, folded over the term; a variable
   not in scope (under a clear) means ω -}
open Semantics C.Op C.sig ω 𝕆-Clos2 public
