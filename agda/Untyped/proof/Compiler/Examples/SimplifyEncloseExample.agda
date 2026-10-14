{-

  An example of simplify (Compiler/Simplify.agda) followed by the
  untyped enclose (Compiler/Enclose.agda).

-}

open import Framework.Primitives using (Int)
open import Language.Prim using (sub)
open import Language.ISWIM
open import Compiler.Simplify using (simplify)
open import Untyped.Compiler.Enclose using (enclose)
import Untyped.Language.Clos2 as L2
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; !_,,_; Nil)
open import proof.Compiler.Examples.SimplifyExample using (inline-let-src)

open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Untyped.proof.Compiler.Examples.SimplifyEncloseExample where

{- End to end: that let stays a let through enclose, so no closure is
   allocated for it (before let, it was the call (λ x. x - 1) (g 3) of a
   new closure). Only the functions of the source, λ g and λ x. x - 1,
   become closures (with no free variables):
     clos (λ g. let f = clos (λ x. x - 1) in let x = g 3 in x - 1) -}
dec₂ : L2.AST
dec₂ = L2.prim sub L2.⦅ L2.` 0 ,, L2.lit Int (+ 1) L2.⦅ Nil ⦆ ,, Nil ⦆

clos₂ : L2.AST → L2.AST
clos₂ N = L2.clos-op 0 L2.⦅ ! L2.clear (L2.bind (L2.ast N)) ,, Nil ⦆

inline-let-enclosed : enclose (simplify inline-let-src)
  ≡ clos₂ (L2.let-op L2.⦅ clos₂ dec₂ ,,
                          ⟩ L2.let-op L2.⦅ L2.app L2.⦅ L2.` 1 ,, L2.lit Int (+ 3) L2.⦅ Nil ⦆ ,, Nil ⦆ ,, ⟩ dec₂ ,, Nil ⦆ ,, Nil ⦆)
inline-let-enclosed = refl
