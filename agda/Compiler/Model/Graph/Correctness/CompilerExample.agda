{-

  An end-to-end example for the whole compiler, from ISWIM to Clos5:

    (λx. λy. x) 7 5

  The program produces 7 in ISWIM, so by the end theorem the compiled
  Clos5 program produces 7 as well.

  Also, a check of what globalize itself produces for a function whose
  body is another function: the inner code is lifted first.

-}

open import Primitives
open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
import Compiler.Lang.Clos4 as L4
import Compiler.Lang.Clos5 as L5
open import Compiler.Compile.Globalize using (globalize)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (⟦_⟧ₚ)
open import Compiler.Model.Graph.Correctness.AnnotateExample using (prog; prog-is-7)
open import Compiler.Model.Graph.Correctness.CompilerCorrect

open import NewSyntaxUtil
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Compiler.Model.Graph.Correctness.CompilerExample where

{- λ X. λ Y. (λ X'. λ Y'. 5) in Clos4: code whose body is more code -}
nested : L4.AST
nested = L4.fun-op L4.⦅ ! L4.clear (L4.bind (L4.bind (L4.ast
           (L4.fun-op L4.⦅ ! L4.clear (L4.bind (L4.bind (L4.ast
              (L4.lit Nat 5 L4.⦅ Nil ⦆)))) ,, Nil ⦆)))) ,, Nil ⦆

{- the inner code is definition 0 and the outer code, which refers to it,
   is definition 1; the definitions are listed newest first -}
nested-globalized : globalize nested
  ≡ L5.program (L5.fun-ref 0 L5.⦅ Nil ⦆ ∷ L5.lit Nat 5 L5.⦅ Nil ⦆ ∷ [])
               (L5.fun-ref 1 L5.⦅ Nil ⦆)
nested-globalized = refl

compiled-is-7 : const {Nat} 7 ∈ ⟦ compile prog ⟧ₚ
compiled-is-7 = proj₁ (compile-correct-const prog 7) prog-is-7
