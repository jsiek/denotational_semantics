{-

  An end-to-end example from ISWIM to Clos4:

    (λx. λy. x) 7 5

  annotate gives the outer function no free variables and the inner one
  just x. The program produces 7 in ISWIM, so by the end theorem the
  program compiled all the way to Clos4 produces 7 as well.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.ISWIM
open import Compiler.Model.Graph.Sem.ISWIM
import Compiler.Model.Graph.Sem.Clos4Iswim as S4
import Compiler.Lang.Clos1 as L1
open import Compiler.Compile.Annotate using (annotate)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.AnnotateCorrect

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Compiler.Model.Graph.Correctness.AnnotateExample where

lit-nat : ℕ → AST
lit-nat k = lit Nat k ⦅ Nil ⦆

{- λx. λy. x -}
const-fun : AST
const-fun = lam ⦅ ⟩ (lam ⦅ ⟩ (` 1) ,, Nil ⦆) ,, Nil ⦆

prog : AST
prog = app ⦅ app ⦅ const-fun ,, lit-nat 7 ,, Nil ⦆ ,, lit-nat 5 ,, Nil ⦆

{- the outer closure captures nothing; the inner one captures x -}
annotated : annotate const-fun
  ≡ L1.clos-op 0 L1.⦅ ⟩ (L1.clos-op 1 L1.⦅ ⟩ (L1.` 1) ,, ((L1.` 0) ,, Nil) ⦆) ,, Nil ⦆
annotated = refl

prog-is-7 : const {Nat} 7 ∈ ⟦ prog ⟧ ρ₀
prog-is-7 =
  ⟨ const 5 ∷ []
  , ⟨ ⟨ const 7 ∷ []
      , ⟨ ⟨ ⟨ here refl , (λ ()) ⟩ , (λ ()) ⟩
        , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩
    , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩

{- compiled all the way to Clos4, the program still produces 7 -}
compiled-is-7 : const {Nat} 7 ∈ S4.⟦ compile-iswim prog ⟧ ρ₀
compiled-is-7 = proj₁ (compile-iswim-correct-const prog 7) prog-is-7
