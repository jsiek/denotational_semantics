{-

  An example of the enclose pass:

    (λx. λy. x) 7 5

  enclose gives the outer closure no free variables and the inner one
  just x. The program produces 7 in ISWIM, so by the correctness of
  enclose it produces 7 in Clos2 as well.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.ISWIM
open import Compiler.Model.Graph.Sem.ISWIM
import Compiler.Model.Graph.Sem.Clos2Iswim as S2
import Compiler.Lang.Clos2 as L2
open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.EncloseCorrect using (enclose-correct-closed)

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Compiler.Model.Graph.Correctness.EncloseExample where

lit-nat : ℕ → AST
lit-nat k = lit Nat k ⦅ Nil ⦆

{- λx. λy. x -}
const-fun : AST
const-fun = lam ⦅ ⟩ (lam ⦅ ⟩ (` 1) ,, Nil ⦆) ,, Nil ⦆

prog : AST
prog = app ⦅ app ⦅ const-fun ,, lit-nat 7 ,, Nil ⦆ ,, lit-nat 5 ,, Nil ⦆

{- the outer closure captures nothing; the inner one captures x, which its
   body refers to as variable 1 -}
enclosed : enclose const-fun
  ≡ L2.clos-op 0 L2.⦅ ! L2.clear (L2.bind (L2.ast
      (L2.clos-op 1 L2.⦅ ! L2.clear (L2.bind (L2.bind (L2.ast (L2.` 1))))
                       ,, ((L2.` 0) ,, Nil) ⦆))) ,, Nil ⦆
enclosed = refl

prog-is-7 : const {Nat} 7 ∈ ⟦ prog ⟧ ρ₀
prog-is-7 =
  ⟨ const 5 ∷ []
  , ⟨ ⟨ const 7 ∷ []
      , ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩
        , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩
    , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩

{- after enclose, the program still produces 7 -}
enclosed-is-7 : const {Nat} 7 ∈ S2.⟦ enclose prog ⟧ ρ₀
enclosed-is-7 = proj₁ (enclose-correct-closed prog) _ prog-is-7
