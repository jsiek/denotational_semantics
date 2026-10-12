{-

  An end-to-end example for the whole compiler ISWIM → Clos5:

    (λx. λy. λz. x) 7 3 1

  enclose captures the first two surrounding variables, x and y, in the
  innermost closure, because its body uses x; but the body does not use
  y, so optimize stops capturing it. The program produces 7 in ISWIM, so
  by the end theorem the compiled Clos5 program produces 7 as well.

-}

open import NewSyntaxUtil
open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Lang.ISWIM
open import Compiler.Model.Graph.Sem.ISWIM
open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Compile.Optimize using (optimize-program)
import Compiler.Lang.Clos2 as L2
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (⟦_⟧ₚ)
open import Compiler.Model.Graph.Correctness.CompilerCorrect

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Compiler.Model.Graph.Correctness.PipelineExample where

lit-nat : ℕ → AST
lit-nat k = lit Nat k ⦅ Nil ⦆

{- λx. λy. λz. x -}
fun : AST
fun = lam ⦅ ⟩ (lam ⦅ ⟩ (lam ⦅ ⟩ (` 2) ,, Nil ⦆) ,, Nil ⦆) ,, Nil ⦆

prog : AST
prog = app ⦅ app ⦅ app ⦅ fun ,, lit-nat 7 ,, Nil ⦆ ,, lit-nat 3 ,, Nil ⦆
           ,, lit-nat 1 ,, Nil ⦆

{- the innermost closure captures x and y -}
enclosed : enclose fun
  ≡ L2.clos-op 0 L2.⦅ ! L2.clear (L2.bind (L2.ast
      (L2.clos-op 1 L2.⦅ ! L2.clear (L2.bind (L2.bind (L2.ast
          (L2.clos-op 2 L2.⦅ ! L2.clear (L2.bind (L2.bind (L2.bind (L2.ast (L2.` 2)))))
                           ,, ((L2.` 1) ,, ((L2.` 0) ,, Nil)) ⦆))))
                       ,, ((L2.` 0) ,, Nil) ⦆))) ,, Nil ⦆
enclosed = refl

{- optimize drops y: the innermost closure captures only x -}
optimized : optimize-program (enclose fun)
  ≡ L2.clos-op 0 L2.⦅ ! L2.clear (L2.bind (L2.ast
      (L2.clos-op 1 L2.⦅ ! L2.clear (L2.bind (L2.bind (L2.ast
          (L2.clos-op 1 L2.⦅ ! L2.clear (L2.bind (L2.bind (L2.ast (L2.` 1))))
                           ,, ((L2.` 1) ,, Nil) ⦆))))
                       ,, ((L2.` 0) ,, Nil) ⦆))) ,, Nil ⦆
optimized = refl

prog-is-7 : const {Nat} 7 ∈ ⟦ prog ⟧ ρ₀
prog-is-7 =
  ⟨ const 1 ∷ []
  , ⟨ ⟨ const 3 ∷ []
      , ⟨ ⟨ const 7 ∷ []
          , ⟨ ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩
            , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩
        , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩
    , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩

{- after the whole compiler, the program still produces 7 -}
compiled-is-7 : const {Nat} 7 ∈ ⟦ compile prog ⟧ₚ
compiled-is-7 = proj₁ (compile-correct-const prog 7) prog-is-7
