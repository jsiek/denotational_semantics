{-# OPTIONS --safe #-}
{-

  An end-to-end example for the pipeline Clos1 → Clos4:

    (λx. λy. 5) 7 3

  The inner closure is annotated with x as a free variable (annotate
  lists the surrounding variables), but its body does not use x, so
  optimize stops capturing it. The program produces 5 in Clos1, so by the
  pipeline theorem the compiled Clos4 program produces 5 as well.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos1
open import Compiler.Model.Graph.Sem.Clos1Iswim
import Compiler.Model.Graph.Sem.Clos4Iswim as S4
open import Compiler.Compile.Enclose using (fv-vars; enclose)
open import Compiler.Compile.Optimize using (optimize-program)
import Compiler.Lang.Clos2 as L2
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.EncloseCorrect
open import Compiler.Model.Graph.Correctness.PipelineCorrect

open import Data.Nat using (ℕ)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Compiler.Model.Graph.Correctness.PipelineExample where

lit-nat : ℕ → AST
lit-nat k = lit Nat k ⦅ Nil ⦆

{- λy. 5, annotated with the surrounding variable x -}
inner : AST
inner = clos-op 1 ⦅ ! bind (ast (lit-nat 5)) ,, fv-vars 1 ⦆

{- λx. λy. 5, at the top level, with no surrounding variables -}
outer : AST
outer = clos-op 0 ⦅ ! bind (ast inner) ,, fv-vars 0 ⦆

prog : AST
prog = app ⦅ app ⦅ outer ,, lit-nat 7 ,, Nil ⦆ ,, lit-nat 3 ,, Nil ⦆

prog-enclosed : Enclosed prog
prog-enclosed =
  enc-app (enc-app (enc-clos (enc-clos enc-lit (λ k → λ ()))
                             (λ k → λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }))
                   enc-lit)
          enc-lit

prog-is-5 : const {Nat} 5 ∈ ⟦ prog ⟧ ρ₀
prog-is-5 =
  ⟨ const 3 ∷ []
  , ⟨ ⟨ const 7 ∷ []
      , ⟨ ⟨ (λ ())                                   -- outer has no free variables
          , ⟨ ⟨ (λ { zero → ⟨ const 7 , here refl ⟩ })  -- inner's free variable x is 7
              , ⟨ ⟨ refl , refl ⟩ , (λ ()) ⟩ ⟩
            , (λ ()) ⟩ ⟩
        , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩
    , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩

{- after enclose, optimize, concretize and delay, the program still produces 5 -}
compiled-is-5 : const {Nat} 5 ∈ S4.⟦ compile prog ⟧ ρ₀
compiled-is-5 = proj₁ (pipeline-correct-const prog prog-enclosed 5) prog-is-5

{- optimize drops x: the inner closure no longer captures anything -}
optimized : optimize-program (enclose prog)
  ≡ L2.app L2.⦅ L2.app L2.⦅ L2.clos-op 0 L2.⦅ ! L2.clear (L2.bind (L2.ast
                    (L2.clos-op 0 L2.⦅ ! L2.clear (L2.bind (L2.ast
                        (L2.lit Nat 5 L2.⦅ Nil ⦆))) ,, Nil ⦆))) ,, Nil ⦆
                 ,, L2.lit Nat 7 L2.⦅ Nil ⦆ ,, Nil ⦆
           ,, L2.lit Nat 3 L2.⦅ Nil ⦆ ,, Nil ⦆
optimized = refl
