{-

  An end-to-end example for concretize and split: a closure that captures
  a free variable.

    case inl 7 of
      x ⇒ (λy. x) 5      -- the closure captures x
      _ ⇒ 0

  In Clos2 the closure binds x and then y; concretize puts x in a tuple
  and replaces it by a projection from that tuple. The program produces 7
  in Clos2, so by the theorems for concretize and split it produces 7 after concretize and split.

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import Untyped.Language.Clos2
open import Untyped.proof.Semantics.Graph.Clos2Iswim
import Untyped.proof.Semantics.Graph.Clos4Iswim as S4
open import Untyped.Compiler.Concretize using (concretize-program)
open import Untyped.Compiler.Split using (split)
open import Untyped.proof.Correctness.Graph.SplitFiniteCommon using (ρ₀)
open import Untyped.proof.Correctness.Graph.ConcretizeCorrect using (concretize-correct-closed)
open import Untyped.proof.Correctness.Graph.SplitPreserve using (split-correct-const)

open import Data.Nat using (ℕ)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (refl)

module Untyped.proof.Correctness.Graph.ConcretizeExample where

lit-nat : ℕ → AST
lit-nat k = lit Nat k ⦅ Nil ⦆

{- λy. x, where x is the free variable 0 -}
const-x : AST
const-x = clos-op 1 ⦅ ! clear (bind (bind (ast (` 1)))) ,, ((` 0) ,, Nil) ⦆

prog : AST
prog = case-op ⦅ inl-op ⦅ lit-nat 7 ,, Nil ⦆
              ,, ⟩ app ⦅ const-x ,, lit-nat 5 ,, Nil ⦆
              ,, ⟩ lit-nat 0
              ,, Nil ⦆

prog-is-7 : const {Nat} 7 ∈ ⟦ prog ⟧ ρ₀
prog-is-7 = inj₁ ⟨ const 7 , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , ⟨ app∋ , ≈-single ⟩ ⟩ ⟩ ⟩
  where
  app∋ : const {Nat} 7 ∈ ⟦ app ⦅ const-x ,, lit-nat 5 ,, Nil ⦆ ⟧ (mem (const {Nat} 7 ∷ []) • ρ₀)
  {- the closure applies because its free variable x has a value, 7 -}
  app∋ = ⟨ const 5 ∷ [] , ⟨ ⟨ (λ { zero → ⟨ const 7 , here refl ⟩ }) , ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ ⟩
                          , ⟨ (λ { _ (here refl) → ⟨ refl , refl ⟩ }) , (λ ()) ⟩ ⟩ ⟩

{- after concretize and split, the program still produces 7 -}
compiled-is-7 : const {Nat} 7 ∈ S4.⟦ split (concretize-program prog) ⟧ ρ₀
compiled-is-7 =
  proj₁ (split-correct-const (concretize-program prog) 7) (proj₁ (concretize-correct-closed prog) _ prog-is-7)
