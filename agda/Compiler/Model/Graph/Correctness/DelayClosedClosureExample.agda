{-

  A regression test for closures with no free variables.

  (λx. x) 5, after closure conversion, applies a closure whose tuple of
  free variables is empty. The empty tuple denotes {⟨⟩}, so the closure
  is not empty and the program produces 5, in Clos3 and, by the end
  theorem of the delay pass, in Clos4. (When 𝒯 0 was ∅, the closure
  denoted ∅ and so did the whole program.)

-}

open import NewSyntaxUtil
open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3
open import Compiler.Model.Graph.Sem.Clos3Iswim
import Compiler.Model.Graph.Sem.Clos4Iswim as S4
open import Compiler.Compile.Delay using (delay)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.DelayPreserveFinite using (preserve-const)

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

module Compiler.Model.Graph.Correctness.DelayClosedClosureExample where

{- the identity function, as a closure with no free variables -}
id-clos : AST
id-clos = clos-op 0 ⦅ ! clear (bind (bind (ast (` 0)))) ,, Nil ⦆

five : AST
five = lit Nat 5 ⦅ Nil ⦆

id-five : AST
id-five = app ⦅ id-clos ,, five ,, Nil ⦆

id-five-is-5 : const {Nat} 5 ∈ ⟦ id-five ⟧ ρ₀
id-five-is-5 = ⟨ const 5 ∷ [] , ⟨ clos∋ , ⟨ five⊆ , (λ ()) ⟩ ⟩ ⟩
  where
  {- apply the code to the empty tuple ⟨⟩ of free variables, then to 5 -}
  clos∋ : (const 5 ∷ []) ↦ const 5 ∈ ⟦ id-clos ⟧ ρ₀
  clos∋ = ⟨ ⟨⟩ ∷ [] , ⟨ ⟨ ⟨ here refl , (λ ()) ⟩ , (λ ()) ⟩
                     , ⟨ (λ { _ (here refl) → tt }) , (λ ()) ⟩ ⟩ ⟩

  five⊆ : mem (const {Nat} 5 ∷ []) ⊆ ⟦ five ⟧ ρ₀
  five⊆ _ (here refl) = ⟨ refl , refl ⟩

{- the delayed program produces 5 as well -}
delay-id-five-is-5 : const {Nat} 5 ∈ S4.⟦ delay id-five ⟧ ρ₀
delay-id-five-is-5 = preserve-const id-five 5 id-five-is-5
