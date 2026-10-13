{-

  The graph-model meaning of this compiler's primitive operations
  (Language.Prim): the value of a primitive's result and the
  operator primD. (Its monotonicity, consistency and continuity are in
  proof/Semantics/Graph/Prim.agda.) The rest of the domain and its
  operators are language independent (Framework/GraphModel/).

-}

module Semantics.Graph.Prim where

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Language.Prim using (Prim; Out; int; bool; δ)

open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
open import Data.List using (_∷_; [])
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_)

{- the value of the result of a primitive: eq returns left ⟨⟩ for true
   and right ⟨⟩ for false -}
out : Out → Value
out (int n) = const {Int} n
out (bool true) = left ⟨⟩
out (bool false) = right ⟨⟩

{- a primitive applies to the integers in its operands -}
primD : Prim → DOp (𝒫 Value) (■ ∷ ■ ∷ [])
primD p ⟨ D , ⟨ E , _ ⟩ ⟩ v =
  Σ[ n ∈ ℤ ] Σ[ m ∈ ℤ ] const {Int} n ∈ D × const {Int} m ∈ E × v ≡ out (δ p n m)
