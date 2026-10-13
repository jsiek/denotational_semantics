{-

  The meaning of this compiler's primitives in the monadic graph model
  with errors: the graph model's primD (Semantics/Graph/Prim.agda) under
  binds of its two operands, left to right, checking that each is an
  integer, as the machines' prim? does.

-}

module Semantics.GraphErrM.Prim where

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.ErrorMonad
open import Semantics.Graph.Prim using (primD; out) public
open import Language.Prim using (Prim)

open import Data.List using (_∷_; [])
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

primᵐ : Prim → DOp (𝒫 Value) (■ ∷ ■ ∷ [])
primᵐ p ⟨ D , ⟨ E , _ ⟩ ⟩ =
  D ≫= λ X → E ≫= λ Y → checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))
