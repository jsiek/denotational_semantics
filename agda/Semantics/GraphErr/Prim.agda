{-

  The meaning of this compiler's primitive operations (Language.Prim) in
  the graph model with errors: a primitive applies to two integers, as
  in the graph model (primD, Semantics/Graph/Prim.agda), and is an error
  on ω in its operands (left to right) or on two values that are not
  both integers, as the machines' prim? is. (Its monotonicity,
  consistency and continuity are in proof/Semantics/GraphErr/Prim.agda.)

-}

module Semantics.GraphErr.Prim where

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.ErrorOps using (errs; val∈; wrong)
open import Semantics.Graph.Prim using (primD; out) public
open import Language.Prim using (Prim)

open import Data.List using (_∷_; [])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Unit renaming (⊤ to True)
open import Data.Empty renaming (⊥ to False)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_)

IsInt : Value → Set
IsInt (const {Int} n) = True
IsInt _ = False

primᵉ : Prim → DOp (𝒫 Value) (■ ∷ ■ ∷ [])
primᵉ p ⟨ D , ⟨ E , _ ⟩ ⟩ v =
    primD p ⟨ D , ⟨ E , ptt ⟩ ⟩ v
  ⊎ (v ≡ ω × (errs 2 ⟨ D , ⟨ E , ptt ⟩ ⟩
             ⊎ (wrong IsInt D × val∈ E) ⊎ (val∈ D × wrong IsInt E)))
