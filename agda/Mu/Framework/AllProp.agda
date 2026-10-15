{-

  Lemmas about lookup in heterogeneous vectors (Mu/Framework/AllUtil.agda),
  as proof/Framework/Lookup.agda's map-! for _!_: lookup commutes with
  map.

-}

module Mu.Framework.AllProp where

open import Framework.Membership using (_∋_; Z; S)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)

open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    X : Set
    P Q : X → Set
    xs : List X
    a : X

lookup-map : (f : ∀ {x} → P x → Q x) (ps : All P xs) (x : xs ∋ a) → lookup (map f ps) x ≡ f (lookup ps x)
lookup-map f (_ ∷ ps) Z = refl
lookup-map f (_ ∷ ps) (S x) = lookup-map f ps x

