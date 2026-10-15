{-

  Lemmas about lookup in heterogeneous vectors (Mu/Framework/AllUtil.agda),
  as proof/Framework/Lookup.agda's map-! and forget-! for _!_: lookup
  commutes with map and with forgetting the newer part of a vector
  (Framework/Lookup.agda).

-}

module Mu.Framework.AllProp where

open import Framework.Membership using (_∋_; Z; S; _⊑_; here⊑; there⊑; ⊑-∋)
open import Framework.Lookup using (forget)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)

open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    X : Set
    P Q : X → Set
    xs ys : List X
    a : X

lookup-map : (f : ∀ {x} → P x → Q x) (ps : All P xs) (x : xs ∋ a) → lookup (map f ps) x ≡ f (lookup ps x)
lookup-map f (_ ∷ ps) Z = refl
lookup-map f (_ ∷ ps) (S x) = lookup-map f ps x

lookup-forget : (p : xs ⊑ ys) (ps : All P ys) (x : xs ∋ a) → lookup (forget p ps) x ≡ lookup ps (⊑-∋ p x)
lookup-forget here⊑ ps x = refl
lookup-forget (there⊑ p) (_ ∷ ps) x = lookup-forget p ps x
