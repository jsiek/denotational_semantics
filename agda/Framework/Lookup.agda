{-

  Looking up a typed index (Framework/Membership.agda) in a list of
  things indexed by the list's elements (an environment typed by a
  context, a table of definitions), and forgetting the newer part of
  such a list (a frame whose newer slots belong to a finished scope).

-}

module Framework.Lookup where

open import Framework.Membership using (_∋_; Z; S; _⊑_; here⊑; there⊑)

open import Data.List.Relation.Unary.All using (All; []; _∷_)

infixl 5 _!_
_!_ : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → xs ∋ x → P x
(p ∷ ps) ! Z = p
(p ∷ ps) ! S x = ps ! x

forget : ∀ {A : Set} {P : A → Set} {xs ys} → xs ⊑ ys → All P ys → All P xs
forget here⊑ ps = ps
forget (there⊑ s) (p ∷ ps) = forget s ps
