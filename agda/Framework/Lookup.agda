{-

  Looking up a typed index (Framework/Membership.agda) in a list of
  things indexed by the list's elements (an environment typed by a
  context, a table of definitions), and popping the newer part off
  such a list (a frame whose newer slots belong to a finished scope).

-}

module Framework.Lookup where

open import Framework.Membership using (_∋_; Z; S; _⊑_; here⊑; there⊑)

open import Data.List.Relation.Unary.All using (All; []; _∷_)

infixl 5 _!_
_!_ : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → xs ∋ x → P x
(p ∷ ps) ! Z = p
(p ∷ ps) ! S x = ps ! x

pop : ∀ {A : Set} {P : A → Set} {xs ys} → xs ⊑ ys → All P ys → All P xs
pop here⊑ ps = ps
pop (there⊑ s) (p ∷ ps) = pop s ps
