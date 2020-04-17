{-
  Miscellaneous Stuff
-}
module Utilities where

open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
  
_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

