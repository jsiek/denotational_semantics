{- logical equivalence of two propositions -}

module Iff where

open import Data.Product using (_×_)

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)
