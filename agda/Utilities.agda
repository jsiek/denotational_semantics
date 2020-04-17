{-
  Miscellaneous Stuff
-}
module Utilities where

open import Data.Product using (_×_)
  
_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)
