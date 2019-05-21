module Primitives where

open import Data.Bool  using (Bool)
open import Data.Nat using (ℕ)

data Base : Set where
  Nat : Base
  𝔹 : Base

data Prim : Set where
  `_ : Base → Prim
  _⇒_ : Base → Prim → Prim

base-rep : Base → Set 
base-rep Nat = ℕ
base-rep 𝔹 = Bool

rep : Prim → Set
rep (` b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p

