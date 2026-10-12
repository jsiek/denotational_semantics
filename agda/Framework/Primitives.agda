module Framework.Primitives where

open import Data.Bool  using (Bool)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Unit renaming (⊤ to Top)
open import Data.Empty using () renaming (⊥ to Bot)

data Base : Set where
  Nat : Base
  Int : Base
  𝔹 : Base
  Unit : Base
  Void : Base
  Blame : Base

data Label : Set where
  label : ℕ → Label

base-rep : Base → Set 
base-rep Nat = ℕ
base-rep Int = ℤ
base-rep 𝔹 = Bool
base-rep Unit = Top
base-rep Void = Bot
base-rep Blame = Label
