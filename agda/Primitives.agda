import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Primitives where

open import Data.Bool  using (Bool)
open import Data.Nat using (ℕ)

data Base : Set where
  Nat : Base
  𝔹 : Base

data Prim : Set where
  base : Base → Prim
  _⇒_ : Base → Prim → Prim

base-rep : Base → Set 
base-rep Nat = ℕ
base-rep 𝔹 = Bool

rep : Prim → Set
rep (base b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p

base-eq? : (B : Base) → (B' : Base) → Dec (B ≡ B')
base-eq? Nat Nat = yes refl
base-eq? Nat 𝔹 = no (λ ())
base-eq? 𝔹 Nat = no (λ ())
base-eq? 𝔹 𝔹 = yes refl

