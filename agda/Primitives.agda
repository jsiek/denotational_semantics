{-# OPTIONS --safe #-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Primitives where

open import Data.Bool  using (Bool) renaming (_≟_ to _=?_)
open import Data.Nat using (ℕ; suc; zero; _≟_) 
open import Data.Integer using (ℤ) renaming (_≟_ to _=int_)
open import Data.Unit using (tt) renaming (⊤ to Top)
open import Data.Empty using () renaming (⊥ to Bot)

data Base : Set where
  Nat : Base
  Int : Base
  𝔹 : Base
  Unit : Base
  Void : Base
  Blame : Base

data Prim : Set where
  base : Base → Prim
  _⇒_ : Base → Prim → Prim

data Label : Set where
  label : ℕ → Label

base-rep : Base → Set 
base-rep Nat = ℕ
base-rep Int = ℤ
base-rep 𝔹 = Bool
base-rep Unit = Top
base-rep Void = Bot
base-rep Blame = Label

rep : Prim → Set
rep (base b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p

arity : Prim → ℕ
arity (base k) = 0
arity (b ⇒ p) = suc (arity p)

base-eq? : (B : Base) → (B' : Base) → Dec (B ≡ B')
base-eq? Nat Nat = yes refl
base-eq? Nat Int = no (λ ())
base-eq? Nat 𝔹 = no (λ ())
base-eq? Nat Unit = no (λ ())
base-eq? Nat Void = no (λ ())
base-eq? Nat Blame  = no (λ ())
base-eq? Int Nat = no (λ ())
base-eq? Int Int = yes refl
base-eq? Int 𝔹 = no (λ ())
base-eq? Int Unit = no (λ ())
base-eq? Int Void = no (λ ())
base-eq? Int Blame  = no (λ ())
base-eq? 𝔹 Nat = no (λ ())
base-eq? 𝔹 Int = no (λ ())
base-eq? 𝔹 𝔹 = yes refl
base-eq? 𝔹 Unit = no (λ ())
base-eq? 𝔹 Void = no (λ ())
base-eq? 𝔹 Blame  = no (λ ())
base-eq? Unit Nat = no (λ ())
base-eq? Unit Int = no (λ ())
base-eq? Unit 𝔹 = no (λ ())
base-eq? Unit Unit = yes refl
base-eq? Unit Void = no (λ ())
base-eq? Unit Blame  = no (λ ())
base-eq? Void Nat = no (λ ())
base-eq? Void Int = no (λ ())
base-eq? Void 𝔹 = no (λ ())
base-eq? Void Unit = no (λ ())
base-eq? Void Void = yes refl
base-eq? Void Blame  = no (λ ())
base-eq? Blame Nat = no (λ ())
base-eq? Blame Int = no (λ ())
base-eq? Blame 𝔹 = no (λ ())
base-eq? Blame Unit = no (λ ())
base-eq? Blame Void = no (λ ())
base-eq? Blame Blame = yes refl

base-rep-eq? : ∀{B} → (k : base-rep B) (k′ : base-rep B) → Dec (k ≡ k′)
base-rep-eq? {Nat} k k′ = k ≟ k′
base-rep-eq? {Int} k k′ = k =int k′
base-rep-eq? {𝔹} k k′ = k =? k′
base-rep-eq? {Unit} tt tt = yes refl
base-rep-eq? {Void} () ()
base-rep-eq? {Blame} (label ℓ) (label ℓ′)
    with ℓ ≟ ℓ′
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }
