{-
  Miscellaneous Stuff
-}
module Utilities where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Iso {ℓ₁ ℓ₂} (P : Set ℓ₁) (Q : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field to : P → Q
        from : Q → P

_iff_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (lsuc (ℓ₁ ⊔ ℓ₂))
P iff Q = Iso P Q

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

