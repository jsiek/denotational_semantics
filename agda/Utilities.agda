{-
  Miscellaneous Stuff
-}
module Utilities where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Iso {ℓ₁ ℓ₂} (P : Set ℓ₁) (Q : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field to : P → Q
        from : Q → P

_iff_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (lsuc (ℓ₁ ⊔ ℓ₂))
P iff Q = Iso P Q

postulate
  extensionality : ∀ {ℓ₁ ℓ₂ : Level}{A : Set ℓ₁}{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix 6 _≅_
_≅_ = Iso

≅-refl : ∀{ℓ}{D : Set ℓ} → D ≅ D
≅-refl {D} = record { to = λ z → z ; from = λ z → z }

≅-reflexive : ∀{ℓ}{D₁ D₂ : Set ℓ} → D₁ ≡ D₂ → D₁ ≅ D₂
≅-reflexive refl = record { to = λ z → z ; from = λ z → z }

≅-sym : ∀{ℓ}{D₁ D₂ : Set ℓ} → D₁ ≅ D₂ → D₂ ≅ D₁
≅-sym d12 = record { to = Iso.from d12 ; from = Iso.to d12 }

≅-trans : ∀{ℓ}{D₁ D₂ D₃ : Set ℓ} → D₁ ≅ D₂ → D₂ ≅ D₃ → D₁ ≅ D₃
≅-trans d12 d23 = record
                    { to = λ z → Iso.to d23 (Iso.to d12 z)
                    ; from = λ z → Iso.from d12 (Iso.from d23 z) }

module ≅-Reasoning where

  infixr 2 _≅⟨⟩_
  _≅⟨⟩_ : ∀ {ℓ} (D₁ : Set ℓ) {D₂ : Set ℓ} → D₁ ≅ D₂ → D₁ ≅ D₂
  D₁ ≅⟨⟩ D₁≅D₂ = D₁≅D₂
  
  infixr 2 _≅⟨_⟩_
  _≅⟨_⟩_ : ∀ {ℓ} (D₁ : Set ℓ) {D₂ D₃ : Set ℓ} → D₁ ≅ D₂ → D₂ ≅ D₃ → D₁ ≅ D₃
  D₁ ≅⟨ D₁≅D₂ ⟩ D₂≅D₃ = ≅-trans D₁≅D₂ D₂≅D₃
  
  infix 3 _∎
  _∎ : ∀ {ℓ} (D : Set ℓ) → D ≅ D
  D ∎  =  ≅-refl
