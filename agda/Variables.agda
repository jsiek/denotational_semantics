open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Variables where

data Var : ℕ → Set where

  Z : ∀ {Γ}
     ---------
   → Var (suc Γ)

  S_ : ∀ {Γ}
    → Var Γ
      ---------
    → Var (suc Γ)

Rename : ℕ → ℕ → Set
Rename Γ Δ = Var Γ → Var Δ

ext : ∀ {Γ Δ} → Rename Γ Δ
    ----------------------
  → Rename (suc Γ) (suc Δ)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)


postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

