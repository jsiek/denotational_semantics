{-# OPTIONS --rewriting #-}

module DenotSTLC where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List
open import Data.Maybe using (Maybe; nothing; just)
open import RecSTLC
open import Var
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Function using (id; _∘_)

ret : ∀{T : Set} → T → ℕ → Maybe T
ret t = λ n → just t

_>>=_ : ∀{T U : Set} → (ℕ → Maybe T) → (T → ℕ → Maybe U) → ℕ → Maybe U
_>>=_ m f n
    with m n
... | nothing = nothing
... | just x = f x n

⟦_⟧ᵗ : Type → Set
⟦ `ℕ ⟧ᵗ = ℕ
⟦ S ⇒ T ⟧ᵗ = ⟦ S ⟧ᵗ → ℕ → Maybe ⟦ T ⟧ᵗ

⟦_⟧ᴸ : List Type → Set
⟦ [] ⟧ᴸ = ⊤
⟦ A ∷ Γ ⟧ᴸ = ⟦ A ⟧ᵗ × ⟦ Γ ⟧ᴸ

infixr 8 _^_
_^_ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → (A → A)
F ^ zero     =  Function.id
F ^ (suc n)  =  F ∘ (F ^ n)

⟦_⟧ : ∀{Γ : List Type}{M : Term}{T : Type} → Γ ⊢ M ⦂ T → ⟦ Γ ⟧ᴸ  → (ℕ → Maybe ⟦ T ⟧ᵗ)

⟦_⟧ⱽ : ∀{Γ : List Type}{V : Term}{T : Type} → Γ ⊢ⱽ V ⦂ T → ⟦ Γ ⟧ᴸ → ⟦ T ⟧ᵗ
⟦ ⊢ⱽzero ⟧ⱽ ρ = 0
⟦ ⊢ⱽsuc ⊢V ⟧ⱽ ρ = suc (⟦ ⊢V ⟧ⱽ ρ)
⟦ ⊢ⱽƛ ⊢N ⟧ⱽ ρ = λ a n → ⟦ ⊢N ⟧ (a , ρ) n
⟦ ⊢ⱽμ{Γ}{V}{A}{B} ⊢V ⟧ⱽ ρ a n =
  (F ^ (suc n)) (λ a n → nothing) a n
  where
  F : (⟦ A ⟧ᵗ → ℕ → Maybe ⟦ B ⟧ᵗ) → (⟦ A ⟧ᵗ → ℕ → Maybe ⟦ B ⟧ᵗ)
  F f = ⟦ ⊢V ⟧ⱽ (f , ρ)

⟦_⟧ {B ∷ Γ} (⊢` {.(B ∷ Γ)} {x = zero} refl) (b , ρ) = λ x → just b
⟦_⟧ {B ∷ Γ} (⊢` {x = suc x} ∋x) (b , ρ) = ⟦ ⊢` ∋x ⟧ ρ 
⟦ ⊢suc ⊢M ⟧ ρ = ⟦ ⊢M ⟧ ρ >>= λ m → ret (suc m)
⟦ ⊢case ⊢L ⊢M ⊢N ⟧ ρ = ⟦ ⊢L ⟧ ρ >>= cases
  where
  cases : ℕ → ℕ → Maybe ⟦ _ ⟧ᵗ
  cases zero = ⟦ ⊢M ⟧ ρ
  cases (suc l) = ⟦ ⊢N ⟧ (l , ρ)
⟦ ⊢val ⊢V ⟧ ρ = λ n → just (⟦ ⊢V ⟧ⱽ ρ)
⟦ ⊢· ⊢L ⊢M ⟧ ρ = ⟦ ⊢L ⟧ ρ >>= λ f → ⟦ ⊢M ⟧ ρ >>= λ a → f a

