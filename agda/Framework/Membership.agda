{-

  Typed de Bruijn indices into a list (a context of types, a table of
  definitions, a list of blocks), their positions, and suffixes of a
  list: Σ ⊑ Σ' when Σ' is Σ with more elements in front, so that an
  index into Σ is one into Σ' (for tables that grow at the front).

-}

module Framework.Membership where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _∸_)

infix 4 _∋_
data _∋_ {A : Set} : List A → A → Set where
  Z : ∀ {Γ a} → (a ∷ Γ) ∋ a
  S : ∀ {Γ a b} → Γ ∋ a → (b ∷ Γ) ∋ a

{- the position of an index, from the front -}
idx : ∀ {A : Set} {Γ : List A} {a} → Γ ∋ a → ℕ
idx Z = zero
idx (S x) = suc (idx x)

{- the position of an index, from the back (stable as the list grows) -}
lvl : ∀ {A : Set} {Γ : List A} {a} → Γ ∋ a → ℕ
lvl {Γ = Γ} x = length Γ ∸ suc (idx x)

infix 4 _⊑_
data _⊑_ {A : Set} : List A → List A → Set where
  here⊑ : ∀ {Γ} → Γ ⊑ Γ
  there⊑ : ∀ {Γ Γ' a} → Γ ⊑ Γ' → Γ ⊑ (a ∷ Γ')

⊑-∋ : ∀ {A : Set} {Γ Γ' : List A} {a} → Γ ⊑ Γ' → Γ ∋ a → Γ' ∋ a
⊑-∋ here⊑ x = x
⊑-∋ (there⊑ s) x = S (⊑-∋ s x)

⊑-trans : ∀ {A : Set} {Γ Γ' Γ'' : List A} → Γ ⊑ Γ' → Γ' ⊑ Γ'' → Γ ⊑ Γ''
⊑-trans s here⊑ = s
⊑-trans s (there⊑ t) = there⊑ (⊑-trans s t)
