

module Val (Base : Set) (base-rep : Base → Set) where

infixr 7 _↦_
infixl 6 _⊔_

data Val : Set where
  ⊥ : Val
  const : {b : Base} → base-rep b → Val
  _↦_ : Val → Val → Val
  _⊔_ : (u : Val) → (v : Val) → Val

{- Splitting a la Huang and Oliveira (2021) -}
data _◁_▷_ : Val → Val → Val → Set where
   ◁⊔▷ : ∀{u v} → u ◁ u ⊔ v ▷ v
   ◁↦▷ : ∀{v w w₁ w₂}
      → w₁ ◁ w ▷ w₂
      → (v ↦ w₁) ◁ (v ↦ w) ▷ (v ↦ w₂)

data _ᵒ : Val → Set where
  ⊥ᵒ : ⊥ ᵒ
  constᵒ : ∀{B k} → (const {B} k) ᵒ
  ↦ᵒ : ∀{v w} → w ᵒ → (v ↦ w) ᵒ

infix 4 _⊑_
data _⊑_ : Val → Val → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k

  ⊑-conj-L : ∀ {u u₁ u₂ v}
        → u₁ ◁ u ▷ u₂
        → u₁ ⊑ v
        → u₂ ⊑ v
          -----------
        → u ⊑ v

  ⊑-conj-R1 : ∀ {u v w}
       → u ⊑ v  →  u ᵒ
         -------------
       → u ⊑ v ⊔ w

  ⊑-conj-R2 : ∀ {u v w}
       → u ⊑ w  → u ᵒ
         -----------
       → u ⊑ v ⊔ w

  ⊑-fun : ∀ {v w v′ w′}
       → v′ ⊑ v  → w ⊑ w′ → (v ↦ w) ᵒ
         -----------------------------
       → v ↦ w ⊑ v′ ↦ w′

