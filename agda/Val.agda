module Val (Base : Set) (base-rep : Base → Set) where

infixr 7 _↦_
infixl 6 _⊔_

data Val : Set where
  ν : Val {- empty function -}
  const : {b : Base} → base-rep b → Val
  _↦_ : Val → Val → Val
  _⊔_ : (u : Val) → (v : Val) → Val
  car : Val → Val
  cdr : Val → Val
  inl : Val → Val
  inr : Val → Val

{- Splitting a la Huang and Oliveira (2021) -}
data _◁_▷_ : Val → Val → Val → Set where
   ◁⊔▷ : ∀{u v} → u ◁ u ⊔ v ▷ v
   ◁↦▷ : ∀{v w w₁ w₂}
      → w₁ ◁ w ▷ w₂
      → (v ↦ w₁) ◁ (v ↦ w) ▷ (v ↦ w₂)
   ◁car▷ : ∀{v v₁ v₂}
      → v₁ ◁ v ▷ v₂
      → (car v₁) ◁ (car v) ▷ (car v₂)
   ◁cdr▷ : ∀{v v₁ v₂}
      → v₁ ◁ v ▷ v₂
      → (cdr v₁) ◁ (cdr v) ▷ (cdr v₂)
   ◁inl▷ : ∀{v v₁ v₂}
      → v₁ ◁ v ▷ v₂
      → (inl v₁) ◁ (inl v) ▷ (inl v₂)
   ◁inr▷ : ∀{v v₁ v₂}
      → v₁ ◁ v ▷ v₂
      → (inr v₁) ◁ (inr v) ▷ (inr v₂)

data _ᵒ : Val → Set where
  νᵒ : ν ᵒ
  constᵒ : ∀{B k} → (const {B} k) ᵒ
  ↦ᵒ : ∀{v w} → w ᵒ → (v ↦ w) ᵒ
  carᵒ : ∀{v} → (car v) ᵒ
  cdrᵒ : ∀{v} → (cdr v) ᵒ
  inlᵒ : ∀{v} → (inl v) ᵒ
  inrᵒ : ∀{v} → (inr v) ᵒ

infix 4 _⊑_
data _⊑_ : Val → Val → Set where

  ⊑-ν : ∀ {v w} → ν ⊑ v ↦ w

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

  ⊑-car : ∀ {v v′}
       → v ⊑ v′ → v ᵒ
         ------------------------------
       → car v ⊑ car v′

  ⊑-cdr : ∀ {v v′}
       → v ⊑ v′ → v ᵒ
         ------------------------------
       → cdr v ⊑ cdr v′

  ⊑-inl : ∀ {v v′}
       → v ⊑ v′ → (inl v) ᵒ
         ------------------
       → inl v ⊑ inl v′

  ⊑-inr : ∀ {v v′}
       → v ⊑ v′ → (inr v) ᵒ
         ------------------
       → inr v ⊑ inr v′

