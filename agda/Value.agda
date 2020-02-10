module Value where

open import Primitives
open import Variables

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  lit : {B : Base} → base-rep B → Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

infix 4 _⊑_

data _⊑_ : Value → Value → Set where
  Bot⊑ : ∀ {v} → ⊥ ⊑ v
  Lit⊑ : ∀{B k} → lit {B} k ⊑ lit {B} k
  Fun⊑ : ∀ {v₁ v₂} → (v₁ ↦ v₂) ⊑ (v₁ ↦ v₂)
  ConjL⊑ : ∀ {v v₁ v₂}
      → v₁ ⊑ v  →  v₂ ⊑ v
        -----------------
      → (v₁ ⊔ v₂) ⊑ v
  ConjR1⊑ : ∀ {v v₁ v₂}
     → v ⊑ v₁
       -------------
     → v ⊑ (v₁ ⊔ v₂)
  ConjR2⊑ : ∀ {v v₁ v₂}
     → v ⊑ v₂
       -------------
     → v ⊑ (v₁ ⊔ v₂)

Refl⊑ : ∀ {v} → v ⊑ v
Refl⊑ {⊥} = Bot⊑
Refl⊑ {lit {B} k} = Lit⊑
Refl⊑ {v ↦ v₁} = Fun⊑
Refl⊑ {v ⊔ v₁} = ConjL⊑ (ConjR1⊑ Refl⊑) (ConjR2⊑ Refl⊑)

Trans⊑ : ∀ {v₁ v₂ v₃} → v₁ ⊑ v₂ → v₂ ⊑ v₃ → v₁ ⊑ v₃
Trans⊑ Bot⊑ b = Bot⊑
Trans⊑ Lit⊑ b = b
Trans⊑ Fun⊑ b = b
Trans⊑ (ConjL⊑ a a₁) b = ConjL⊑ (Trans⊑ a b) (Trans⊑ a₁ b)
Trans⊑ (ConjR1⊑ a) (ConjL⊑ b b₁) = Trans⊑ a b
Trans⊑ (ConjR1⊑ a) (ConjR1⊑ b) = ConjR1⊑ (Trans⊑ (ConjR1⊑ a) b)
Trans⊑ (ConjR1⊑ a) (ConjR2⊑ b) = ConjR2⊑ (Trans⊑ (ConjR1⊑ a) b)
Trans⊑ (ConjR2⊑ a) (ConjL⊑ b b₁) = Trans⊑ a b₁
Trans⊑ (ConjR2⊑ a) (ConjR1⊑ b) = ConjR1⊑ (Trans⊑ (ConjR2⊑ a) b)
Trans⊑ (ConjR2⊑ a) (ConjR2⊑ b) = ConjR2⊑ (Trans⊑ (ConjR2⊑ a) b)

Context = ℕ

data Env : (Γ : Context) → Set where
  ∅ : Env 0
  _,_ : ∀ { Γ } → Env Γ → Value → Env (suc Γ)

nth : ∀{Γ} → (Γ ∋ ★) → Env Γ → Value
nth () ∅
nth Z (ρ , v) = v
nth (S x) (ρ , v) = nth x ρ

_`⊑_ : ∀{Γ} → (γ : Env Γ) → (δ : Env Γ) → Set
_`⊑_ {Γ} γ δ = ∀{k : Γ ∋ ★} → nth k γ ⊑ nth k δ

_`⊔_ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → Env Γ
∅ `⊔ ∅ = ∅
(γ , v) `⊔ (δ , v') = (γ `⊔ δ) , (v ⊔ v')

nth-join-env : ∀ {Γ} → {γ₁ : Env Γ} → {γ₂ : Env Γ}
  → ∀ {k} → nth k (γ₁ `⊔ γ₂) ≡ (nth k γ₁) ⊔ (nth k γ₂)
nth-join-env {∅} {∅} {∅} {()}
nth-join-env {Γ , ★} {γ₁ , v₁} {γ₂ , v₂} {Z} = refl
nth-join-env {Γ , ★} {γ₁ , v₁} {γ₂ , v₂} {S k} = nth-join-env {Γ}{γ₁}{γ₂}{k}

EnvConjR1⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → γ `⊑ (γ `⊔ δ)
EnvConjR1⊑ ∅ ∅ {()}
EnvConjR1⊑ (γ , v) (δ , v') {Z} = ConjR1⊑ Refl⊑
EnvConjR1⊑ (γ , v) (δ , v') {S k} = EnvConjR1⊑ γ δ {k}

EnvConjR2⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → δ `⊑ (γ `⊔ δ)
EnvConjR2⊑ ∅ ∅ {()}
EnvConjR2⊑ (γ , v) (δ , v') {Z} = ConjR2⊑ Refl⊑
EnvConjR2⊑ (γ , v) (δ , v') {S k} = EnvConjR2⊑ γ δ {k}

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

