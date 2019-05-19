module ValueBCD where

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
  Bot⊑Bot : ⊥ ⊑ ⊥
  Bot⊑Fun : ∀ {v v'} → ⊥ ⊑ v ↦ v'
  Lit⊑ : ∀{B k} → lit {B} k ⊑ lit {B} k
  Fun⊑ : ∀ {v₁ v₂ v₁' v₂'}
       → v₁' ⊑ v₁  →  v₂ ⊑ v₂'
         -----------------------
       → (v₁ ↦ v₂) ⊑ (v₁' ↦ v₂')
  Dist⊑ : ∀{v₁ v₂ v₃}
         --------------------------------------
       → v₁ ↦ (v₂ ⊔ v₃) ⊑ (v₁ ↦ v₂) ⊔ (v₁ ↦ v₃)
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

  Trans⊑ : ∀ {v₁ v₂ v₃}
     → v₁ ⊑ v₂ → v₂ ⊑ v₃
       -----------------
     → v₁ ⊑ v₃


Refl⊑ : ∀ {v} → v ⊑ v
Refl⊑ {⊥} = Bot⊑Bot
Refl⊑ {lit x} = Lit⊑
Refl⊑ {v ↦ v₁} = Fun⊑ Refl⊑ Refl⊑
Refl⊑ {v ⊔ v₁} = ConjL⊑ (ConjR1⊑ Refl⊑) (ConjR2⊑ Refl⊑)


Conj⊑Conj : ∀ {v₁ v₂ v₁' v₂'}
      → v₁ ⊑ v₁'  →  v₂ ⊑ v₂'
        -----------------------
      → (v₁ ⊔ v₂) ⊑ (v₁' ⊔ v₂')
Conj⊑Conj d₁ d₂ = ConjL⊑ (ConjR1⊑ d₁) (ConjR2⊑ d₂)


Dist⊔↦⊔ : ∀{v₁ v₁' v₂ v₂' : Value}
        → (v₁ ⊔ v₁') ↦ (v₂ ⊔ v₂') ⊑ (v₁ ↦ v₂) ⊔ (v₁' ↦ v₂')
Dist⊔↦⊔{v₁}{v₁'}{v₂}{v₂'} =
    Trans⊑ (Dist⊑{v₁ = v₁ ⊔ v₁'}{v₂ = v₂}{v₃ = v₂'})
           (Conj⊑Conj (Fun⊑ (ConjR1⊑ Refl⊑) Refl⊑)
                      (Fun⊑ (ConjR2⊑ Refl⊑) Refl⊑))


Dist⊔↦⊑↦⊔ : ∀{v₁ v₂ v₄ : Value}
         → (v₁ ↦ v₂) ⊔ (v₁ ↦ v₄) ⊑ v₁ ↦ (v₂ ⊔ v₄)
Dist⊔↦⊑↦⊔ = ConjL⊑ (Fun⊑ Refl⊑ (ConjR1⊑ Refl⊑))
                   (Fun⊑ Refl⊑ (ConjR2⊑ Refl⊑))


⊔⊑L : ∀{v₁ v₂ v : Value}
    → v₁ ⊔ v₂ ⊑ v
    → v₁ ⊑ v
⊔⊑L (ConjL⊑ d d₁) = d
⊔⊑L (ConjR1⊑ d) = ConjR1⊑ (⊔⊑L d)
⊔⊑L (ConjR2⊑ d) = ConjR2⊑ (⊔⊑L d)
⊔⊑L (Trans⊑ {v₁ ⊔ v₂} d₁ d₂) = Trans⊑ (⊔⊑L d₁) d₂


⊔⊑R : ∀{v₁ v₂ v : Value}
    → v₁ ⊔ v₂ ⊑ v
    → v₂ ⊑ v
⊔⊑R (ConjL⊑ d d₁) = d₁
⊔⊑R (ConjR1⊑ d) = ConjR1⊑ (⊔⊑R d)
⊔⊑R (ConjR2⊑ d) = ConjR2⊑ (⊔⊑R d)
⊔⊑R (Trans⊑ {v₁ ⊔ v₂} d₁ d₂) = Trans⊑ (⊔⊑R d₁) d₂


data Env : (Γ : Context) → Set where
  ∅ : Env ∅
  _,_ : ∀ { Γ } → Env Γ → Value → Env (Γ , ★)

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

