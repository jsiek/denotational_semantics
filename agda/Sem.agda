module Sem where

open import Lambda
open import ValueBCD

open import Data.Product renaming (_,_ to ⟨_,_⟩)

Sem : Context → Set₁
Sem Γ = (Env Γ → Value → Set)

infix 3 _≃_

_≃_ : ∀ {Γ} → (Sem Γ) → (Sem Γ) → Set
_≃_ {Γ} D₁ D₂ = ∀{γ : Env Γ} {v} → D₁ γ v iff D₂ γ v

≃-refl : ∀ {Γ : Context} → {M : Sem Γ}
  → M ≃ M
≃-refl = ⟨ (λ x → x) , (λ x → x) ⟩

≃-sym : ∀ {Γ : Context} → {M : Sem Γ} → {N : Sem Γ}
  → M ≃ N
    -----
  → N ≃ M
≃-sym eq = ⟨ proj₂ eq , proj₁ eq ⟩

≃-trans : ∀ {Γ : Context} → {M₁ : Sem Γ} → {M₂ : Sem Γ} → {M₃ : Sem Γ}
  → M₁ ≃ M₂ → M₂ ≃ M₃
    -----------------
  → M₁ ≃ M₃
≃-trans eq1 eq3 =
  ⟨ (λ z → proj₁ eq3 (proj₁ eq1 z)) , (λ z → proj₂ eq1 (proj₂ eq3 z)) ⟩

data ℘ : ∀{P : Prim} → rep P → Value → Set where
   ℘-base : ∀{B}{b : base-rep B}
              ---------------
            → ℘ {` B} b (lit b)
   ℘-fun :  ∀{B}{P}{f : base-rep B → rep P}{k : base-rep B}{v v₁ v₂ : Value}
            → ℘ {P} (f k) v  → lit {B} k ⊑ v₁  →  v₂ ⊑ v
              ------------------------------------------
            → ℘ {B ⇒ P} f (v₁ ↦ v₂)
   ℘-⊔ :  ∀{P : Prim}{p : rep P}{v₁ v₂ : Value}
            → ℘ {P} p v₁  →  ℘ {P} p v₂
              -------------------------
            → ℘ {P} p (v₁ ⊔ v₂)
   ℘-⊥ :  ∀{P : Prim}{p : rep P}
              ---------
            → ℘ {P} p ⊥
   ℘-⊑ :  ∀{P : Prim}{p : rep P}{v₁ v₂ : Value}
            → ℘ {P} p v₁  →  v₂ ⊑ v₁
              ----------------------
            → ℘ {P} p v₂


data ℰ : ∀{Γ} → Γ ⊢ ★ → Sem Γ where
  ℰ-var : ∀ {Γ} {γ : Env Γ} {x v}
                   → v ⊑ nth x γ
        -----------
      → ℰ (` x) γ v
  ℰ-lit : ∀{Γ}{γ : Env Γ}{P : Prim} {p : rep P} {v : Value}
        → ℘ {P} p v
          --------------------
        → ℰ ($_ {Γ} {P} p) γ v
  ℰ-app : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v v₁ v₂}
        → ℰ M₁ γ (v₁ ↦ v₂)  →  ℰ M₂ γ v₁   → v ⊑ v₂
          ----------------------------------
        → ℰ (M₁ · M₂) γ v

  ℰ-lam : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → ℰ M (γ , v₁) v₂
          -------------------
        → ℰ (ƛ M) γ (v₁ ↦ v₂)

  ℰ-⊥ : ∀ {Γ} {γ : Env Γ} {M}
          -----------
        → ℰ (ƛ M) γ ⊥

  ℰ-⊔ : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → ℰ M γ v₁  →  ℰ M γ v₂
          ---------------------
        → ℰ M γ (v₁ ⊔ v₂)

  ℰ-⊑ : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → ℰ M γ v₁  →  v₂ ⊑ v₁
          ---------------------
        → ℰ M γ v₂

var-inv : ∀ {Γ v x} {γ : Env Γ}
  → ℰ (` x) γ v
    -------------------
  → v ⊑ nth x γ
var-inv (ℰ-var lt) = lt
var-inv (ℰ-⊔ d₁ d₂) = ConjL⊑ (var-inv d₁) (var-inv d₂)
var-inv (ℰ-⊑ d lt) = Trans⊑ lt (var-inv d)

prim-inv : ∀ {Γ v} {γ : Env Γ}{P : Prim}{p : rep P}
  → ℰ ($_ {Γ}{P} p) γ v
    -----------------------------------
  → ℘ {P} p v
prim-inv (ℰ-lit{v = v} d) = d
prim-inv (ℰ-⊔ d d₁) = ℘-⊔ (prim-inv d) (prim-inv d₁)
prim-inv (ℰ-⊑ d lt) = ℘-⊑ (prim-inv d) lt

