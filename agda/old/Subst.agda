module Subst where

open import Lambda
open import ValueBCD
open import Sem
open import Rename


Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A


_⊨_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
_⊨_↓_ {Δ}{Γ} δ σ γ = (∀{k : Γ ∋ ★} → ℰ (σ k) δ (nth k γ))


subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (σ : Subst Γ Δ)  →  δ ⊨ σ ↓ γ
   ------------------------------
  → (δ , v) ⊨ exts σ ↓ (γ , v)
subst-ext{v = v} σ d {Z} = ℰ-var Refl⊑
subst-ext{Γ}{Δ}{v}{γ}{δ} σ d {S x'} =
  rename-pres (λ {A} → S_) (λ {n} → Refl⊑) (d {x'})


subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (σ : Subst Γ Δ)  →  δ ⊨ σ ↓ γ  →  ℰ M γ v
    -----------------------------------------
  → ℰ (subst σ M) δ v
subst-pres σ s (ℰ-var {x = x} lt) = ℰ-⊑ (s {x}) lt
subst-pres σ s (ℰ-lit d) = (ℰ-lit d)
subst-pres σ s (ℰ-app d₁ d₂ lt2) =
   ℰ-app (subst-pres σ s d₁) (subst-pres σ s d₂) lt2
subst-pres σ s (ℰ-lam d) =
   ℰ-lam (subst-pres (λ {A} → exts σ) (λ {x} → subst-ext σ s {x}) d)
subst-pres σ s ℰ-⊥ = ℰ-⊥
subst-pres σ s (ℰ-⊔ d₁ d₂) =
   ℰ-⊔ (subst-pres σ s d₁) (subst-pres σ s d₂)
subst-pres σ s (ℰ-⊑ d lt) = ℰ-⊑ (subst-pres σ s d) lt


substitution : ∀ {Γ} {γ : Env Γ} {M N v₁ v₂}
   → ℰ M (γ , v₁) v₂  →  ℰ N γ v₁
     ----------------------------
   → ℰ (M [ N ]) γ v₂   
substitution{Γ}{γ}{M}{N}{v₁}{v₂} dm dn =
  subst-pres (subst-zero N) sub-z-ok dm
  where
  sub-z-ok : (∀ {y : Γ , ★ ∋ ★} → ℰ ((subst-zero N) y) γ (nth y (γ , v₁)))
  sub-z-ok {Z} = dn
  sub-z-ok {S y'} = ℰ-var Refl⊑
