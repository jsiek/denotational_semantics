module Rename where

open import Lambda
open import ValueBCD
open import Sem

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit

ext-nth : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
    -----------------------------------------------------------------
  → (∀ {n : Γ , ★ ∋ ★} → nth n (γ , v) ⊑ nth ((ext ρ) n) (δ , v))
ext-nth ρ lt {Z} = Refl⊑
ext-nth ρ lt {S n'} = lt

rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (ρ : Rename Γ Δ)
  → (∀ {n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
  → ℰ M γ v
    ----------------------------------------
  → ℰ (rename ρ M) δ v
rename-pres ρ nth-eq (ℰ-var{x = x} lt) =  ℰ-var (Trans⊑ lt (nth-eq {x}))
rename-pres ρ nth-eq (ℰ-lit d) = ℰ-lit d
rename-pres ρ nth-eq (ℰ-app d d₁ lt2) =
  ℰ-app (rename-pres ρ nth-eq d) (rename-pres ρ nth-eq d₁) lt2
rename-pres ρ nth-eq (ℰ-lam d) =
  ℰ-lam (rename-pres (ext ρ) (λ {n} → ext-nth ρ nth-eq {n}) d)
rename-pres ρ nth-eq ℰ-⊥ = ℰ-⊥
rename-pres ρ nth-eq (ℰ-⊔ d d₁) =
  ℰ-⊔ (rename-pres ρ nth-eq d) (rename-pres ρ nth-eq d₁)
rename-pres ρ nth-eq (ℰ-⊑ d lt) =
  ℰ-⊑ (rename-pres ρ nth-eq d) lt

rename-inc-pres : ∀ {Γ v' v} {γ : Env Γ} {M : Γ ⊢ ★}
    → ℰ M γ v
    → ℰ (rename (λ {A} → λ k → S k) M) (γ , v') v
rename-inc-pres d = rename-pres (λ {A} → λ k → S k) (λ {n} → Refl⊑) d

is-identity : ∀ {Γ} (id : ∀{A} → Γ ∋ A → Γ ∋ A) → Set
is-identity {Γ} id = (∀ {x : Γ ∋ ★} → id {★} x ≡ x)

rename-id : ∀ {Γ} {M : Γ ⊢ ★} {id : ∀{A} → Γ ∋ A → Γ ∋ A}
  → is-identity id
    ---------------
  → rename id M ≡ M
rename-id {M = ` x} eq = cong `_ (eq {x})
rename-id {M = $_ k} eq = cong $_ refl
rename-id {M = ƛ M₁}{id = id} eq = cong ƛ_ (rename-id {M = M₁} ext-id)
  where
  ext-id : is-identity (ext id)
  ext-id {Z} = refl
  ext-id {S x} = cong S_ eq
rename-id {M = M · M₁} eq = cong₂ _·_ (rename-id eq) (rename-id eq)

var-id : ∀ {Γ A} → (Γ ∋ A) → (Γ ∋ A)
var-id {A} x = x

var-id-id : ∀ {Γ} → is-identity {Γ} var-id
var-id-id = refl

Env⊑ : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
  → ℰ M γ v  →  γ `⊑ δ
    --------------------
  → ℰ M δ v
Env⊑{Γ}{γ}{δ}{M}{v} d lt
      with rename-pres var-id lt d
... | d' rewrite rename-id {Γ}{M}{var-id} (var-id-id {Γ}) = d'


up-env : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
  → ℰ M (γ , u₁) v  →  u₁ ⊑ u₂
    ----------------------------
  → ℰ M (γ , u₂) v
up-env{Γ}{γ}{M}{v}{u₁}{u₂} d lt = Env⊑ d (λ {k} → nth-le lt {k})
  where
  nth-le : u₁ ⊑ u₂ → (γ , u₁) `⊑ (γ , u₂)
  nth-le lt {Z} = lt
  nth-le lt {S n} = Refl⊑

