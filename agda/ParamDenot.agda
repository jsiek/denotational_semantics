open import Primitives
open import LambdaV using (Term; $; _·_; ƛ; TermV; t-var; t-lam; t-app)
open LambdaV.AST using (Var; Z; S_; `_; α_; _⦅_⦆; extensionality; Rename; Subst;
     ext; exts; rename)
open import Structures
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)


module ParamDenot
    (Value : Set)
    (domain : Domain Value)
    where


open Domain domain

import Environment
module E = Environment Value domain
open E

Sem : ℕ → Set₁
Sem Γ = (Env Γ → Value → Set)

data ℘ : ∀{P : Prim} → rep P → Value → Set where
   ℘-base : ∀{B}{b : base-rep B}
              ---------------
            → ℘ {` B} b (lit b)
   ℘-fun :  ∀{B}{P}{f : base-rep B → rep P}{k : base-rep B}{v : Value}
            → ℘ {P} (f k) v
              -----------------------------
            → ℘ {B ⇒ P} f ((lit {B} k) ↦ v)
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


data ℰ : ∀{Γ} → Term Γ → Sem Γ where
  ℰ-var : ∀ {Γ} {γ : Env Γ} {x}
        ---------------
      → ℰ (` x) γ (γ x)
  ℰ-lit : ∀{Γ}{γ : Env Γ}{P : Prim} {p : rep P} {v : Value}
        → ℘ {P} p v
          --------------------
        → ℰ ($ {Γ} {P} p) γ v
  ℰ-app : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v₁ v₂}
        → ℰ M₁ γ (v₁ ↦ v₂)  →  ℰ M₂ γ v₁
          ------------------------------
        → ℰ (M₁ · M₂) γ v₂

  ℰ-lam : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → ℰ M (γ `, v₁) v₂
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
  → v ⊑ γ x
var-inv (ℰ-var) = Refl⊑
var-inv (ℰ-⊔ d₁ d₂) = ConjL⊑ (var-inv d₁) (var-inv d₂)
var-inv (ℰ-⊑ d lt) = Trans⊑ lt (var-inv d)

Denotation : ℕ → Set₁
Denotation Γ = (Env Γ → Value → Set)

{-
ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)
-}

{-
lambda-inversion
  : ∀{Γ} {γ : Env Γ} {M : Term Γ} {N : Term (suc Γ)} {v v₁ v₂ : Value}
  → ℰ M γ v → M ≡ (ƛ N) → v ≡ (v₁ ↦ v₂)
    -----------------------------------
  → ℰ N (γ `, v₁) v₂
lambda-inversion {v₁ = v₁} {v₂} ℰ-var ()
lambda-inversion {v₁ = v₁} {v₂} (ℰ-lit x) ()
lambda-inversion {v₁ = v₁} {v₂} (ℰ-app d d₁) ()
lambda-inversion {v₁ = v₁} {v₂} (ℰ-lam{v₁ = u₁}{v₂ = u₂} d) refl eq
    with Cong↦ eq 
... | ⟨ eq1 , eq2 ⟩ rewrite eq1 | eq2 =
    d
lambda-inversion {v₁ = v₁} {v₂} ℰ-⊥ eq1 eq2 = ⊥-elim (⊥≢↦ eq2)
lambda-inversion {v₁ = v₁} {v₂} (ℰ-⊔ d d₁) eq1 eq2 = ⊥-elim (⊔≢↦ eq2)
lambda-inversion {v₁ = v₁} {v₂} (ℰ-⊑ ℰMv₁ v⊑v₁) eq1 eq2 =

  {!!}
-}











rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
  → ℰ M γ v
    ---------------------
  → ℰ (rename ρ M) δ v
rename-pres ρ lt (ℰ-lit p) = ℰ-lit p
rename-pres {Γ}{Δ}{c}{γ}{δ}{M} ρ lt (ℰ-var {x = x}) =
   ℰ-⊑ (ℰ-var{Δ}{δ}{ρ x}) (lt x)
rename-pres ρ lt (ℰ-app d d₁) =
   ℰ-app (rename-pres ρ lt d) (rename-pres ρ lt d₁) 
rename-pres ρ lt (ℰ-lam d) =
   ℰ-lam (rename-pres (ext ρ) (ext-nth ρ lt) d)
rename-pres ρ lt ℰ-⊥ = ℰ-⊥
rename-pres ρ lt (ℰ-⊔ d d₁) =
   ℰ-⊔ (rename-pres ρ lt d) (rename-pres ρ lt d₁)
rename-pres ρ lt (ℰ-⊑ d lt′) =
   ℰ-⊑ (rename-pres ρ lt d) lt′


`ℰ : ∀{Δ Γ} → Subst Γ Δ → Env Δ → Env Γ → Set
`ℰ {Δ}{Γ} σ δ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))

subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (σ : Subst Γ Δ)
  → `ℰ σ δ γ
   ------------------------------
  → `ℰ (exts σ) (δ `, v) (γ `, v)
subst-ext σ d Z = ℰ-var
subst-ext σ d (S x′) = rename-pres S_ (λ _ → Refl⊑) (d x′)

