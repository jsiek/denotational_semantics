open import LambdaV
open LambdaV.AST using (Var; Z; S_; `_; extensionality)

module ParamDenot
    (Value : Set)
    (⊥ : Value)
    (lit : ∀{B : Base} → base-rep B → Value)
    (_↦_ : Value → Value → Value)
    (_⊔_ : Value → Value → Value)
    (_⊑_ : Value → Value → Set)
    where

open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)


Env : ℕ → Set
Env Γ = ∀ (x : Var Γ) → Value

`∅ : Env zero
`∅ ()

infixl 5 _`,_

_`,_ : ∀ {Γ} → Env Γ → Value → Env (suc Γ)
(γ `, v) Z = v
(γ `, v) (S x) = γ x

init : ∀ {Γ} → Env (suc Γ) → Env Γ
init γ x = γ (S x)

last : ∀ {Γ} → Env (suc Γ) → Value
last γ = γ Z

init-last : ∀ {Γ} → (γ : Env (suc Γ)) → γ ≡ (init γ `, last γ)
init-last {Γ} γ = extensionality lemma
  where
  lemma : ∀ (x : Var (suc Γ)) → γ x ≡ (init γ `, last γ) x
  lemma Z      =  refl
  lemma (S x)  =  refl

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
