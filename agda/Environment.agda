open import Structures
open import Data.Nat using (ℕ; zero; suc)
open import LambdaV using (Term; $; _·_; ƛ)
open LambdaV.AST using (Var; Z; S_; `_; extensionality; Rename; Subst; ext)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Function using (_∘_)


module Environment
    (Value : Set)
    (domain : Domain Value)
    where

open Domain domain

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

_`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
_`⊑_ {Γ} γ δ = ∀ (x : Var Γ) → γ x ⊑ δ x

ext-nth : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
    ------------------------------
  → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
ext-nth ρ lt Z = Refl⊑
ext-nth ρ lt (S n′) = lt n′
