module Structures where

open import Primitives
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty renaming (⊥ to Bot)
import LambdaV
open LambdaV.ASTMod using (Var)

open import Data.Nat using (ℕ; zero; suc)

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

record Domain (D : Set) : Set₁ where
  field
    ⊥ : D
{-
    lit : ∀{B : Base} → base-rep B → D
-}
    _↦_ : D → D → D
    _⊔_ : D → D → D
    _⊑_ : D → D → Set

    ⊥≢↦ : ∀{u v} → ⊥ ≡ u ↦ v → Bot
    ⊔≢↦ : ∀{u v u' v'} → u ⊔ v ≡ u' ↦ v' → Bot
    Cong↦ : ∀{u v u' v'} → u ↦ v ≡ u' ↦ v' → u ≡ u' × v ≡ v'
    Refl⊑ : ∀ {v} → v ⊑ v
    ConjL⊑ : ∀ {u v w} → v ⊑ u → w ⊑ u → (v ⊔ w) ⊑ u
    Trans⊑ : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w

Env : ℕ → Set → Set
Env Γ D = ∀ (x : Var Γ) → D

Denotation : ℕ → Set → Set₁
Denotation Γ D = (Env Γ D → D → Set)

record LambdaModel (D : Set) : Set₂ where
  field
    ℱ : ∀{Γ} → Denotation (suc Γ) D → Denotation Γ D
    _●_ : ∀{Γ} → Denotation Γ D → Denotation Γ D → Denotation Γ D
    _⊑_ : D → D → Set
{-
    _≃_ : ∀ {Γ} → (Denotation Γ D) → (Denotation Γ D) → Set

    ≃-refl : ∀ {Γ} → {D : Denotation Γ D} → D ≃ D
    ≃-sym : ∀ {Γ} → {M N : Denotation Γ D} → M ≃ N → N ≃ M
    ≃-trans : ∀ {Γ} → {M₁ M₂ M₃ : Denotation Γ D} → M₁ ≃ M₂ → M₂ ≃ M₃ → M₁ ≃ M₃
-}
