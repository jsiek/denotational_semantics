module Structures where

open import Primitives
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty renaming (⊥ to Bot)
import LambdaV
open LambdaV.ASTMod using (Rename; Var; Z; S_; ext; extensionality)

open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_)

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


module LambdaModelMod
  (D : Set)
  (_⊑_ : D → D → Set)
  (_⊔_ : D → D → D)
  where

  Env : ℕ → Set
  Env Γ = ∀ (x : Var Γ) → D

  `∅ : Env zero
  `∅ ()

  infixl 5 _`,_

  _`,_ : ∀ {Γ} → Env Γ → D → Env (suc Γ)
  (γ `, v) Z = v
  (γ `, v) (S x) = γ x

  init : ∀ {Γ} → Env (suc Γ) → Env Γ
  init γ x = γ (S x)

  last : ∀ {Γ} → Env (suc Γ) → D
  last γ = γ Z

  init-last : ∀ {Γ} → (γ : Env (suc Γ)) → γ ≡ (init γ `, last γ)
  init-last {Γ} γ = extensionality lemma
    where
    lemma : ∀ (x : Var (suc Γ)) → γ x ≡ (init γ `, last γ) x
    lemma Z      =  refl
    lemma (S x)  =  refl

  _`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`⊑_ {Γ} γ δ = ∀ (x : Var Γ) → γ x ⊑ δ x

  record Denotation (Γ : ℕ) : Set₁ where
    field
      E : Env Γ → D → Set
      up-env : ∀{γ δ}{v} → E γ v → γ `⊑ δ → E δ v
      ⊑-closed : ∀{γ}{v w} → E γ v → w ⊑ v → E γ w
      ⊔-closed : ∀{γ u v} → E γ u → E γ v → E γ (u ⊔ v)
      
  record LambdaModel : Set₁ where
    field
      var : ∀{Γ} → Var Γ → Denotation Γ
      ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
      _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
      Refl⊑ : ∀ {v} → v ⊑ v
      Trans⊑ : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
      ConjL⊑ : ∀ {u v w} → v ⊑ u → w ⊑ u → (v ⊔ w) ⊑ u
