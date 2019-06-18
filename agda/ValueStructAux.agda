open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Variables
open import Structures

{-

  The ValueStructAux module contains stuff that is defined/proved
  generically in terms of the ValueStruct structure.
  
-}

module ValueStructAux(D : ValueStruct) where

  open ValueStruct D

  Env : ℕ → Set
  Env Γ = Var Γ → Value

  Denotation : ℕ → Set₁
  Denotation Γ = Env Γ → Value → Set

  `∅ : Env zero
  `∅ ()

  `⊥ : ∀ {Γ} → Env Γ
  `⊥ x = ⊥

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

  _`⊔_ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → Env Γ
  (γ `⊔ δ) x = γ x ⊔ δ x

  _`≡_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`≡_ {Γ} γ δ = (x : Var Γ) → γ x ≡ δ x

  const-env : ∀{Γ} → (x : Var Γ) → Value → Env Γ
  const-env x v y with x var≟ y
  ...             | yes _       = v
  ...             | no _        = ⊥

  nth-const-env : ∀{Γ} {x : Var Γ} {v} → (const-env x v) x ≡ v
  nth-const-env {x = x} rewrite var≟-refl x = refl

  diff-nth-const-env : ∀{Γ} {x y : Var Γ} {v}
    → x ≢ y
      -------------------
    → const-env x v y ≡ ⊥
  diff-nth-const-env {Γ} {x} {y} neq with x var≟ y
  ...  | yes eq  =  ⊥-elim (neq eq)
  ...  | no _    =  refl



