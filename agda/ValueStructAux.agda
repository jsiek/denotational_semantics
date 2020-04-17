open import Utilities using (extensionality)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Structures
open import Syntax using (Var)

{-

  The ValueStructAux module contains stuff that is defined/proved
  generically in terms of the ValueStruct structure.
  
-}

module ValueStructAux(D : ValueStruct) where

  open ValueStruct D

  Env : Set
  Env = Var → Value

  Denotation : Set₁
  Denotation = Env → Value → Set

  `∅ : Env
  `∅ x = ⊥    {- ??? -}

  `⊥ : Env
  `⊥ x = ⊥

  infixl 5 _`,_

  _`,_ : Env → Value → Env
  (γ `, v) 0 = v
  (γ `, v) (suc x) = γ x

  init : Env → Env
  init γ x = γ (suc x)

  last : Env → Value
  last γ = γ 0

  init-last : (γ : Env) → γ ≡ (init γ `, last γ)
  init-last γ = extensionality lemma
    where
    lemma : ∀ (x : Var) → γ x ≡ (init γ `, last γ) x
    lemma 0      =  refl
    lemma (suc x)  =  refl

  _`⊔_ : (γ : Env) → (δ : Env) → Env
  (γ `⊔ δ) x = γ x ⊔ δ x

  _`≡_ : Env → Env → Set
  _`≡_ γ δ = (x : Var) → γ x ≡ δ x

  const-env : (x : Var) → Value → Env
  const-env x v y with x ≟ y
  ...             | yes _       = v
  ...             | no _        = ⊥

  nth-const-env : ∀{x : Var} {v} → (const-env x v) x ≡ v
  nth-const-env {x = x}
      with x ≟ x
  ... | yes eq = refl
  ... | no neq = ⊥-elim (neq refl) 

  diff-nth-const-env : ∀ {x y : Var} {v}
    → x ≢ y
      -------------------
    → const-env x v y ≡ ⊥
  diff-nth-const-env {x} {y} neq with x ≟ y
  ...  | yes eq  =  ⊥-elim (neq eq)
  ...  | no _    =  refl



