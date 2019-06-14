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



  _≲_ : (Value → Set) → (Value → Set) → Set
  d ≲ d' = ∀{v : Value} → d v → d' v

  ≲-refl : ∀ {d : Value → Set}
         → d ≲ d
  ≲-refl = λ z → z

  ≲-trans : ∀ {d₁ d₂ d₃ : Value → Set}
    → d₁ ≲ d₂
    → d₂ ≲ d₃
      ------- 
    → d₁ ≲ d₃
  ≲-trans m12 m23 = λ z → m23 (m12 z)

  infixr 2 _≲⟨⟩_ _≲⟨_⟩_
  infix  3 _☐

  _≲⟨⟩_ : ∀ (x : Value → Set) {y : Value → Set}
      → x ≲ y
        -----
      → x ≲ y
  x ≲⟨⟩ x≲y  = x≲y

  _≲⟨_⟩_ : ∀ (x : Value → Set) {y z : Value → Set}
      → x ≲ y
      → y ≲ z
        -----
      → x ≲ z
  (x ≲⟨ x≲y ⟩ y≲z) {v} =  ≲-trans (x≲y{v}) y≲z {v}

  _☐ : ∀ (d : Value → Set)
        -----
      → d ≲ d
  (d ☐) {v} =  ≲-refl {d}


  infix 3 _≃_

  _≃_ : ∀ {Γ} → (Denotation Γ) → (Denotation Γ) → Set
  (_≃_ {Γ} D₁ D₂) = (γ : Env Γ) → (v : Value) → D₁ γ v iff D₂ γ v

  ≃-refl : ∀ {Γ } → {M : Denotation Γ}
    → M ≃ M
  ≃-refl γ v = ⟨ (λ x → x) , (λ x → x) ⟩

  ≃-sym : ∀ {Γ } → {M N : Denotation Γ}
    → M ≃ N
      -----
    → N ≃ M
  ≃-sym eq γ v = ⟨ (proj₂ (eq γ v)) , (proj₁ (eq γ v)) ⟩

  ≃-trans : ∀ {Γ } → {M₁ M₂ M₃ : Denotation Γ}
    → M₁ ≃ M₂
    → M₂ ≃ M₃
      -------
    → M₁ ≃ M₃
  ≃-trans eq1 eq2 γ v = ⟨ (λ z → proj₁ (eq2 γ v) (proj₁ (eq1 γ v) z)) ,
                          (λ z → proj₂ (eq1 γ v) (proj₂ (eq2 γ v) z)) ⟩

  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _□

  _≃⟨⟩_ : ∀ {Γ} (x : Denotation Γ) {y : Denotation Γ}
      → x ≃ y
        -----
      → x ≃ y
  x ≃⟨⟩ x≃y  = x≃y

  _≃⟨_⟩_ : ∀ {Γ} (x : Denotation Γ) {y z : Denotation Γ}
      → x ≃ y
      → y ≃ z
        -----
      → x ≃ z
  (x ≃⟨ x≃y ⟩ y≃z) =  ≃-trans x≃y y≃z

  _□ : ∀ {Γ} (d : Denotation Γ)
        -----
      → d ≃ d
  (d □) =  ≃-refl

