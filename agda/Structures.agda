module Structures where

open import Variables
open import Lambda
open Lambda.ASTMod using (⟪_⟫)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_)

record Domain : Set₁ where
  infixr 7 _↦_
  infixl 5 _⊔_
  field
    Value : Set
    ⊥ : Value
    _↦_ : Value → Value → Value
    _⊔_ : Value → Value → Value

record ValueOrdering (D : Domain) : Set₁ where
  open Domain D
  infix 4 _⊑_
  field
    _⊑_ : Value → Value → Set
    ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

    ⊑-conj-L : ∀ {u v w}
        → v ⊑ u
        → w ⊑ u
          -----------
        → (v ⊔ w) ⊑ u

    ⊑-conj-R1 : ∀ {u v w}
       → u ⊑ v
         -----------
       → u ⊑ (v ⊔ w)

    ⊑-conj-R2 : ∀ {u v w}
       → u ⊑ w
         -----------
       → u ⊑ (v ⊔ w)

    ⊑-trans : ∀ {u v w}
       → u ⊑ v
       → v ⊑ w
         -----
       → u ⊑ w

    ⊑-fun : ∀ {v w v′ w′}
         → v′ ⊑ v
         → w ⊑ w′
           -------------------
         → (v ↦ w) ⊑ (v′ ↦ w′)

    ⊑-dist : ∀{v w w′}
           ---------------------------------
         → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

    ⊑-refl : ∀ {v} → v ⊑ v


{-

  The DomainAux module contains stuff that is defined/proved
  generically in terms of the Domain structure.
  
-}

module DomainAux(D : Domain) where

  open Domain D

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

  _`⊔_ : ∀ {Γ} → Env Γ → Env Γ → Env Γ
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

  _iff_ : Set → Set → Set
  P iff Q = (P → Q) × (Q → P)


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


{-

  The following caused problems with equality. -Jeremy

  record LambdaModel : Set₁ where
    field
      _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
      ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
-}

{-

  The OrderingAux module contains stuff that is defined/proved
  generically in terms of the Domain and ValueOrdering structures.
  
-}

module OrderingAux (D : Domain) (V : ValueOrdering D) where

  open Domain D
  open DomainAux D
  open ValueOrdering V
  
  ⊔⊑⊔ : ∀ {v w v′ w′}
        → v ⊑ v′  →  w ⊑ w′
          -----------------------
        → (v ⊔ w) ⊑ (v′ ⊔ w′)
  ⊔⊑⊔ d₁ d₂ = ⊑-conj-L (⊑-conj-R1 d₁) (⊑-conj-R2 d₂)

  Dist⊔↦⊔ : ∀{v v′ w w′ : Value}
          → ((v ⊔ v′) ↦ (w ⊔ w′)) ⊑ ((v ↦ w) ⊔ (v′ ↦ w′))
  Dist⊔↦⊔ = ⊑-trans ⊑-dist (⊔⊑⊔ (⊑-fun (⊑-conj-R1 ⊑-refl) ⊑-refl)
                              (⊑-fun (⊑-conj-R2 ⊑-refl) ⊑-refl))

  infixr 2 _⊑⟨⟩_ _⊑⟨_⟩_
  infix  3 _◼

  _⊑⟨⟩_ : ∀ (x : Value) {y : Value}
      → x ⊑ y
        -----
      → x ⊑ y
  x ⊑⟨⟩ x⊑y  = x⊑y

  _⊑⟨_⟩_ : ∀ (x : Value) {y z : Value}
      → x ⊑ y
      → y ⊑ z
        -----
      → x ⊑ z
  (x ⊑⟨ x⊑y ⟩ y⊑z) =  ⊑-trans x⊑y y⊑z

  _◼ : ∀ (v : Value)
        -----
      → v ⊑ v
  (v ◼) =  ⊑-refl

  _`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`⊑_ {Γ} γ δ = (x : Var Γ) → γ x ⊑ δ x

  `Refl⊑ : ∀ {Γ} {γ : Env Γ} → γ `⊑ γ
  `Refl⊑ {Γ} {γ} x = ⊑-refl {γ x}

  EnvConjR1⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → γ `⊑ (γ `⊔ δ)
  EnvConjR1⊑ γ δ x = ⊑-conj-R1 ⊑-refl

  EnvConjR2⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → δ `⊑ (γ `⊔ δ)
  EnvConjR2⊑ γ δ x = ⊑-conj-R2 ⊑-refl

  record WFDenot (Γ : ℕ) (E : Denotation Γ) : Set₁ where
    field
      ⊑-env : ∀{γ δ}{v} → E γ v → γ `⊑ δ → E δ v
      ⊑-closed : ∀{γ}{v w} → E γ v → w ⊑ v → E γ w
      ⊔-closed : ∀{γ u v} → E γ u → E γ v → E γ (u ⊔ v)


  record LambdaModelBasics
      (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
      (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
      : Set₁ where
    field
      ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
            {D′ : Denotation (suc Δ)}
          → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
          → ℱ D γ ≲ ℱ D′ δ
      ●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
              {D₁′ D₂′ : Denotation Δ}
          → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
          → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
      ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
          → WFDenot (suc Γ) D
          → ℱ D γ v → w ⊑ v → ℱ D γ w
      ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
          → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v → (D₁ ● D₂) γ w
      ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
          → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
      ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
          → WFDenot Γ D₁ → WFDenot Γ D₂
          → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
      ℱ-⊥ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} → ℱ D γ ⊥

module LambdaDenot
  (D : Domain) (V : ValueOrdering D)
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  where
  open Domain D
  open DomainAux D
  open ValueOrdering V

  open ASTMod using (`_; _⦅_⦆; cons; bind; nil; Subst)

  ℰ : ∀{Γ} → Term Γ → Denotation Γ
  ℰ {Γ} (` x) γ v = v ⊑ γ x
  ℰ {Γ} (lam ⦅ bind N nil ⦆) = ℱ (ℰ N)
  ℰ {Γ} (app ⦅ cons L (cons M nil) ⦆) = (ℰ L) ● (ℰ M)

  split : ∀ {Γ} {M : Term (suc Γ)} {δ : Env (suc Γ)} {v}
    → ℰ M δ v
      ------------------------
    → ℰ M (init δ `, last δ) v
  split {δ = δ} δMv rewrite init-last δ = δMv

  infix 3 _`⊢_↓_
  _`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
  _`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))


module DenotAux
  (D : Domain) (V : ValueOrdering D) 
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (MB : OrderingAux.LambdaModelBasics D V _●_ ℱ)
  where
  open Domain D
  open DomainAux D
  open OrderingAux D V
  open LambdaDenot D V _●_ ℱ
  open LambdaModelBasics MB

  ƛ-⊥ : ∀{Γ}{N : Term (suc Γ)}{γ : Env Γ}
      → ℰ (ƛ N) γ ⊥
  ƛ-⊥ = ℱ-⊥

{-
  cong-● : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≃ D₁′ δ → D₂ γ ≃ D₂′ δ → (D₁ ● D₂) γ ≃ (D₁′ ● D₂′) δ
  cong-● {γ = γ}{δ}{D₁}{D₂}{D₁′}{D₂′} eq1 eq2 {w} =
    ⟨ (●-≲{D₁ = D₁}{D₂}{D₁′}{D₂′} (proj₁ eq1) (proj₁ eq2)) {v = w} ,
      (●-≲{D₁ = D₁′}{D₂′}{D₁}{D₂} (proj₂ eq1) (proj₂ eq2)) {v = w} ⟩
-}
