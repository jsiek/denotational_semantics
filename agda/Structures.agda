module Structures where

open import Variables
open import Primitives

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Data.List
open import Function using (_∘_)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)

record ValueStruct : Set₁ where
  infixr 7 _↦_
  infixl 5 _⊔_
  field
    Value : Set
    ⊥ : Value
    _↦_ : Value → Value → Value
    _⊔_ : (u : Value) → (v : Value) → Value

record ValueOrdering (D : ValueStruct) : Set₁ where
  open ValueStruct D
  infix 4 _⊑_
  field
    _⊑_ : Value → Value → Set

    ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

    ⊑-conj-L : ∀ {u v w}
        → v ⊑ u
        → w ⊑ u
          -----------
        → v ⊔ w ⊑ u

    ⊑-conj-R1 : ∀ {u v w}
       → u ⊑ v
         ------------------
       → u ⊑ v ⊔ w

    ⊑-conj-R2 : ∀ {u v w}
       → u ⊑ w
         -----------
       → u ⊑ v ⊔ w

    ⊑-trans : ∀ {u v w}
       → u ⊑ v
       → v ⊑ w
         -----
       → u ⊑ w

    ⊑-fun : ∀ {v w v′ w′}
         → v′ ⊑ v
         → w ⊑ w′
           -------------------
         → v ↦ w ⊑ v′ ↦ w′
         
    ⊑-refl : ∀ {v} → v ⊑ v

    ⊑-dist : ∀{v w w′}
           -----------------------------
         → v ↦ (w ⊔ w′) ⊑ v ↦ w ⊔ v ↦ w′


record Consistent (D : ValueStruct) (V : ValueOrdering D) : Set₁ where
  open ValueStruct D
  open ValueOrdering V
  infix 4 _~_
  field
    _~_ : Value → Value → Set
    ~-⊑ : ∀{u v u′ v′}  → u ~ v → u′ ⊑ u → v′ ⊑ v → u′ ~ v′
    ~-↦-cong : ∀{u v u′ v′} → u ~ u′ → v ~ v′ → (u ↦ v) ~ (u′ ↦ v′)
    
    ~-refl : ∀{v} → v ~ v
    
    ~-↦ : ∀{v w v′ w′} → (v ↦ w ~ v′ ↦ w′) → ((v ~ v′ × w ~ w′) ⊎ ¬ (v ~ v′))
    
    ~-⊔-cong : ∀{u v u′ v′}
             → (u ~ u′) → (u ~ v′)
             → (v ~ u′) → (v ~ v′)
             → u ⊔ v ~ u′ ⊔ v′
             


{-

  The following caused problems with equality. -Jeremy

  record LambdaModel : Set₁ where
    field
      _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
      ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
-}


