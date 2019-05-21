module Structures where

open import Primitives
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty renaming (⊥ to Bot)

record Domain (D : Set) : Set₁ where
  field
    ⊥ : D
    lit : ∀{B : Base} → base-rep B → D
    _↦_ : D → D → D
    _⊔_ : D → D → D
    _⊑_ : D → D → Set

    ⊥≢↦ : ∀{u v} → ⊥ ≡ u ↦ v → Bot
    ⊔≢↦ : ∀{u v u' v'} → u ⊔ v ≡ u' ↦ v' → Bot
    Cong↦ : ∀{u v u' v'} → u ↦ v ≡ u' ↦ v' → u ≡ u' × v ≡ v'
    Refl⊑ : ∀ {v} → v ⊑ v
    ConjL⊑ : ∀ {u v w} → v ⊑ u → w ⊑ u → (v ⊔ w) ⊑ u
    Trans⊑ : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
