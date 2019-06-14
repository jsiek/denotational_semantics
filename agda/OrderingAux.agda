open import Variables
open import Structures
import ValueStructAux

{-

  The OrderingAux module contains stuff that is defined/proved
  generically in terms of the ValueStruct and ValueOrdering structures.
  
-}

module OrderingAux (D : ValueStruct) (V : ValueOrdering D) where

  open ValueStruct D
  open ValueStructAux D
  open ValueOrdering V
  
  ⊔⊑⊔ : ∀ {v w v′ w′}
        → v ⊑ v′  →  w ⊑ w′
          --------------------------
        → v ⊔ w ⊑ v′ ⊔ w′
  ⊔⊑⊔ d₁ d₂ = ⊑-conj-L (⊑-conj-R1 d₁) (⊑-conj-R2 d₂)

  Dist⊔↦⊔ : ∀{v v′ w w′ : Value}
          → (v ⊔ v′) ↦ (w ⊔ w′) ⊑ v ↦ w ⊔ v′ ↦ w′
  Dist⊔↦⊔ =
     ⊑-trans ⊑-dist (⊔⊑⊔ (⊑-fun (⊑-conj-R1 ⊑-refl) ⊑-refl)
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

  EnvConjR1⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ)
             → γ `⊑ (γ `⊔ δ)
  EnvConjR1⊑ γ δ x = ⊑-conj-R1 ⊑-refl

  EnvConjR2⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ)
             → δ `⊑ (γ `⊔ δ)
  EnvConjR2⊑ γ δ x = ⊑-conj-R2 ⊑-refl


