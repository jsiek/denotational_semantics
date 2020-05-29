open import Structures
open import Var using (Var)
open import Data.Nat using (ℕ; zero; suc)
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

  _`⊑_ : Env → Env → Set
  _`⊑_ γ δ = (x : Var) → γ x ⊑ δ x

  `⊑-refl : ∀ {γ : Env} → γ `⊑ γ
  `⊑-refl {γ} x = ⊑-refl
  
  `⊑-extend : ∀ {γ δ : Env}{v w}
            → γ `⊑ δ → v ⊑ w
            → (γ `, v) `⊑ (δ `, w)
  `⊑-extend {γ} {δ} {v} {w} γ⊑δ v⊑w 0 = v⊑w
  `⊑-extend {γ} {δ} {v} {w} γ⊑δ v⊑w (suc x) = γ⊑δ x
  

  `Refl⊑ : ∀ {γ : Env} → γ `⊑ γ
  `Refl⊑ {γ} x = ⊑-refl {γ x}

  EnvConjR1⊑ : (γ : Env) → (δ : Env)
             → γ `⊑ (γ `⊔ δ)
  EnvConjR1⊑ γ δ x = ⊑-conj-R1 ⊑-refl

  EnvConjR2⊑ : (γ : Env) → (δ : Env)
             → δ `⊑ (γ `⊔ δ)
  EnvConjR2⊑ γ δ x = ⊑-conj-R2 ⊑-refl


