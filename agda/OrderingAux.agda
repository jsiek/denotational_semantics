open import Structures
open import DomainAux

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
        → {c1 : v ~ w}{c2 : v′ ~ w′}
          --------------------------
        → ((v ⊔ w){c1}) ⊑ ((v′ ⊔ w′){c2})
  ⊔⊑⊔ d₁ d₂ {vw}{vw′} = ⊑-conj-L (⊑-conj-R1 d₁) (⊑-conj-R2 d₂)

  Dist⊔↦⊔ : ∀{v v′ w w′ : Value}
          → {c1 : v ~ v′} → {c2 : w ~ w′}
          → (((v ⊔ v′){c1}) ↦ ((w ⊔ w′) {c2})) ⊑ ((v ↦ w) ⊔ (v′ ↦ w′))
                                                    {~-↦-cong c1 c2}
  Dist⊔↦⊔ {v~v′} {w~w′} =
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
             → {c : γ ~′ δ}
             → γ `⊑ ((γ `⊔ δ){c})
  EnvConjR1⊑ γ δ x = ⊑-conj-R1 ⊑-refl

  EnvConjR2⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ)
             → {c : γ ~′ δ}
             → δ `⊑ ((γ `⊔ δ){c})
  EnvConjR2⊑ γ δ x = ⊑-conj-R2 ⊑-refl

  ~′-refl : ∀{Γ}{γ : Env Γ} → γ ~′ γ
  ~′-refl {Γ}{γ}{x} = ~-refl

