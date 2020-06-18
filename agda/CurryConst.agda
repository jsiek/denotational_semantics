open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)

module CurryConst where

open import Primitives
open import ValueConst
open import ValueStructAux value_struct

ℱ : Denotation → Denotation
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (const k) = Bot
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)

℘ : ∀{P : Prim} → rep P → Value → Set
℘ {P} k (const {B′} k′)
    with P
... | B ⇒ P′ = Bot
... | base B 
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′
... | no neq = Bot
℘ {P} k ⊥ = ⊤
℘ {P} f (v ↦ w)
    with P
... | base B = Bot
... | B ⇒ P′ = Σ[ k ∈ base-rep B ] (const {B} k ⊑ v × ℘ {P′} (f k) w)
℘ {P} f (u ⊔ v) = ℘ {P} f u × ℘ {P} f v


open import Data.List using (List; []; _∷_)
open import Agda.Primitive using (Level; lzero; lsuc)

module Experiment (Op : Set) (sig : Op → List ℕ) where

  {- Check the 𝐹-cong requirement needed for subst preserves denot
     fold. (See Experiment module in LambdaDenot.)  -}

  open import Fold Op sig
  open RelBind {lsuc lzero}{Value}{Value → Set}{Value}{Value → Set} _≡_ _≡_

  𝐹 : (Value → Value → Set) → (Value → Set)
  𝐹 f ⊥ = ⊤
  𝐹 f (const k) = Bot
  𝐹 f (v ↦ w) = f v w
  𝐹 f (u ⊔ v) = 𝐹 f u × 𝐹 f v
  
  postulate
    extensionality : ∀ {ℓ : Level}{A : Set}{B : Set ℓ} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  𝐹-cong : ∀ {f g : Bind Value (Value → Set) 1}
         → _⩳_ {b = 1} f g   →   𝐹 f ≡ 𝐹 g
  𝐹-cong {f}{g} f=g = extensionality {lsuc lzero} G
      where
      G : (v : Value) → 𝐹 f v ≡ 𝐹 g v
      G ⊥ = refl
      G (const k) = refl
      G (v ↦ w) rewrite f=g {v}{v} refl = refl
      G (u ⊔ v) = cong₂ _×_ (G u) (G v)
