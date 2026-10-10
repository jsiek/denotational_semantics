open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Utilities using (_iff_)

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

{-
  Alternative that starts with induction on P.
-}
℘′ : ∀{P : Prim} → rep P → Value → Set
℘′ {base B} k ⊥ = ⊤
℘′ {base B} k (const {B′} k′)
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′
... | no neq = Bot
℘′ {base B} k (v ↦ w) = Bot
℘′ {base B} k (u ⊔ v) = ℘′ {base B} k u × ℘′ {base B} k v
℘′ {B ⇒ P} f ⊥ = ⊤
℘′ {B ⇒ P} f (const k′) = Bot
℘′ {B ⇒ P} f (v ↦ w) = Σ[ k ∈ base-rep B ] const {B} k ⊑ v × ℘′{P} (f k) w
℘′ {B ⇒ P} f (u ⊔ v) = ℘′ {B ⇒ P} f u × ℘′ {B ⇒ P} f v
