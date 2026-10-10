module ITRS where

open import Substitution using (_•_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (tt; ⊤)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary using (¬_)

{-------------------------------------------------------------------------------
   Denotational Values
-------------------------------------------------------------------------------}

infixr 7 _↦_
infixl 6 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : (u : Value) → (v : Value) → Value

{-------------------------------------------------------------------------------
   Value Ordering and Auxiliary Definitions
-------------------------------------------------------------------------------}

infix 5 _∈_
_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ v ↦ w = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w

infix 5 _⊆_
_⊆_ : Value → Value → Set
v ⊆ w = ∀{u} → u ∈ v → u ∈ w

AllFun : (u : Value) → Set
AllFun ⊥ = Bot
AllFun (v ↦ w) = ⊤
AllFun (u ⊔ v) = AllFun u × AllFun v 

dom : (u : Value) → ∀{a : AllFun u } → Value
dom ⊥ {()}
dom (v ↦ w) = v
dom (u ⊔ v) { ⟨ fu , fv ⟩ } = dom u {fu} ⊔ dom v {fv}

cod : (u : Value) → ∀{a : AllFun u} → Value
cod ⊥ {()}
cod (v ↦ w) = w
cod (u ⊔ v) { ⟨ fu , fv ⟩ } = cod u {fu} ⊔ cod v {fv}

infix 4 _⊑_
data _⊑_ : Value → Value → Set where
  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v
  ⊑-conj-L : ∀ {u v w} → v ⊑ u → w ⊑ u → v ⊔ w ⊑ u
  ⊑-conj-R1 : ∀ {u v w} → u ⊑ v → u ⊑ v ⊔ w
  ⊑-conj-R2 : ∀ {u v w} → u ⊑ w → u ⊑ v ⊔ w
  ⊑-fun : ∀ {u u′ v w} → u′ ⊆ u → (fu′ : AllFun u′)
       → dom u′ {fu′} ⊑ v → w ⊑ cod u′ {fu′}
       → v ↦ w ⊑ u

{------------------------------------------------------------------------------
 Consistency
 -----------------------------------------------------------------------------}

infix 4 _~_
_~_ : Value → Value → Set
⊥ ~ v = ⊤
v ↦ w ~ ⊥ = ⊤
v ↦ w ~ v′ ↦ w′ = (v ~ v′ × w ~ w′) ⊎ ¬ (v ~ v′)
v ↦ w ~ (u₁ ⊔ u₂) = v ↦ w ~ u₁ × v ↦ w ~ u₂
v₁ ⊔ v₂ ~ u = v₁ ~ u × v₂ ~ u

data wf : Value → Set where
  wf-bot : wf ⊥
  wf-fun : ∀{v w} → wf v → wf w → wf (v ↦ w)
  wf-⊔ : ∀{u v} → u ~ v → wf u → wf v → wf (u ⊔ v)

{-------------------------------------------------------------------------------
   Syntax
-------------------------------------------------------------------------------}

data Term : Set where
  `_ : ℕ → Term
  ƛ_ : Term → Term
  _·_ : Term → Term → Term

{-------------------------------------------------------------------------------
   Semantics
-------------------------------------------------------------------------------}

⟦_⟧ : Term → (ℕ → Value) → Value → Set
⟦ ` x ⟧ ρ v = v ⊑ ρ x
⟦ L · M ⟧ ρ w = Σ[ v ∈ Value ] wf v × ⟦ L ⟧ ρ (v ↦ w) × ⟦ M ⟧ ρ v 
⟦ ƛ N ⟧ ρ u = ∀ v w → v ↦ w ∈ u → ⟦ N ⟧ (v • ρ) w
