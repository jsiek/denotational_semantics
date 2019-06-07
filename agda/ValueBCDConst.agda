open import Primitives
open import Structures

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)


module ValueBCDConst where

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  const : {B : Base} → base-rep B → Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

domain : Domain
domain = record { Value = Value ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_ }

open DomainAux domain

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (const k) = Bot
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k

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


infix 4 _~_

_~_ : Value → Value → Set
⊥ ~ v = ⊤
const {B} k ~ ⊥ = ⊤
const {B} k ~ const {B′} k′
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′ 
... | no neq = Bot
const {B} k ~ v ↦ w = Bot
const {B} k ~ u ⊔ v = const {B} k ~ u × const {B} k ~ v
v ↦ w ~ ⊥ = ⊤
v ↦ w ~ const k = Bot
v ↦ w ~ v′ ↦ w′ = (v ~ v′ × w ~ w′) ⊎ ¬ (v ~ v′)
v ↦ w ~ (u₁ ⊔ u₂) = v ↦ w ~ u₁ × v ↦ w ~ u₂
v₁ ⊔ v₂ ~ u = v₁ ~ u × v₂ ~ u


consistent? : (u : Value) → (v : Value) → Dec (u ~ v)
consistent? ⊥ v = yes tt
consistent? (const k) ⊥ = yes tt
consistent? (const {B} k) (const {B′} k′)
    with base-eq? B B′
... | yes eq rewrite eq = base-rep-eq? k k′
... | no  neq = no (λ z → z)
consistent? (const k) (v₁ ↦ v₂) = no (λ z → z)
consistent? (const k) (v₁ ⊔ v₂)
    with consistent? (const k) v₁ | consistent? (const k) v₂
... | yes c1 | yes c2 = yes ⟨ c1 , c2 ⟩
... | yes c1 | no c2 = no (λ z → c2 (proj₂ z))
... | no c1  | yes c2 = no (λ z → c1 (proj₁ z))
... | no c1  | no c2 = no (λ z → c2 (proj₂ z))
consistent? (u₁ ↦ u₂) ⊥ = yes tt
consistent? (u₁ ↦ u₂) (const x) = no (λ z → z)
consistent? (u₁ ↦ u₂) (v₁ ↦ v₂)
    with consistent? u₁ v₁ | consistent? u₂ v₂
... | yes c1 | yes c2 = yes (inj₁ ⟨ c1 , c2 ⟩)
... | no c1  | yes c2 = yes (inj₂ c1)
... | no c1  | no c2 = yes (inj₂ c1)
... | yes c1 | no c2 = no (G c1 c2)
    where
    G : u₁ ~ v₁ → ¬ (u₂ ~ v₂) → ¬ ((u₁ ~ v₁ × u₂ ~ v₂) ⊎ (u₁ ~ v₁ → Bot))
    G c1 c2 (inj₁ x) = c2 (proj₂ x)
    G c1 c2 (inj₂ y) = y c1
consistent? (u₁ ↦ u₂) (v₁ ⊔ v₂)
    with consistent? (u₁ ↦ u₂) v₁ | consistent? (u₁ ↦ u₂) v₂
... | yes c1 | yes c2 = yes ⟨ c1 , c2 ⟩
... | no c1  | yes c2 = no (λ z → c1 (proj₁ z))
... | no c1  | no c2 = no (λ z → c2 (proj₂ z))
... | yes c1 | no c2 = no (λ z → c2 (proj₂ z))
consistent? (u₁ ⊔ u₂) v
    with consistent? u₁ v | consistent? u₂ v
... | yes c1 | yes c2 = yes ⟨ c1 , c2 ⟩
... | no c1  | yes c2 = no (λ z → c1 (proj₁ z))
... | no c1  | no c2 = no (λ z → c2 (proj₂ z))
... | yes c1 | no c2 = no (λ z → c2 (proj₂ z))


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


infix 5 _∈_

_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ const {B} k = u ≡ const {B} k
u ∈ v ↦ w = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w

infix 5 _⊆_

_⊆_ : Value → Value → Set
v ⊆ w = ∀{u} → u ∈ v → u ∈ w

data Fun : Value → Set where
  fun : ∀{u v w} → u ≡ (v ↦ w) → Fun u

data Fun⊥ : Value → Set where
  fun : ∀{u v w} → u ≡ (v ↦ w) → Fun⊥ u
  bot : ∀{u} → u ≡ ⊥ → Fun⊥ u

dom : (u : Value) → Value
dom ⊥  = ⊥
dom (const {B} k) = ⊥
dom (v ↦ w) = v
dom (u ⊔ u′) = dom u ⊔ dom u′

cod : (u : Value) → Value
cod ⊥  = ⊥
cod (const {B} k) = ⊥
cod (v ↦ w) = w
cod (u ⊔ u′) = cod u ⊔ cod u′

Below⊥ : Value → Set
Below⊥ ⊥ = ⊤
Below⊥ (const x) = Bot
Below⊥ (v ↦ v₁) = Bot
Below⊥ (u ⊔ v) = Below⊥ u × Below⊥ v

BelowConst : ∀{B : Base} → (k : base-rep B) → Value → Set
BelowConst k ⊥ = ⊤
BelowConst {B} k (const {B′} k′)
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′ 
... | no neg = Bot
BelowConst k (v ↦ w) = Bot
BelowConst k (u ⊔ v) = BelowConst k u × BelowConst k v

⊑-refl : ∀ {v} → v ⊑ v
⊑-refl {⊥} = ⊑-⊥
⊑-refl {const k} = ⊑-const
⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

ordering : ValueOrdering domain
ordering = record
             { _⊑_ = _⊑_
             ; ⊑-⊥ = ⊑-⊥
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-trans = ⊑-trans
             ; ⊑-fun = ⊑-fun
             ; ⊑-dist = ⊑-dist
             ; ⊑-refl = ⊑-refl
             }

