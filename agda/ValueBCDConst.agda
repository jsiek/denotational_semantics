open import Primitives
open import Structures

open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module ValueBCDConst where

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set 
infix 4 _~_
_~_ : Value → Value → Set


data Value where
  ⊥ : Value
  const : {B : Base} → base-rep B → Value
  _↦_ : Value → Value → Value
  _⊔_ : (u : Value) → (v : Value) → {c : u ~ v} → Value

domain : Domain
domain = record { Value = Value ; _~_ = _~_ ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_ }

open DomainAux domain

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (const k) = Bot
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)



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


~⊔R : ∀{v u₁ u₂} → v ~ u₁ → v ~ u₂ → {c : u₁ ~ u₂}
    → v ~ ((u₁ ⊔ u₂){c})
~⊔R {⊥} v~u₁ v~u₂ = tt
~⊔R {const k} v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
~⊔R {v ↦ w} v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
~⊔R {v₁ ⊔ v₂} v~u₁ v~u₂ =
    ⟨ (~⊔R {v = v₁} (proj₁ v~u₁) (proj₁ v~u₂)) ,
      (~⊔R {v = v₂} (proj₂ v~u₁) (proj₂ v~u₂)) ⟩

~-sym : ∀{u v} → u ~ v → v ~ u
~-sym {⊥} {⊥} u~v = tt
~-sym {⊥} {const k} u~v = tt
~-sym {⊥} {v ↦ w} u~v = tt
~-sym {⊥} {v₁ ⊔ v₂} u~v = ⟨ ~-sym {v = v₁} tt , ~-sym {v = v₂} tt ⟩
~-sym {const k} {⊥} u~v = tt
~-sym {const {B} k} {const {B′} k′} u~v
    with base-eq? B B′
... | no neq = ⊥-elim u~v
... | yes eq
    rewrite eq
    with base-eq? B′ B′
... | no neq = neq refl
... | yes refl = sym u~v
~-sym {const k} {v ↦ w} ()
~-sym {const k} {u ⊔ v} ⟨ k~u , k~v ⟩ =
  ⟨ (~-sym{v = u} k~u) , (~-sym{v = v} k~v) ⟩
~-sym {v ↦ w} {⊥} u~v = tt
~-sym {v ↦ w} {const k} ()
~-sym {v ↦ w} {v′ ↦ w′} (inj₁ ⟨ fst , snd ⟩) =
   inj₁ ⟨ (~-sym{v = v′} fst) , (~-sym{v = w′} snd) ⟩
~-sym {v ↦ w} {v′ ↦ w′} (inj₂ ¬v~v′) =
   inj₂ λ x → ⊥-elim (contradiction (~-sym{u = v′} x) ¬v~v′)
~-sym {v ↦ w} {u₁ ⊔ u₂} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{v = u₁} fst , ~-sym{v = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {⊥} ⟨ fst , snd ⟩ = tt
~-sym {u₁ ⊔ u₂} {const k} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{u = u₁} fst , ~-sym{u = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {v ↦ v₁} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{u = u₁} fst , ~-sym{u = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {v₁ ⊔ v₂} ⟨ fst , snd ⟩ 
    with ~-sym {u₁} {v₁ ⊔ v₂} fst
       | ~-sym {u₂} {v₁ ⊔ v₂} snd
... | ⟨ v₁~u₁ , v₂~u₁ ⟩ | ⟨ v₁~u₂ , v₂~u₂ ⟩ =
      ⟨ ~⊔R{v = v₁} v₁~u₁ v₁~u₂ , ~⊔R{v = v₂} v₂~u₁ v₂~u₂ ⟩


~-refl : ∀{v} → v ~ v
~-refl {⊥} = tt
~-refl {const {B} k} 
    with base-eq? B B
... | yes eq rewrite eq = refl
... | no neq = neq refl
~-refl {v ↦ w} = inj₁ ⟨ ~-refl {v} , ~-refl {w} ⟩
~-refl {(v₁ ⊔ v₂){c}} =
    ⟨ ~⊔R {v₁} (~-refl {v₁}) c ,
      ~⊔R {v₂} (~-sym {v₁} c) (~-refl {v₂}) ⟩

~-↦-cong : ∀{u v u′ v′} → u ~ u′ → v ~ v′ → (u ↦ v) ~ (u′ ↦ v′)
~-↦-cong = λ z z₁ → inj₁ ⟨ z , z₁ ⟩

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k

  ⊑-conj-L : ∀ {u v w}
        → v ⊑ u
        → w ⊑ u
        → {c : v ~ w}
          -----------
        → ((v ⊔ w){c}) ⊑ u

  ⊑-conj-R1 : ∀ {u v w}
       → u ⊑ v → {c : v ~ w}
         ------------------
       → u ⊑ ((v ⊔ w){c})

  ⊑-conj-R2 : ∀ {u v w}
       → u ⊑ w → {c : v ~ w}
         -----------
       → u ⊑ ((v ⊔ w){c})

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
       → {c : w ~ w′}
         --------------------------------------------
       → v ↦ ((w ⊔ w′){c}) ⊑ (((v ↦ w) ⊔ (v ↦ w′))
         {~-↦-cong {v}{w}{v}{w′} (~-refl {v}) c})


⊔⊑R : ∀{B₁ B₂ A} {c}
    → ((B₁ ⊔ B₂){c}) ⊑ A
    → B₁ ⊑ A
⊔⊑R (⊑-conj-L B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = B₁⊔B₂⊑A
⊔⊑R (⊑-conj-R1 B₁⊔B₂⊑A) = ⊑-conj-R1 (⊔⊑R B₁⊔B₂⊑A)
⊔⊑R (⊑-conj-R2 B₁⊔B₂⊑A) = ⊑-conj-R2 (⊔⊑R B₁⊔B₂⊑A)
⊔⊑R (⊑-trans B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = ⊑-trans (⊔⊑R B₁⊔B₂⊑A) B₁⊔B₂⊑A₁

⊔⊑L : ∀{B₁ B₂ A} {c}
    → ((B₁ ⊔ B₂){c}) ⊑ A
    → B₂ ⊑ A
⊔⊑L (⊑-conj-L B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = B₁⊔B₂⊑A₁
⊔⊑L (⊑-conj-R1 B₁⊔B₂⊑A) = ⊑-conj-R1 (⊔⊑L B₁⊔B₂⊑A)
⊔⊑L (⊑-conj-R2 B₁⊔B₂⊑A) = ⊑-conj-R2 (⊔⊑L B₁⊔B₂⊑A)
⊔⊑L (⊑-trans B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = ⊑-trans (⊔⊑L B₁⊔B₂⊑A) B₁⊔B₂⊑A₁


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

v~⊥ : ∀{v : Value} → v ~ ⊥
v~⊥ {⊥} = tt
v~⊥ {const x} = tt
v~⊥ {v ↦ w} = tt
v~⊥ {v₁ ⊔ v₂} = ⟨ v~⊥ {v₁} , v~⊥ {v₂} ⟩

dom : (u : Value) → Maybe Value
dom ⊥ = nothing
dom (const k) = nothing
dom (u₁ ↦ u₂) = just u₁
dom (u₁ ⊔ u₂)
    with dom u₁ | dom u₂
... | nothing | _ = nothing
... | just v₁ | nothing = nothing
... | just v₁ | just v₂
    with consistent? v₁ v₂
... | yes v₁~v₂ = just ((v₁ ⊔ v₂) {v₁~v₂})
... | no v₁~̸v₂ = nothing


{-
dom ⊥ {c} = ⊥
dom (const {B} k) {c} = ⊥
dom (v ↦ w) {c} = v
dom ((u ⊔ u′){c}) {dc} = (dom u ⊔ dom u′){{!!}}
-}

cod : (u : Value) → Maybe Value
cod ⊥ = nothing
cod (const k) = nothing
cod (u₁ ↦ u₂) = just u₂
cod (u₁ ⊔ u₂)
    with cod u₁ | cod u₂
... | nothing | _ = nothing
... | just v₁ | nothing = nothing
... | just v₁ | just v₂
    with consistent? v₁ v₂
... | yes c = just ((v₁ ⊔ v₂) {c})
... | no nc = nothing


{-
cod ⊥  = ⊥
cod (const {B} k) = ⊥
cod (v ↦ w) = w
cod ((u ⊔ u′){c}) = (cod u ⊔ cod u′){~-cod~ {u}{u′} c}
-}



⊑-refl : ∀ {v} → v ⊑ v
⊑-refl {⊥} = ⊑-⊥
⊑-refl {const k} = ⊑-const
⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)


u~v⊔w : ∀{u v w}{c} → u ~ v → u ~ w → u ~ (v ⊔ w) {c}
u~v⊔w {⊥} {v} {w} u~v u~w = tt
u~v⊔w {const k} {v} {w} u~v u~w = ⟨ u~v , u~w ⟩
u~v⊔w {u₁ ↦ u₂} {v} {w} u~v u~w = ⟨ u~v , u~w ⟩
u~v⊔w {u₁ ⊔ u₂} {v} {w} u~v u~w =
  ⟨ (u~v⊔w {u₁} (proj₁ u~v) (proj₁ u~w)) ,
    (u~v⊔w {u₂} (proj₂ u~v) (proj₂ u~w)) ⟩

~-⊔-cong : ∀{u v u′ v′}
             → (u ~ u′) → (u ~ v′)
             → (v ~ u′) → (v ~ v′)
             → {c1 : (u ~ v)} {c2 : (u′ ~ v′)}
             → ((u ⊔ v){c1}) ~ ((u′ ⊔ v′){c2})
~-⊔-cong {u}{v}{u′}{v′} u~u′ u~v′ v~u′ v~v′ {u~v} {u′~v′} =
  ⟨ u~v⊔w {u}{u′}{v′} u~u′ u~v′ , u~v⊔w {v}{u′}{v′} v~u′ v~v′ ⟩

ordering : ValueOrdering domain
ordering = record
             { _⊑_ = _⊑_
             ; ⊑-⊥ = ⊑-⊥
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-trans = ⊑-trans
             ; ⊑-fun = ⊑-fun
             ; ⊑-refl = ⊑-refl
             ; ~-↦-cong = λ {u} {v} {u′} {v′} z z₁ → inj₁ ⟨ z , z₁ ⟩
             ; ~-refl = λ {v} → ~-refl {v}
             ; ~-↦ = λ {v} {w} {v′} {w′} z → z
             ; ~-⊔-cong = λ {u}{v}{u′}{v′} → ~-⊔-cong {u}{v}{u′}{v′}
             ; ⊑-dist = ⊑-dist
             }


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

