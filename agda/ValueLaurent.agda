open import Primitives

open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.List using (List ; _∷_ ; []; _++_) 
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module ValueLaurent where

infixr 7 _↦_
infixl 6 _⊔_

data Value : Set 

data Value where
  ⊥ : Value
  const : {b : Base} → base-rep b → Value
  _↦_ : Value → Value → Value
  _⊔_ : (u : Value) → (v : Value) → Value

{-
infix 3 _⊢_

Funs Γ = ∀{A} → A ∈ Γ → Σ[ B ∈ Value ] Σ[ C ∈ Value ] A ≡ B ↦ C

data _⊢_ : List Value  → Value → Set where
  wk-const : ∀{Γ Δ}{C}{b}{k} →  Γ ++ Δ ⊢ C  →  Γ ++ const {b} k ∷ Δ ⊢ C
  wk-fun : ∀{Γ Δ}{C}{A}{B} →  Γ ++ Δ ⊢ C  →  Γ ++ A ↦ B ∷ Δ ⊢ C
  ⊔R : ∀{Γ}{A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⊔ B
  ⊔L : ∀{Γ Δ}{A B C} →  Γ ++ A ∷ B ∷ Δ ⊢ C  →  Γ ++ A ⊔ B ∷ Δ ⊢ C
  refl-const : ∀{b}{k} →  const {b} k ∷ [] ⊢ const {b} k
  ⊢-fun : → 
          → (∀{C D} → C ↦ D ∈ Γ → A ∷ [] ⊢ C)
          → map cod Γ 
          → Γ ⊢ A ↦ B
-}

infix 5 _∈_

_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ const {B} k = u ≡ const {B} k
u ∈ v ↦ w = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w

infix 5 _⊆_

_⊆_ : Value → Value → Set
v ⊆ w = ∀{u} → u ∈ v → u ∈ w


AllFun : (u : Value) → Set
AllFun ⊥ = ⊤
AllFun (const x) = Bot
AllFun (v ↦ w) = ⊤
AllFun (u ⊔ v) = AllFun u × AllFun v 

SomeFun : (u : Value) → Set
SomeFun ⊥ = Bot
SomeFun (const x) = Bot
SomeFun (v ↦ w) = ⊤
SomeFun (u ⊔ v) = SomeFun u ⊎ SomeFun v 

{-
AllFun→SomeFun : ∀{u} → AllFun u → SomeFun u
AllFun→SomeFun {⊥} ()
AllFun→SomeFun {const k} ()
AllFun→SomeFun {v ↦ w} afu = tt
AllFun→SomeFun {u ⊔ v} afu = inj₁ (AllFun→SomeFun (proj₁ afu))
-}

dom : (u : Value) → Value
dom ⊥ = ⊥
dom (const k) = ⊥
dom (v ↦ w) = v
dom (u ⊔ v) = dom u ⊔ dom v

cod : (u : Value) → Value
cod ⊥  = ⊥
cod (const k) = ⊥
cod (v ↦ w) = w
cod (u ⊔ v) = cod u ⊔ cod v

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k

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

  ⊑-fun : ∀ {u v w}
       → AllFun u
       → SomeFun u
       → dom u ⊑ v
       → w ⊑ cod u
         -------------------
       → v ↦ w ⊑ u


⊑-refl : ∀{v} → v ⊑ v
⊑-refl {⊥} = ⊑-⊥
⊑-refl {const k} = ⊑-const
⊑-refl {v ↦ w} = ⊑-fun tt tt (⊑-refl{v}) ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

⊔⊑R : ∀{B C A}
    → B ⊔ C ⊑ A
    → B ⊑ A
⊔⊑R (⊑-conj-L B⊔C⊑A B⊔C⊑A₁) = B⊔C⊑A
⊔⊑R (⊑-conj-R1 B⊔C⊑A) = ⊑-conj-R1 (⊔⊑R B⊔C⊑A)
⊔⊑R (⊑-conj-R2 B⊔C⊑A) = ⊑-conj-R2 (⊔⊑R B⊔C⊑A)

⊔⊑L : ∀{B C A}
    → B ⊔ C ⊑ A
    → C ⊑ A
⊔⊑L (⊑-conj-L B⊔C⊑A B⊔C⊑A₁) = B⊔C⊑A₁
⊔⊑L (⊑-conj-R1 B⊔C⊑A) = ⊑-conj-R1 (⊔⊑L B⊔C⊑A)
⊔⊑L (⊑-conj-R2 B⊔C⊑A) = ⊑-conj-R2 (⊔⊑L B⊔C⊑A)


∈→⊑ : ∀{u v : Value}
    → u ∈ v
      -----
    → u ⊑ v
∈→⊑ {u} {⊥} refl = ⊑-⊥
∈→⊑ {u} {const k} refl = ⊑-const
∈→⊑ {u} {v ↦ w} refl = ⊑-refl
∈→⊑ {u} {v₁ ⊔ v₂} (inj₁ x) = ⊑-conj-R1 (∈→⊑ x)
∈→⊑ {u} {v₁ ⊔ v₂} (inj₂ y) = ⊑-conj-R2 (∈→⊑ y)

⊆→⊑ : ∀{u v : Value}
    → u ⊆ v
      -----
    → u ⊑ v
⊆→⊑ {⊥} s with s {⊥} refl
... | x = ⊑-⊥
⊆→⊑ {const {B} k} s with s {const {B} k} refl
... | x = ∈→⊑ x
⊆→⊑ {u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u ⊔ u′} s = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))

u∈v⊑w→u⊑w : ∀{B A C} → C ∈ B → B ⊑ A → C ⊑ A
u∈v⊑w→u⊑w {⊥} C∈B B⊑A  rewrite C∈B = B⊑A
u∈v⊑w→u⊑w {const k} C∈B B⊑A rewrite C∈B = B⊑A
u∈v⊑w→u⊑w {B₁ ↦ B₂} C∈B B⊑A rewrite C∈B = B⊑A
u∈v⊑w→u⊑w {B₁ ⊔ B₂}{A}{C} (inj₁ C∈B₁) B⊑A = u∈v⊑w→u⊑w {B₁}{A}{C} C∈B₁ (⊔⊑R B⊑A)
u∈v⊑w→u⊑w {B₁ ⊔ B₂}{A}{C} (inj₂ C∈B₂) B⊑A = u∈v⊑w→u⊑w {B₂}{A}{C} C∈B₂ (⊔⊑L B⊑A)

u⊆v⊑w→u⊑w : ∀{u v w} → u ⊆ v → v ⊑ w → u ⊑ w
u⊆v⊑w→u⊑w {⊥} {v} {w} u⊆v v⊑w = ⊑-⊥
u⊆v⊑w→u⊑w {const k} {v} {w} u⊆v v⊑w
    with u⊆v refl
... | k∈v = u∈v⊑w→u⊑w k∈v v⊑w
u⊆v⊑w→u⊑w {u₁ ↦ u₂} {v} {w} u⊆v v⊑w
    with u⊆v refl
... | u₁↦u₂∈v = u∈v⊑w→u⊑w u₁↦u₂∈v v⊑w
u⊆v⊑w→u⊑w {u₁ ⊔ u₂} {v} {w} u⊆v v⊑w =
    ⊑-conj-L (u⊆v⊑w→u⊑w u₁⊆v v⊑w) (u⊆v⊑w→u⊑w u₂⊆v v⊑w)
    where
    u₁⊆v : u₁ ⊆ v
    u₁⊆v {u′} u′∈u₁ = u⊆v (inj₁ u′∈u₁)
    u₂⊆v : u₂ ⊆ v
    u₂⊆v {u′} u′∈u₂ = u⊆v (inj₂ u′∈u₂)

{-
dom↦cod-⊑ : ∀{v}
          → AllFun v
          → dom v ↦ cod v ⊑ v
dom↦cod-⊑ {⊥} ()
dom↦cod-⊑ {const k} ()
dom↦cod-⊑ {v ↦ w} fv = ⊑-refl
dom↦cod-⊑ {u ⊔ v} ⟨ fu , fv ⟩ =
  ⊑-fun {!!}
        (⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl))
        (⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl))
-}

dom↦cod-⊑ : ∀{v w}
          → v ⊑ w
          → AllFun v → SomeFun v
          → dom v ↦ cod v ⊑ w
dom↦cod-⊑ {.⊥} {w} ⊑-⊥ afv ()
dom↦cod-⊑ {.(const _)} {.(const _)} ⊑-const afv ()
dom↦cod-⊑ {v₁ ⊔ v₂} {w} (⊑-conj-L v₁⊑w v₂⊑w) ⟨ fst , snd ⟩ (inj₁ x) 
    with dom↦cod-⊑ {v₁} {w} v₁⊑w fst x
... | ⊑-fun a b c d = {!!}    
... | ⊑-conj-R1 a = {!!}
... | ⊑-conj-R2 b = {!!}
dom↦cod-⊑ {v₁ ⊔ v₂} {w} (⊑-conj-L v⊑w v⊑w₁) ⟨ fst , snd ⟩ (inj₂ y) = {!!}
dom↦cod-⊑ {v} {.(_ ⊔ _)} (⊑-conj-R1 v⊑w) afv sfv = {!!}
dom↦cod-⊑ {v} {.(_ ⊔ _)} (⊑-conj-R2 v⊑w) afv sfv = {!!}
dom↦cod-⊑ {.(_ ↦ _)} {w} (⊑-fun x x₁ v⊑w v⊑w₁) afv sfv = {!!}



SomeFun-⊑ : ∀{v w} → SomeFun v → v ⊑ w → SomeFun w
SomeFun-⊑ {.⊥} {w} () ⊑-⊥
SomeFun-⊑ {.(const _)} {.(const _)} () ⊑-const
SomeFun-⊑ {.(_ ⊔ _)} {w} (inj₁ x) (⊑-conj-L v⊑w v⊑w₁) = SomeFun-⊑ x v⊑w
SomeFun-⊑ {.(_ ⊔ _)} {w} (inj₂ y) (⊑-conj-L v⊑w v⊑w₁) = SomeFun-⊑ y v⊑w₁
SomeFun-⊑ {v} {w₁ ⊔ w₂} fv (⊑-conj-R1 v⊑w) = inj₁ (SomeFun-⊑ fv v⊑w)
SomeFun-⊑ {v} {.(_ ⊔ _)} fv (⊑-conj-R2 v⊑w) = inj₂ (SomeFun-⊑ fv v⊑w)
SomeFun-⊑ {.(_ ↦ _)} {w} fv (⊑-fun x y v⊑w v⊑w₁) = y

AllFun-⊑ : ∀{v w} → AllFun w → v ⊑ w → AllFun v
AllFun-⊑ {.⊥} {w} afw ⊑-⊥ = tt
AllFun-⊑ {.(const _)} {.(const _)} () ⊑-const
AllFun-⊑ {.(_ ⊔ _)} {w} afw (⊑-conj-L v⊑w v⊑w₁) =
    ⟨ AllFun-⊑ afw v⊑w , AllFun-⊑ afw v⊑w₁ ⟩
AllFun-⊑ {v} {.(_ ⊔ _)} afw (⊑-conj-R1 v⊑w) = AllFun-⊑ (proj₁ afw) v⊑w
AllFun-⊑ {v} {.(_ ⊔ _)} afw (⊑-conj-R2 v⊑w) = AllFun-⊑ (proj₂ afw) v⊑w
AllFun-⊑ {.(_ ↦ _)} {w} afw (⊑-fun x y v⊑w v⊑w₁) = tt

factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = AllFun u′ × u′ ⊆ u × dom u′ ⊑ v × w ⊑ cod u′

⊑-fun-inv : ∀{u₁ u₂ v w}
      → u₁ ⊑ u₂
      → v ↦ w ∈ u₁
      → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
⊑-fun-inv {.⊥} {u₂} {v} {w} ⊑-⊥ ()
⊑-fun-inv {.(const _)} {.(const _)} {v} {w} ⊑-const ()
⊑-fun-inv {u11 ⊔ u12} {u₂} {v} {w} (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₁ x) = ⊑-fun-inv u₁⊑u₂ x
⊑-fun-inv {u11 ⊔ u12} {u₂} {v} {w} (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₂ y) = ⊑-fun-inv u₁⊑u₃ y
⊑-fun-inv {u₁} {u21 ⊔ u22} {v} {w} (⊑-conj-R1 u₁⊑u₂) v↦w∈u₁
    with ⊑-fun-inv {u₁} {u21} {v} {w} u₁⊑u₂ v↦w∈u₁
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u3⊆u₁ , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ afu₃ , ⟨ (λ {x} x₁ → inj₁ (u3⊆u₁ x₁)) , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩  
⊑-fun-inv {u₁} {u21 ⊔ u22} {v} {w} (⊑-conj-R2 u₁⊑u₂) v↦w∈u₁
    with ⊑-fun-inv {u₁} {u22} {v} {w} u₁⊑u₂ v↦w∈u₁
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u3⊆u₁ , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ afu₃ , ⟨ (λ {x} x₁ → inj₂ (u3⊆u₁ x₁)) , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩  
⊑-fun-inv {u11 ↦ u21} {u₂} {v} {w} (⊑-fun x x₁ u₁⊑u₂ u₁⊑u₃) refl =
      ⟨ u₂ , ⟨ x , ⟨ (λ {x₂} x₃ → x₃) , ⟨ u₁⊑u₂ , u₁⊑u₃ ⟩ ⟩ ⟩ ⟩


⊑-dom : ∀{u v}
      → u ⊑ v
      → SomeFun u
      → Σ[ v′ ∈ Value ] v′ ⊆ v × dom v′ ⊑ dom u × AllFun v′ × SomeFun v′
⊑-dom {.⊥} {v} ⊑-⊥ ()
⊑-dom {.(const _)} {.(const _)} ⊑-const ()
⊑-dom {u₁ ⊔ u₂} {v} (⊑-conj-L u₁⊑v u₂⊑v) (inj₁ sfu₁) 
    with ⊑-dom {u₁} {v} u₁⊑v sfu₁ 
... | ⟨ v′ , ⟨ v′⊆v , ⟨ dv′⊑du₁ , ⟨ af , sf ⟩ ⟩ ⟩ ⟩ =
      ⟨ v′ , ⟨ v′⊆v , ⟨ ⊑-conj-R1 dv′⊑du₁ , ⟨ af , sf ⟩ ⟩ ⟩ ⟩
⊑-dom {u₁ ⊔ u₂} {v} (⊑-conj-L u₁⊑v u₂⊑v) (inj₂ sfu₂)
    with ⊑-dom {u₂} {v} u₂⊑v sfu₂
... | ⟨ v′ , ⟨ v′⊆v , ⟨ dv′⊑du₂ , ⟨ af , sf ⟩ ⟩ ⟩ ⟩ =
      ⟨ v′ , ⟨ v′⊆v , ⟨ ⊑-conj-R2 dv′⊑du₂ , ⟨ af , sf ⟩ ⟩ ⟩ ⟩
⊑-dom {u} {v₁ ⊔ v₂} (⊑-conj-R1 u⊑v) sfu 
    with ⊑-dom {u} {v₁} u⊑v sfu
... | ⟨ v₁′ , ⟨ v₁′⊆v₁ , ⟨ dv₁′⊑du , ⟨ af , sf ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₁′ , ⟨ (λ {u₁} z → inj₁ (v₁′⊆v₁ z)) , ⟨ dv₁′⊑du , ⟨ af , sf ⟩ ⟩ ⟩ ⟩
⊑-dom {u} {v₁ ⊔ v₂} (⊑-conj-R2 u⊑v) sfu
    with ⊑-dom {u} {v₂} u⊑v sfu
... | ⟨ v₂′ , ⟨ v₂′⊆v₂ , ⟨ dv₂′⊑du , ⟨ af , sf ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂′ , ⟨ (λ {u₁} z → inj₂ (v₂′⊆v₂ z)) , ⟨ dv₂′⊑du , ⟨ af , sf ⟩ ⟩ ⟩ ⟩
⊑-dom {u₁ ↦ u₂} {v} (⊑-fun x y u⊑v u⊑v₁) sfu =
      ⟨ v , ⟨ (λ {x₁} x₂ → x₂) , ⟨ u⊑v , ⟨ x , y ⟩ ⟩ ⟩ ⟩

⊑-cod : ∀{u v}
      → u ⊑ v
      → AllFun u
      → cod u ⊑ cod v
⊑-cod {.⊥} {v} ⊑-⊥ afu = ⊑-⊥
⊑-cod {.(const _)} {.(const _)} ⊑-const ()
⊑-cod {u₁ ⊔ u₂} {v} (⊑-conj-L u₁⊑v u₂⊑v) ⟨ afu₁ , afu₂ ⟩ =
    ⊑-conj-L (⊑-cod {u₁}{v} u₁⊑v afu₁) (⊑-cod {u₂}{v} u₂⊑v afu₂)
⊑-cod {u} {v₁ ⊔ v₂} (⊑-conj-R1 u⊑v₁) afu = ⊑-conj-R1 (⊑-cod u⊑v₁ afu)
⊑-cod {u} {v₁ ⊔ v₂} (⊑-conj-R2 u⊑v₂) afu = ⊑-conj-R2 (⊑-cod u⊑v₂ afu)
⊑-cod {u₁ ↦ u₂} {v} (⊑-fun afv sfv dv⊑v w⊑cv) afu = w⊑cv


⊥∈→⊥∈cod : ∀{v} → ⊥ ∈ v → ⊥ ∈ cod v
⊥∈→⊥∈cod {⊥} ⊥∈v = refl
⊥∈→⊥∈cod {const x} ⊥∈v = refl
⊥∈→⊥∈cod {v ↦ v₁} ()
⊥∈→⊥∈cod {v₁ ⊔ v₂} (inj₁ x) = inj₁ (⊥∈→⊥∈cod x)
⊥∈→⊥∈cod {v₁ ⊔ v₂} (inj₂ y) = inj₂ (⊥∈→⊥∈cod y)

v↦w∈u→w⊆cod-u : ∀{u v w} → v ↦ w ∈ u → w ⊆ cod u
v↦w∈u→w⊆cod-u {⊥} ()
v↦w∈u→w⊆cod-u {const k} ()
v↦w∈u→w⊆cod-u {u₁ ↦ u₂} refl {u} u∈u₂ = u∈u₂
v↦w∈u→w⊆cod-u {u₁ ⊔ u₂}{v}{w} (inj₁ x) {u} u∈w = inj₁ (v↦w∈u→w⊆cod-u x u∈w)
v↦w∈u→w⊆cod-u {u₁ ⊔ u₂} (inj₂ y) {u} u∈w = inj₂ (v↦w∈u→w⊆cod-u y u∈w)

⊆-cod : ∀{u v} → u ⊆ v → AllFun u → cod u ⊆ cod v
⊆-cod {⊥} {⊥} u⊆v afu = λ z → z
⊆-cod {const x} {⊥} u⊆v ()
⊆-cod {u ↦ u₁} {⊥} u⊆v afu {w} w∈codu
    with u⊆v refl
... | ()    
⊆-cod {u₁ ⊔ u₂} {v} u⊆v afu {w} (inj₁ x) =
    ⊆-cod (λ {u} z → u⊆v (inj₁ z)) (proj₁ afu) x
⊆-cod {u₁ ⊔ u₂} {v} u⊆v afu {w} (inj₂ y) =
    ⊆-cod (λ {u} z → u⊆v (inj₂ z)) (proj₂ afu) y
⊆-cod {⊥} {const k} u⊆v afu = λ z → z
⊆-cod {const k} {const k′} u⊆v ()
⊆-cod {u₁ ↦ u₂} {const k} u⊆v afu {w} w∈codu
    with u⊆v refl
... | ()    
⊆-cod {⊥} {v₁ ↦ v₂} u⊆v afu
    with u⊆v refl
... | ()
⊆-cod {const k} {v₁ ↦ v₂} u⊆v ()
⊆-cod {u₁ ↦ u₂} {v₁ ↦ v₂} u⊆v afu {w} w∈codu 
    with u⊆v refl
... | refl = w∈codu
⊆-cod {⊥} {v₁ ⊔ v₂} u⊆v afu {u′} u′∈codv
    with u⊆v refl
... | inj₁ ⊥∈v₁ rewrite u′∈codv = inj₁ (⊥∈→⊥∈cod ⊥∈v₁)
... | inj₂ ⊥∈v₂ rewrite u′∈codv = inj₂ (⊥∈→⊥∈cod ⊥∈v₂)
⊆-cod {const k} {v₁ ⊔ v₂} u⊆v ()
⊆-cod {u₁ ↦ u₂} {v₁ ⊔ v₂} u⊆v afu {w} w∈codu
    with u⊆v refl
... | inj₁ u₁↦u₂∈v₁ =
      inj₁ (v↦w∈u→w⊆cod-u u₁↦u₂∈v₁ w∈codu)
... | inj₂ u₁↦u₂∈v₂ =
      inj₂ (v↦w∈u→w⊆cod-u u₁↦u₂∈v₂ w∈codu)


         

{-
⊆-cod : ∀{u u′ v} → u′ ⊆ u → cod u ⊑ cod v
         → cod u′ ⊑ cod v

⊑-cod : ∀{u v} → u ⊑ v → AllFun u
         → Σ[ v′ ∈ Value ] v′ ⊆ v × cod u ⊑ cod v′
⊑-cod {.⊥} {v} ⊑-⊥ ()
⊑-cod {.(const _)} {.(const _)} ⊑-const ()
⊑-cod {u₁ ⊔ u₂} {v} (⊑-conj-L u₁⊑v u₂⊑v) ⟨ afu₁ , afu₂ ⟩
    with ⊑-cod {u₁}{v} u₁⊑v afu₁ | ⊑-cod {u₂}{v} u₂⊑v afu₂
... | ⟨ v₁ , ⟨ v₁⊆v , cu⊑cv₁ ⟩ ⟩ | ⟨ v₂ , ⟨ v₂⊆v , cu⊑cv₂ ⟩ ⟩ =
      ⟨ (v₁ ⊔ v₂) , ⟨ G , (⊑-conj-L (⊑-conj-R1 cu⊑cv₁) (⊑-conj-R2 cu⊑cv₂)) ⟩ ⟩
    where
    G : {u : Value} → u ∈ v₁ ⊎ u ∈ v₂ → u ∈ v
    G {u} (inj₁ u∈v₁) = v₁⊆v u∈v₁
    G {u} (inj₂ u∈v₂) = v₂⊆v u∈v₂
⊑-cod {u} {v₁ ⊔ v₂} (⊑-conj-R1 u⊑v₁) afu
    with ⊑-cod {u}{v₁} u⊑v₁ afu
... | ⟨ v , ⟨ v⊆v₁ , cu⊑cv ⟩ ⟩ =
      ⟨ v , ⟨ (λ {u₁} z → inj₁ (v⊆v₁ z)) , cu⊑cv ⟩ ⟩
⊑-cod {u} {v₁ ⊔ v₂} (⊑-conj-R2 u⊑v₂) afu
    with ⊑-cod {u}{v₂} u⊑v₂ afu
... | ⟨ v , ⟨ v⊆v₂ , cu⊑cv ⟩ ⟩ =
      ⟨ v , ⟨ (λ {u₁} z → inj₂ (v⊆v₂ z)) , cu⊑cv ⟩ ⟩
⊑-cod {u₁ ↦ u₂} {v} (⊑-fun sfv dv⊑u₁ u₂⊑cv) afu =
      ⟨ v , ⟨ (λ {x} x₁ → x₁) , u₂⊑cv ⟩ ⟩
-}

{-
⊑-dom : ∀{u v} → u ⊑ v → SomeFun u → dom v ⊑ dom u
⊑-dom {.⊥} {v} ⊑-⊥ ()
⊑-dom {.(const _)} {.(const _)} ⊑-const ()
⊑-dom {.(_ ⊔ _)} {v} (⊑-conj-L u⊑v u⊑v₁) (inj₁ x) = ⊑-conj-R1 (⊑-dom u⊑v x)
⊑-dom {.(_ ⊔ _)} {v} (⊑-conj-L u⊑v u⊑v₁) (inj₂ y) = ⊑-conj-R2 (⊑-dom u⊑v₁ y)
⊑-dom {u} {v₁ ⊔ v₂} (⊑-conj-R1 u⊑v) sfu = {!!}
⊑-dom {u} {.(_ ⊔ _)} (⊑-conj-R2 u⊑v) sfu = {!!}
⊑-dom {.(_ ↦ _)} {v} (⊑-fun x u⊑v u⊑v₁) sfu = u⊑v
-}


⊑-trans : ∀{u v w} → u ⊑ v → v ⊑ w → u ⊑ w
⊑-trans {.⊥} {v} {w} ⊑-⊥ v⊑w = ⊑-⊥
⊑-trans {const k} {const k′} {w} ⊑-const v⊑w = v⊑w
⊑-trans {.(_ ⊔ _)} {v} {w} (⊑-conj-L u⊑v u⊑v₁) v⊑w =
    ⊑-conj-L (⊑-trans u⊑v v⊑w) (⊑-trans u⊑v₁ v⊑w)
⊑-trans {u} {v₁ ⊔ v₂} {w} (⊑-conj-R1 u⊑v₁) v₁⊔v₂⊑w =
    let v₁⊑w = ⊔⊑R v₁⊔v₂⊑w in
    ⊑-trans u⊑v₁ v₁⊑w
⊑-trans {u} {v₁ ⊔ v₂} {w} (⊑-conj-R2 u⊑v₂) v₁⊔v₂⊑w =
    let v₂⊑w = ⊔⊑L v₁⊔v₂⊑w in
    ⊑-trans u⊑v₂ v₂⊑w
⊑-trans {u₁ ↦ u₂} {v} {w} (⊑-fun afv sfv dv⊑u₁ u₂⊑cv) v⊑w
    with ⊑-fun-inv {u₁ ↦ u₂} {v} (⊑-fun afv sfv dv⊑u₁ u₂⊑cv) refl
... | ⟨ v′ , ⟨ afv′ , ⟨ v′⊆v , ⟨ dv′⊑u₁ , u₂⊑cv′ ⟩ ⟩ ⟩ ⟩ =
    

   {!!}
   
   where
   H : ∀{v₁ v₂} → v₁ ↦ v₂ ∈ v′ → Σ[ w′ ∈ Value ] factor w w′ v₁ v₂
   H {v₁}{v₂} v₁↦v₂∈v′ =
       ⊑-fun-inv {v′} {w} (u⊆v⊑w→u⊑w v′⊆v v⊑w) v₁↦v₂∈v′

