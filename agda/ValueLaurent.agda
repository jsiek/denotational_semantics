open import Primitives

open import Data.Nat using (ℕ; suc ; zero; _+_; _<_; _≤_; z≤n; s≤s) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; ≤-step; ⊔-mono-≤;
         +-mono-≤; +-mono-≤-<; +-mono-<-≤; +-comm; +-assoc; n≤1+n; 
         ≤-pred; m≤m+n; n≤m+n; ≤-reflexive)
open Data.Nat.Properties.≤-Reasoning using (begin_; _≤⟨_⟩_; _∎)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning renaming (begin_ to start_; _∎ to _□)

module ValueLaurent where

infixr 7 _↦_
infixl 6 _⊔_

data Value : Set 

data Value where
  ⊥ : Value
  const : {b : Base} → base-rep b → Value
  _↦_ : Value → Value → Value
  _⊔_ : (u : Value) → (v : Value) → Value

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
AllFun ⊥ = Bot
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

  ⊑-fun : ∀ {u u′ v w}
       → u′ ⊆ u
       → AllFun u′
       → dom u′ ⊑ v
       → w ⊑ cod u′
         -------------------
       → v ↦ w ⊑ u


⊑-refl : ∀{v} → v ⊑ v
⊑-refl {⊥} = ⊑-⊥
⊑-refl {const k} = ⊑-const
⊑-refl {v ↦ w} = ⊑-fun{v ↦ w}{v ↦ w} (λ {u} z → z) tt (⊑-refl{v}) ⊑-refl
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
_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

SomeFun⇔↦∈ : ∀{v} → SomeFun v iff (Σ[ u₁ ∈ Value ] Σ[ u₂ ∈ Value ] u₁ ↦ u₂ ∈ v)
SomeFun⇔↦∈ {⊥} = ⟨ (λ ()) , G ⟩
  where
  G : (Σ[ u₁ ∈ Value ] Σ[ u₂ ∈ Value ] u₁ ↦ u₂ ≡ ⊥) → Bot
  G ⟨ u₁ , ⟨ u₂ , () ⟩ ⟩
SomeFun⇔↦∈ {const k} = ⟨ (λ ()) , G ⟩
  where
  G : (Σ[ u₁ ∈ Value ] Σ[ u₂ ∈ Value ] u₁ ↦ u₂ ≡ const k) → Bot
  G ⟨ u₁ , ⟨ u₂ , () ⟩ ⟩
SomeFun⇔↦∈ {v ↦ w} = ⟨ (λ x → ⟨ v , ⟨ w , refl ⟩ ⟩) , (λ x → tt) ⟩
SomeFun⇔↦∈ {v ⊔ w} = ⟨ G , H ⟩
  where
  G : SomeFun v ⊎ SomeFun w →
      Σ[ u₁ ∈ Value ] Σ[ u₂ ∈ Value ] (u₁ ↦ u₂ ∈ v ⊎ u₁ ↦ u₂ ∈ w)
  G (inj₁ x)
      with proj₁ (SomeFun⇔↦∈ {v}) x
  ... | ⟨ u₁ , ⟨ u₂ , u₁↦u₂∈v ⟩ ⟩ =  
        ⟨ u₁ , ⟨ u₂ , (inj₁ u₁↦u₂∈v) ⟩ ⟩
  G (inj₂ y)
      with proj₁ (SomeFun⇔↦∈ {w}) y
  ... | ⟨ u₁ , ⟨ u₂ , u₁↦u₂∈w ⟩ ⟩ =  
        ⟨ u₁ , ⟨ u₂ , (inj₂ u₁↦u₂∈w) ⟩ ⟩

  H : (Σ[ u₁ ∈ Value ] Σ[ u₂ ∈ Value ] (u₁ ↦ u₂ ∈ v ⊎ u₁ ↦ u₂ ∈ w)) → SomeFun v ⊎ SomeFun w
  H ⟨ u₁ , ⟨ u₂ , inj₁ x ⟩ ⟩ =
    let sfv = proj₂ (SomeFun⇔↦∈ {v}) ⟨ u₁ , ⟨ u₂ , x ⟩ ⟩ in
    inj₁ sfv
  H ⟨ u₁ , ⟨ u₂ , inj₂ y ⟩ ⟩ =
    let sfw = proj₂ (SomeFun⇔↦∈ {w}) ⟨ u₁ , ⟨ u₂ , y ⟩ ⟩ in
    inj₂ sfw
-}

{-
SomeFun-⊑ : ∀{v w} → SomeFun v → v ⊑ w → SomeFun w
SomeFun-⊑ {.⊥} {w} () ⊑-⊥
SomeFun-⊑ {.(const _)} {.(const _)} () ⊑-const
SomeFun-⊑ {.(_ ⊔ _)} {w} (inj₁ x) (⊑-conj-L v⊑w v⊑w₁) = SomeFun-⊑ x v⊑w
SomeFun-⊑ {.(_ ⊔ _)} {w} (inj₂ y) (⊑-conj-L v⊑w v⊑w₁) = SomeFun-⊑ y v⊑w₁
SomeFun-⊑ {v} {w₁ ⊔ w₂} fv (⊑-conj-R1 v⊑w) = inj₁ (SomeFun-⊑ fv v⊑w)
SomeFun-⊑ {v} {.(_ ⊔ _)} fv (⊑-conj-R2 v⊑w) = inj₂ (SomeFun-⊑ fv v⊑w)
SomeFun-⊑ {v₁ ↦ v₂} {w} fv (⊑-fun{w}{u′} u′⊆w afu′ du′⊑v₁ v₂⊑cu′) = {!!}
-}
{-
AllFun-⊑ : ∀{v w} → AllFun w → v ⊑ w → AllFun v
AllFun-⊑ {.⊥} {w} afw ⊑-⊥ = tt
AllFun-⊑ {.(const _)} {.(const _)} () ⊑-const
AllFun-⊑ {.(_ ⊔ _)} {w} afw (⊑-conj-L v⊑w v⊑w₁) =
    ⟨ AllFun-⊑ afw v⊑w , AllFun-⊑ afw v⊑w₁ ⟩
AllFun-⊑ {v} {.(_ ⊔ _)} afw (⊑-conj-R1 v⊑w) = AllFun-⊑ (proj₁ afw) v⊑w
AllFun-⊑ {v} {.(_ ⊔ _)} afw (⊑-conj-R2 v⊑w) = AllFun-⊑ (proj₂ afw) v⊑w
AllFun-⊑ {.(_ ↦ _)} {w} afw (⊑-fun x y v⊑w v⊑w₁) = tt
-}

factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = AllFun u′ × u′ ⊆ u × dom u′ ⊑ v × w ⊑ cod u′

⊑-fun-inv : ∀{u₁ u₂ v w}
      → u₁ ⊑ u₂
      → v ↦ w ∈ u₁
      → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
⊑-fun-inv {.⊥} {u₂} {v} {w} ⊑-⊥ ()
⊑-fun-inv {.(const _)} {.(const _)} {v} {w} ⊑-const ()
⊑-fun-inv {u11 ⊔ u12} {u₂} {v} {w} (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₁ x) =
    ⊑-fun-inv u₁⊑u₂ x
⊑-fun-inv {u11 ⊔ u12} {u₂} {v} {w} (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₂ y) =
    ⊑-fun-inv u₁⊑u₃ y
⊑-fun-inv {u₁} {u21 ⊔ u22} {v} {w} (⊑-conj-R1 u₁⊑u₂) v↦w∈u₁
    with ⊑-fun-inv {u₁} {u21} {v} {w} u₁⊑u₂ v↦w∈u₁
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u3⊆u₁ , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ afu₃ , ⟨ (λ {x} x₁ → inj₁ (u3⊆u₁ x₁)) , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩  
⊑-fun-inv {u₁} {u21 ⊔ u22} {v} {w} (⊑-conj-R2 u₁⊑u₂) v↦w∈u₁
    with ⊑-fun-inv {u₁} {u22} {v} {w} u₁⊑u₂ v↦w∈u₁
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u3⊆u₁ , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ afu₃ , ⟨ (λ {x} x₁ → inj₂ (u3⊆u₁ x₁)) , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩  
⊑-fun-inv {u11 ↦ u21} {u₂} {v} {w} (⊑-fun{u′ = u′} u′⊆u₂ afu′ du′⊑u11 u21⊑cu′) refl =
      ⟨ u′ , ⟨ afu′ , ⟨ u′⊆u₂ , ⟨ du′⊑u11 , u21⊑cu′ ⟩ ⟩ ⟩ ⟩


{-
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
      ⟨ v , ⟨ (λ {x₁} x₂ → x₂) , ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩ ⟩ ⟩

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
⊑-cod {u₁ ↦ u₂} {v} (⊑-fun x sfv dv⊑v w⊑cv) afu = {!!}
-}

{-
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
-}
{-
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
-}

         

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


sub-inv-trans : ∀{u′ u₂ u : Value}
    → AllFun u′  →  u′ ⊆ u
    → (∀{v′ w′} → v′ ↦ w′ ∈ u′ → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
      ---------------------------------------------------------------
    → Σ[ u₃ ∈ Value ] factor u₂ u₃ (dom u′) (cod u′)
sub-inv-trans {⊥} {u₂} {u} () u′⊆u IH
sub-inv-trans {const k} {u₂} {u} () u′⊆u IH
sub-inv-trans {u₁′ ↦ u₂′} {u₂} {u} fu′ u′⊆u IH = IH refl
sub-inv-trans {u₁′ ⊔ u₂′} {u₂} {u} ⟨ afu₁′ , afu₂′ ⟩ u′⊆u IH
    with sub-inv-trans {u₁′} {u₂} {u} afu₁′
               (λ {u₁} z → u′⊆u (inj₁ z)) (λ {v′} {w′} z → IH (inj₁ z))
    | sub-inv-trans {u₂′} {u₂} {u} afu₂′
               (λ {u₁} z → u′⊆u (inj₂ z)) (λ {v′} {w′} z → IH (inj₂ z))
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u₃⊆ , ⟨ du₃⊑ , ⊑cu₃ ⟩ ⟩ ⟩ ⟩
    | ⟨ u₄ , ⟨ afu₄ , ⟨ u₄⊆ , ⟨ du₄⊑ , ⊑cu₄ ⟩ ⟩ ⟩ ⟩ =

      ⟨ (u₃ ⊔ u₄) , ⟨ ⟨ afu₃ , afu₄ ⟩ , ⟨ G , ⟨ H , I ⟩ ⟩ ⟩ ⟩
    where
    G : ∀ {u₁} → u₁ ∈ u₃ ⊎ u₁ ∈ u₄ → u₁ ∈ u₂
    G {u₁} (inj₁ x) = u₃⊆ x
    G {u₁} (inj₂ y) = u₄⊆ y

    H : dom u₃ ⊔ dom u₄ ⊑ dom u₁′ ⊔ dom u₂′
    H = ⊑-conj-L (⊑-conj-R1 du₃⊑) (⊑-conj-R2 du₄⊑)

    I : cod u₁′ ⊔ cod u₂′ ⊑ cod u₃ ⊔ cod u₄
    I = ⊑-conj-L (⊑-conj-R1 ⊑cu₃) (⊑-conj-R2 ⊑cu₄)


depth : (v : Value) → ℕ
depth ⊥ = zero
depth (const k) = zero
depth (v ↦ w) = suc (max (depth v) (depth w))
depth (v₁ ⊔ v₂) = max (depth v₁) (depth v₂)

size : (v : Value) → ℕ
size ⊥ = zero
size (const k) = zero
size (v ↦ w) = suc (size v + size w)
size (v₁ ⊔ v₂) = suc (size v₁ + size v₂)

measure : (n : ℕ) → (A : Value) → (B : Value) → (C : Value) → Set
measure n A B C =
   (suc (depth A + depth B + depth C) ≤ n)
   ⊎
   ((depth A + depth B + depth C ≡ n) × (suc (size A + size B + size C) ≤ n))

not-measure-zero : ∀{A B C} → ¬ measure zero A B C
not-measure-zero {A} {B} {C} (inj₁ x)
    with n≤0⇒n≡0 x
... | ()
not-measure-zero {A} {B} {C} (inj₂ ⟨ fst , snd ⟩)
    with n≤0⇒n≡0 snd
... | ()

∈→size≤ : ∀{v u : Value} → u ∈ v → size u ≤ size v
∈→size≤ {⊥} {u} u∈v rewrite u∈v = _≤_.z≤n
∈→size≤ {const x} {u} u∈v rewrite u∈v = _≤_.z≤n
∈→size≤ {v ↦ w} {u} u∈v rewrite u∈v = ≤-refl
∈→size≤ {v₁ ⊔ v₂} {u} (inj₁ u∈v₁) =
    begin
      size u
    ≤⟨ ∈→size≤ {v₁}{u} u∈v₁ ⟩
      size v₁
    ≤⟨ m≤m+n (size v₁) (size v₂) ⟩
      size v₁ + size v₂
    ≤⟨ n≤1+n (size v₁ + size v₂) ⟩
      suc (size v₁ + size v₂)
    ∎ 
∈→size≤ {v₁ ⊔ v₂} {u} (inj₂ u∈v₂) =
    begin
      size u
    ≤⟨ ∈→size≤ {v₂}{u} u∈v₂ ⟩
      size v₂
    ≤⟨ n≤m+n (size v₁) (size v₂) ⟩
      size v₁ + size v₂
    ≤⟨ n≤1+n (size v₁ + size v₂) ⟩
      suc (size v₁ + size v₂)
    ∎ 

∈→depth≤ : ∀{v u : Value} → u ∈ v → depth u ≤ depth v
∈→depth≤ {⊥} {u} u∈v rewrite u∈v = _≤_.z≤n
∈→depth≤ {const x} {u} u∈v rewrite u∈v = _≤_.z≤n
∈→depth≤ {v ↦ w} {u} u∈v rewrite u∈v = ≤-refl
∈→depth≤ {v₁ ⊔ v₂} {u} (inj₁ x) =
    ≤-trans (∈→depth≤ {v₁} {u} x) (m≤m⊔n (depth v₁) (depth v₂))
∈→depth≤ {v₁ ⊔ v₂} {u} (inj₂ y) =
    ≤-trans (∈→depth≤ {v₂} {u} y) (n≤m⊔n (depth v₁) (depth v₂))

max-lub : ∀{x y z : ℕ} → x ≤ z → y ≤ z → max x y ≤ z
max-lub {.0} {y} {z} _≤_.z≤n y≤z = y≤z
max-lub {suc x} {.0} {suc z} (_≤_.s≤s x≤z) _≤_.z≤n = _≤_.s≤s x≤z
max-lub {suc x} {suc y} {suc z} (_≤_.s≤s x≤z) (_≤_.s≤s y≤z) =
  let max-xy≤z = max-lub {x}{y}{z} x≤z y≤z in
  _≤_.s≤s max-xy≤z

⊔⊆-inv : ∀{u v w : Value}
       → (u ⊔ v) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = ⟨ (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x)) ⟩

⊆→depth≤ : ∀{u v : Value} → u ⊆ v → depth u ≤ depth v
⊆→depth≤ {⊥} {v} u⊆v = _≤_.z≤n
⊆→depth≤ {const x} {v} u⊆v = _≤_.z≤n
⊆→depth≤ {u₁ ↦ u₂} {v} u⊆v = ∈→depth≤ (u⊆v refl)
⊆→depth≤ {u₁ ⊔ u₂} {v} u⊆v
    with ⊔⊆-inv u⊆v
... | ⟨ u₁⊆v , u₂⊆v ⟩ =
    let u₁≤v = ⊆→depth≤ u₁⊆v in
    let u₂≤v = ⊆→depth≤ u₂⊆v in
    max-lub u₁≤v u₂≤v

dom-depth-≤ : ∀{u : Value} → depth (dom u) ≤ depth u
dom-depth-≤ {⊥} = _≤_.z≤n
dom-depth-≤ {const k} = _≤_.z≤n
dom-depth-≤ {v ↦ w} = ≤-step (m≤m⊔n (depth v) (depth w))
dom-depth-≤ {u ⊔ v} =
  let ih1 = dom-depth-≤ {u} in
  let ih2 = dom-depth-≤ {v} in
  ⊔-mono-≤ ih1 ih2

cod-depth-≤ : ∀{u : Value} → depth (cod u) ≤ depth u
cod-depth-≤ {⊥} = _≤_.z≤n
cod-depth-≤ {const k} = _≤_.z≤n
cod-depth-≤ {v ↦ w} = ≤-step (n≤m⊔n (depth v) (depth w))
cod-depth-≤ {u ⊔ v} =
  let ih1 = cod-depth-≤ {u} in
  let ih2 = cod-depth-≤ {v} in
  ⊔-mono-≤ ih1 ih2

sm+n≡m+sn : ∀{m n} → suc (m + n) ≡ m + suc n
sm+n≡m+sn {zero} {n} = refl
sm+n≡m+sn {suc m} {n} =
  let ih = sm+n≡m+sn {m} {n} in
  start
      suc (suc (m + n))
  ≡⟨ cong suc ih ⟩
      suc (m + suc n)
  □


{-
  Attempting the Bove-Capretta method!
-}
data ⊑t-acc : Value → Value → Value → Set where
  acc-⊥ : ∀{v w} → ⊑t-acc ⊥ v w
  acc-k : ∀{b}{k w} → ⊑t-acc (const {b} k) (const {b} k) w
  acc-u₁⊔u₂ : ∀{u₁ u₂ v w}
            → ⊑t-acc u₁ v w → ⊑t-acc u₂ v w
            → ⊑t-acc (u₁ ⊔ u₂) v w
  acc-v₁⊔v₂-L : ∀{u v₁ v₂ w} → ⊑t-acc u v₁ w → ⊑t-acc u (v₁ ⊔ v₂) w
  acc-v₁⊔v₂-R : ∀{u v₁ v₂ w} → ⊑t-acc u v₂ w → ⊑t-acc u (v₁ ⊔ v₂) w
  acc-u₁↦u₂ : ∀{u₁ u₂ v w}
            → (∀{v′ w′} → AllFun v′ → v′ ⊆ v → AllFun w′ → w′ ⊆ w
                → ⊑t-acc (dom w′) (dom v′) u₁ × ⊑t-acc u₂ (cod v′) (cod w′))
            → ⊑t-acc (u₁ ↦ u₂) v w



u⊑v×v⊑w→⊑t-acc : ∀{u v w}
               → u ⊑ v → v ⊑ w → ⊑t-acc u v w
u⊑v×v⊑w→⊑t-acc {.⊥} {v} {w} ⊑-⊥ v⊑w = acc-⊥
u⊑v×v⊑w→⊑t-acc {.(const _)} {.(const _)} {w} ⊑-const v⊑w = acc-k
u⊑v×v⊑w→⊑t-acc {.(_ ⊔ _)} {v} {w} (⊑-conj-L u⊑v u⊑v₁) v⊑w = acc-u₁⊔u₂ (u⊑v×v⊑w→⊑t-acc u⊑v v⊑w) (u⊑v×v⊑w→⊑t-acc u⊑v₁ v⊑w)
u⊑v×v⊑w→⊑t-acc {u} {v₁ ⊔ v₂} {w} (⊑-conj-R1 u⊑v₁) v⊑w =
   let IH = u⊑v×v⊑w→⊑t-acc {u}{v₁}{w} u⊑v₁ (⊔⊑R v⊑w) in
   acc-v₁⊔v₂-L IH
u⊑v×v⊑w→⊑t-acc {u} {v₁ ⊔ v₂} {w} (⊑-conj-R2 u⊑v₂) v⊑w =
   let IH = u⊑v×v⊑w→⊑t-acc {u}{v₂}{w} u⊑v₂ (⊔⊑L v⊑w) in
   acc-v₁⊔v₂-R IH
u⊑v×v⊑w→⊑t-acc {u₁ ↦ u₂} {v} {w} (⊑-fun{u′ = v′} v′⊆v afv′ dv′⊑u₁ u₂⊑cv′) v⊑w =
  acc-u₁↦u₂ (G v⊑w)
  where
  G : ∀ {v w v′ w′} → v ⊑ w → AllFun v′ → v′ ⊆ v → AllFun w′ → w′ ⊆ w →
        ⊑t-acc (dom w′) (dom v′) u₁ × ⊑t-acc u₂ (cod v′) (cod w′)
  G {v′ = ⊥} ⊑-⊥ () v′⊆v afw′ w′⊆w
  G {v′ = const x} ⊑-⊥ () v′⊆v afw′ w′⊆w
  G {v′ = v′ ↦ v′₁} ⊑-⊥ afv′ v′⊆v afw′ w′⊆w
      with v′⊆v refl
  ... | ()
  G {v′ = v′ ⊔ v′₁} ⊑-⊥ ⟨ fst , snd ⟩ v′⊆v afw′ w′⊆w
      with ⊔⊆-inv{v′}{v′₁}{⊥} v′⊆v
  ... | ⟨ xx , yy ⟩ = ⟨ {!!} , {!!} ⟩
  G ⊑-const afv′ v′⊆v afw′ w′⊆w = {!!}
  G (⊑-conj-L v⊑w v⊑w₁) afv′ v′⊆v afw′ w′⊆w = {!!}
  G (⊑-conj-R1 v⊑w) afv′ v′⊆v afw′ w′⊆w = {!!}
  G (⊑-conj-R2 v⊑w) afv′ v′⊆v afw′ w′⊆w = {!!}
  G (⊑-fun x x₁ v⊑w v⊑w₁) afv′ v′⊆v afw′ w′⊆w = {!!}

⊑-trans : ∀{u v w}{n : ℕ}{m : measure n u v w} → u ⊑ v → v ⊑ w → u ⊑ w
⊑-trans {u} {v} {w}{zero}{m} u⊑v v⊑w =
    ⊥-elim (not-measure-zero {u}{v}{w} m)
⊑-trans {.⊥} {v} {w}{suc n}{m} ⊑-⊥ v⊑w = ⊑-⊥
⊑-trans {const k} {const k′} {w}{suc n}{m} ⊑-const v⊑w = v⊑w
⊑-trans {u₁ ⊔ u₂} {v} {w}{suc n}{m} (⊑-conj-L u₁⊑v u₂⊑v) v⊑w =
    ⊑-conj-L (⊑-trans{m = M1} u₁⊑v v⊑w)
             (⊑-trans{m = M2} u₂⊑v v⊑w)
    where
    M1 : measure n u₁ v w
    M1 = {!!}
    M2 : measure n u₂ v w
    M2 = {!!}
⊑-trans {u} {v₁ ⊔ v₂} {w}{suc n}{m} (⊑-conj-R1 u⊑v₁) v₁⊔v₂⊑w =
    let v₁⊑w = ⊔⊑R v₁⊔v₂⊑w in
    ⊑-trans{m = M} u⊑v₁ v₁⊑w
    where
    M : measure n u v₁ w
    M = {!!}
⊑-trans {u} {v₁ ⊔ v₂} {w}{suc n}{m} (⊑-conj-R2 u⊑v₂) v₁⊔v₂⊑w =
    let v₂⊑w = ⊔⊑L v₁⊔v₂⊑w in
    ⊑-trans{m = M} u⊑v₂ v₂⊑w
    where
    M : measure n u v₂ w
    M = {!!}
⊑-trans {u₁ ↦ u₂} {v} {w}{suc n}{m} (⊑-fun xx sfv dv⊑u₁ u₂⊑cv) v⊑w
    with ⊑-fun-inv {u₁ ↦ u₂} {v} (⊑-fun xx sfv dv⊑u₁ u₂⊑cv) refl
... | ⟨ v′ , ⟨ afv′ , ⟨ v′⊆v , ⟨ dv′⊑u₁ , u₂⊑cv′ ⟩ ⟩ ⟩ ⟩ 
    with sub-inv-trans afv′ v′⊆v (λ {v₁}{v₂} v₁↦v₂∈v′ → ⊑-fun-inv {v′} {w} (u⊆v⊑w→u⊑w v′⊆v v⊑w) v₁↦v₂∈v′)
... | ⟨ w′ , ⟨ afw′ , ⟨ w′⊆w , ⟨ dw′⊑dv′ , cv′⊑cw′ ⟩ ⟩ ⟩ ⟩ =
      let dw′⊑u₁ = ⊑-trans{n = n}{M1 m} dw′⊑dv′ dv′⊑u₁ in
      let u₂⊑cw′ = ⊑-trans{n = n}{M2 m} u₂⊑cv′ cv′⊑cw′ in
      ⊑-fun{u′ = w′} w′⊆w afw′ dw′⊑u₁ u₂⊑cw′
    where
    dw′≤w : depth (dom w′) ≤ depth w
    dw′≤w = begin
              depth (dom w′)
            ≤⟨ dom-depth-≤{w′} ⟩
              depth w′
            ≤⟨ ⊆→depth≤ w′⊆w ⟩
              depth w
            ∎ 
    dv′≤v : depth (dom v′) ≤ depth v
    dv′≤v = begin
              depth (dom v′)
            ≤⟨ dom-depth-≤{v′} ⟩
              depth v′
            ≤⟨ ⊆→depth≤ v′⊆v ⟩
              depth v
            ∎ 
    u₁<u₁↦u₂ : suc (depth u₁) ≤ depth (u₁ ↦ u₂)
    u₁<u₁↦u₂ = s≤s (m≤m⊔n (depth u₁) (depth u₂))

    du12vw≤n : measure (suc n) (u₁ ↦ u₂) v w → depth (u₁ ↦ u₂) + depth v + depth w ≤ suc n
    du12vw≤n (inj₁ x) = {!!}
    du12vw≤n (inj₂ ⟨ refl , snd ⟩) = ≤-refl

    M1 : measure (suc n) (u₁ ↦ u₂) v w → measure n (dom w′) (dom v′) u₁
    M1 (inj₁ m′) =
           inj₁
           (begin
             suc (depth (dom w′) + depth (dom v′) + depth u₁)
           ≤⟨ s≤s (+-mono-≤ (+-mono-≤ dw′≤w ≤-refl) ≤-refl) ⟩
             suc (depth w + depth (dom v′) + depth u₁)
           ≤⟨ s≤s (+-mono-≤ (+-mono-≤{depth w} ≤-refl dv′≤v) ≤-refl) ⟩
             suc ((depth w + depth v) + depth u₁)
           ≤⟨ ≤-reflexive sm+n≡m+sn ⟩
             (depth w + depth v) + suc (depth u₁)
           ≤⟨ +-mono-≤ ≤-refl u₁<u₁↦u₂ ⟩
             (depth w + depth v) + depth (u₁ ↦ u₂)
           ≤⟨ ≤-reflexive (+-comm (depth w + depth v) (depth (u₁ ↦ u₂))) ⟩
             depth (u₁ ↦ u₂) + (depth w + depth v)
           ≤⟨  +-mono-≤ (≤-refl{depth (u₁ ↦ u₂)}) (≤-reflexive (+-comm (depth w) (depth v))) ⟩
             depth (u₁ ↦ u₂) + (depth v + depth w)
           ≤⟨  ≤-reflexive (sym (+-assoc (depth (u₁ ↦ u₂)) (depth v) (depth w))) ⟩
             depth (u₁ ↦ u₂) + depth v + depth w
           ≤⟨ ≤-pred m′ ⟩
             n
           ∎) 
    
    M1 (inj₂ ⟨ fst , snd ⟩) = {!!}
    

    M2 : measure (suc n) (u₁ ↦ u₂) v w → measure n u₂ (cod v′) (cod w′)
    M2 m = {!!}


