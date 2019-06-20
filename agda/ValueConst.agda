open import Primitives
open import Structures

open import Data.Nat using (ℕ; suc ; zero; _+_; _≤′_; _<′_; _<_; _≤_;
    z≤n; s≤s; ≤′-refl; ≤′-step) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; ≤-step; ⊔-mono-≤;
         +-mono-≤; +-mono-≤-<; +-mono-<-≤; +-comm; +-assoc; n≤1+n; 
         ≤-pred; m≤m+n; n≤m+n; ≤-reflexive; ≤′⇒≤; ≤⇒≤′; +-suc)
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
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)

module ValueConst where

infixr 7 _↦_
infixl 6 _⊔_

data Value : Set where
  ⊥ : Value
  const : {b : Base} → base-rep b → Value
  _↦_ : Value → Value → Value
  _⊔_ : (u : Value) → (v : Value) → Value

value_struct : ValueStruct
value_struct = record { Value = Value ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_ }

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

dom : (u : Value) → ∀{a : AllFun u } → Value
dom ⊥ {()}
dom (const k) {()}
dom (v ↦ w) = v
dom (u ⊔ v) { ⟨ fu , fv ⟩ } = dom u {fu} ⊔ dom v {fv}

cod : (u : Value) → ∀{a : AllFun u} → Value
cod ⊥ {()}
cod (const k) {()}
cod (v ↦ w) = w
cod (u ⊔ v) { ⟨ fu , fv ⟩ } = cod u {fu} ⊔ cod v {fv}

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
       → (fu′ : AllFun u′)
       → dom u′ {fu′} ⊑ v
       → w ⊑ cod u′ {fu′}
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

⊔⊑-inv : ∀{B C A}
    → B ⊔ C ⊑ A
    → B ⊑ A × C ⊑ A
⊔⊑-inv B⊔C⊑A  = ⟨ ⊔⊑R B⊔C⊑A , ⊔⊑L B⊔C⊑A ⟩

factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = Σ[ fu′ ∈ AllFun u′ ] u′ ⊆ u
                  × dom u′ {fu′} ⊑ v × w ⊑ cod u′ {fu′}


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
⊑-fun-inv {u11 ↦ u21} {u₂} {v} {w} (⊑-fun{u′ = u′} u′⊆u₂ afu′ du′⊑u11 u21⊑cu′)
    refl =
      ⟨ u′ , ⟨ afu′ , ⟨ u′⊆u₂ , ⟨ du′⊑u11 , u21⊑cu′ ⟩ ⟩ ⟩ ⟩


sub-inv-trans : ∀{u′ u₂ u : Value}
    → (fu′ : AllFun u′)  →  u′ ⊆ u
    → (∀{v′ w′} → v′ ↦ w′ ∈ u′ → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
      ---------------------------------------------------------------
    → Σ[ u₃ ∈ Value ] factor u₂ u₃ (dom u′ {fu′}) (cod u′ {fu′})
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

dom-depth-≤ : ∀{u : Value}{fu : AllFun u} → depth (dom u {fu}) ≤ depth u
dom-depth-≤ {⊥}{()}
dom-depth-≤ {const k}{()}
dom-depth-≤ {v ↦ w} = ≤-step (m≤m⊔n (depth v) (depth w))
dom-depth-≤ {u ⊔ v} =
  let ih1 = dom-depth-≤ {u} in
  let ih2 = dom-depth-≤ {v} in
  ⊔-mono-≤ ih1 ih2

cod-depth-≤ : ∀{u : Value}{fu : AllFun u} → depth (cod u {fu}) ≤ depth u
cod-depth-≤ {⊥}{()}
cod-depth-≤ {const k}{()}
cod-depth-≤ {v ↦ w} = ≤-step (n≤m⊔n (depth v) (depth w))
cod-depth-≤ {u ⊔ v} {⟨ fu , fv ⟩} =
  let ih1 = cod-depth-≤ {u}{fu} in
  let ih2 = cod-depth-≤ {v}{fv} in
  ⊔-mono-≤ ih1 ih2

≤′-trans : ∀{x y z} → x ≤′ y → y ≤′ z → x ≤′ z
≤′-trans x≤′y y≤′z = ≤⇒≤′ (≤-trans (≤′⇒≤ x≤′y) (≤′⇒≤ y≤′z))

data _<<_ : ℕ × ℕ → ℕ × ℕ → Set where
  fst : ∀{x x' y y'} → x <′ x' → ⟨ x , y ⟩ << ⟨ x' , y' ⟩
  snd : ∀{x x' y y'} → x ≤′ x' → y <′ y' → ⟨ x , y ⟩ << ⟨ x' , y' ⟩

{- 

  The following is based on code from Pierre-Evariste Dagand.
  https://pages.lip6.fr/Pierre-Evariste.Dagand/stuffs/notes/html/Bove.html
 -}
<<-wellfounded : (P : ℕ → ℕ → Set) →
         (∀ x y → (∀ {x' y'} → ⟨ x' , y' ⟩ << ⟨ x , y ⟩ → P x' y') → P x y) →
         ∀ x y → P x y
<<-wellfounded P ih x y = ih x y (help x y)
  where help : (x y : ℕ) → ∀{ x' y'} → ⟨ x' , y' ⟩ << ⟨ x , y ⟩ → P x' y'
        help .(suc x') y {x'}{y'} (fst ≤′-refl) =
            ih x' y' (help x' y') 
        help .(suc x) y {x'}{y'} (fst (≤′-step {x} q)) =
            help x y {x'}{y'} (fst q)
        help x .(suc y) {x'}{y} (snd x'≤x ≤′-refl) =
            let h : ∀ {x₁} {x₂} → (⟨ x₁ , x₂ ⟩ << ⟨ x , y ⟩) → P x₁ x₂
                h = help x y in
            ih x' y G
            where
            G : ∀ {x'' y'} → ⟨ x'' , y' ⟩ << ⟨ x' , y ⟩ → P x'' y'
            G {x''} {y'} (fst x''<x') =
               help x y (fst {y = y'}{y' = y} (≤′-trans x''<x' x'≤x))
            G {x''} {y'} (snd x''≤x' y'<y) =
               help x y {x''}{y'} (snd (≤′-trans x''≤x' x'≤x) y'<y)
        help x .(suc y) {x'}{y'} (snd x′≤x (≤′-step {y} q)) =
            help x y {x'}{y'} (snd x′≤x q)


⊑-trans-P : ℕ → ℕ → Set
⊑-trans-P d s = ∀{u v w} → d ≡ depth u + depth w → s ≡ size u + size v
                         → u ⊑ v → v ⊑ w → u ⊑ w

⊑-trans-rec : ∀ d s → ⊑-trans-P d s
⊑-trans-rec = <<-wellfounded ⊑-trans-P helper
  where
  helper : ∀ x y 
         → (∀ {x' y'} → ⟨ x' , y' ⟩ << ⟨ x , y ⟩ → ⊑-trans-P x' y')
         → ⊑-trans-P x y
  helper d s IH {.⊥} {v} {w} d≡ s≡ ⊑-⊥ v⊑w = ⊑-⊥
  helper d s IH {.(const _)} {.(const _)} {w} d≡ s≡ ⊑-const v⊑w = v⊑w
  helper d s IH {u₁ ⊔ u₂} {v} {w} d≡ s≡ (⊑-conj-L u₁⊑v u₂⊑v) v⊑w
      rewrite d≡ | s≡ =
      let u₁⊑w = IH M1 {u₁}{v}{w} refl refl u₁⊑v v⊑w in
      let u₂⊑w = IH M2 {u₂}{v}{w} refl refl u₂⊑v v⊑w in
      ⊑-conj-L u₁⊑w u₂⊑w
      where
      M1a = begin
               depth u₁ + depth w
             ≤⟨ +-mono-≤ (m≤m⊔n (depth u₁) (depth u₂)) ≤-refl ⟩
               max (depth u₁) (depth u₂) + depth w
            ∎
      M1b = begin
               suc (size u₁ + size v)
            ≤⟨ s≤s (+-mono-≤ ≤-refl (n≤m+n (size u₂) (size v))) ⟩
               suc (size u₁ + (size u₂ + size v))
            ≤⟨ s≤s (≤-reflexive (sym (+-assoc (size u₁) (size u₂) (size v)))) ⟩
               suc (size u₁ + size u₂ + size v)
            ∎ 
      M1 : ⟨ depth u₁ + depth w , size u₁ + size v ⟩ <<
           ⟨ max (depth u₁) (depth u₂) + depth w ,
             suc (size u₁ + size u₂ + size v) ⟩
      M1 = snd (≤⇒≤′ M1a) (≤⇒≤′ M1b)
      M2a = begin
               depth u₂ + depth w
             ≤⟨ +-mono-≤ (n≤m⊔n (depth u₁) (depth u₂)) ≤-refl ⟩
               max (depth u₁) (depth u₂) + depth w
            ∎
      M2b = begin
               suc (size u₂ + size v)
            ≤⟨ s≤s (+-mono-≤ (n≤m+n (size u₁) (size u₂)) ≤-refl) ⟩
               suc ((size u₁ + size u₂) + size v)
            ∎ 
      M2 : ⟨ depth u₂ + depth w , size u₂ + size v ⟩ <<
           ⟨ max (depth u₁) (depth u₂) + depth w ,
             suc (size u₁ + size u₂ + size v) ⟩
      M2 = snd (≤⇒≤′ M2a) (≤⇒≤′ M2b)
  helper d s IH {u} {v₁ ⊔ v₂} {w} d≡ s≡ (⊑-conj-R1 u⊑v₁) v₁⊔v₂⊑w 
      rewrite d≡ | s≡ =
      let v₁⊑w = ⊔⊑R v₁⊔v₂⊑w in
      IH M {u}{v₁}{w} refl refl u⊑v₁ v₁⊑w
      where
      Ma = begin
              suc (size u + size v₁)
           ≤⟨ ≤-reflexive (sym (+-suc (size u) (size v₁))) ⟩
              size u + suc (size v₁)
           ≤⟨ +-mono-≤ ≤-refl (s≤s (m≤m+n (size v₁) (size v₂))) ⟩
              size u + suc (size v₁ + size v₂)
           ∎ 
      M : ⟨ depth u + depth w , size u + size v₁ ⟩ <<
          ⟨ depth u + depth w , size u + suc (size v₁ + size v₂) ⟩
      M = snd (≤⇒≤′ ≤-refl) (≤⇒≤′ Ma)
  helper d s IH {u} {v₁ ⊔ v₂} {w} d≡ s≡ (⊑-conj-R2 u⊑v₂) v₁⊔v₂⊑w
      rewrite d≡ | s≡ =
      let v₂⊑w = ⊔⊑L v₁⊔v₂⊑w in
      IH M {u}{v₂}{w} refl refl u⊑v₂ v₂⊑w
      where
      Ma = begin
              suc (size u + size v₂)
           ≤⟨ ≤-reflexive (sym (+-suc (size u) (size v₂))) ⟩
              size u + suc (size v₂)
           ≤⟨ +-mono-≤ ≤-refl (s≤s (n≤m+n (size v₁) (size v₂))) ⟩
              size u + suc (size v₁ + size v₂)
           ∎ 
      M : ⟨ depth u + depth w , size u + size v₂ ⟩ <<
          ⟨ depth u + depth w , size u + suc (size v₁ + size v₂) ⟩
      M = snd (≤⇒≤′ ≤-refl) (≤⇒≤′ Ma)
  helper d s IH {u₁ ↦ u₂}{v}{w}d≡ s≡ (⊑-fun{u′ = v′}v′⊆v afv′ dv′⊑u₁ u₂⊑cv′) v⊑w
      rewrite d≡ | s≡
      with sub-inv-trans afv′ v′⊆v
                (λ {v₁}{v₂} v₁↦v₂∈v′ →
                   ⊑-fun-inv {v′} {w} (u⊆v⊑w→u⊑w v′⊆v v⊑w) v₁↦v₂∈v′)
  ... | ⟨ w′ , ⟨ afw′ , ⟨ w′⊆w , ⟨ dw′⊑dv′ , cv′⊑cw′ ⟩ ⟩ ⟩ ⟩ =
        let dw′⊑u₁ = IH M1 {dom w′}{dom v′}{u₁} refl refl dw′⊑dv′ dv′⊑u₁ in
        let u₂⊑cw′ = IH M2 {u₂}{cod v′}{cod w′} refl refl u₂⊑cv′ cv′⊑cw′ in
        ⊑-fun{u′ = w′} w′⊆w afw′ dw′⊑u₁ u₂⊑cw′
      where
      dw′≤w : depth (dom w′) ≤ depth w
      dw′≤w = ≤-trans (dom-depth-≤{w′}) (⊆→depth≤ w′⊆w)
      cw′≤w : depth (cod w′) ≤ depth w
      cw′≤w = ≤-trans (cod-depth-≤{w′}) (⊆→depth≤ w′⊆w)

      M1a = begin
               suc (depth (dom w′) + depth u₁)
            ≤⟨ s≤s (≤-reflexive (+-comm (depth (dom w′)) (depth u₁))) ⟩
               suc (depth u₁ + depth (dom w′))
            ≤⟨ s≤s (+-mono-≤ (m≤m⊔n (depth u₁) (depth u₂)) dw′≤w) ⟩
               suc (max (depth u₁) (depth u₂) + depth w)
            ∎ 
      M1 : ⟨ depth (dom w′) + depth u₁ , size (dom w′) + size (dom v′) ⟩
        << ⟨ suc (max (depth u₁) (depth u₂) + depth w) ,
             suc (size u₁ + size u₂ + size v) ⟩
      M1 = fst (≤⇒≤′ M1a)
      M2a = begin
               suc (depth u₂ + depth (cod w′))
            ≤⟨ s≤s (+-mono-≤ (n≤m⊔n (depth u₁) (depth u₂)) cw′≤w) ⟩
               suc (max (depth u₁) (depth u₂) + depth w)
            ∎ 
      M2 : ⟨ depth u₂ + depth (cod w′) ,
             size u₂ + size (cod v′) ⟩
        << ⟨ suc (max (depth u₁) (depth u₂) + depth w) ,
             suc (size u₁ + size u₂ + size v) ⟩
      M2 = fst (≤⇒≤′ M2a)


⊑-trans : ∀{u v w} → u ⊑ v → v ⊑ w → u ⊑ w
⊑-trans {u} {v} {w} u⊑v v⊑w =
    ⊑-trans-rec (depth u + depth w) (size u + size v) refl refl u⊑v v⊑w

{-
  The traditional function subtyping rule is admissible.
 -}

⊑-fun′ : ∀{v w v′ w′}
       → v′ ⊑ v
       → w ⊑ w′
         -------------------
       → (v ↦ w) ⊑ (v′ ↦ w′)
⊑-fun′ {v}{w}{v′}{w′} v′⊑v w⊑w′ =
    ⊑-fun {v′ ↦ w′}{v′ ↦ w′}{v}{w} (λ {u} z → z) tt v′⊑v w⊑w′

{-
  The traditional distributivity rule is admissible.
 -}

⊑-dist : ∀{v w w′}
         ---------------------------------
       → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)
⊑-dist {v}{w}{w′} =
  ⊑-fun {(v ↦ w) ⊔ (v ↦ w′)} {(v ↦ w) ⊔ (v ↦ w′)} {v} {w ⊔ w′}
        (λ {u} z → z) ⟨ tt , tt ⟩
        (⊑-conj-L ⊑-refl ⊑-refl)
        ((⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)))

{-

  The usual inversion rule for function subtyping.

 -}

AllFun∈ : ∀{u}
      → AllFun u
      → Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ∈ u
AllFun∈ {⊥} ()
AllFun∈ {const k} ()
AllFun∈ {v ↦ w} afu = ⟨ v , ⟨ w , refl ⟩ ⟩
AllFun∈ {u₁ ⊔ u₂} ⟨ fst₁ , snd₁ ⟩
    with AllFun∈ {u₁} fst₁
... | ⟨ v , ⟨ w , vw∈u ⟩ ⟩ =
      ⟨ v , ⟨ w , inj₁ vw∈u ⟩ ⟩

⊆↦→cod⊆ : ∀{u v w : Value} {fu : AllFun u}
        → u ⊆ v ↦ w
          --------------
        → cod u {fu} ⊆ w
⊆↦→cod⊆ {⊥} {fu = ()}
⊆↦→cod⊆ {const {B} k} {fu = ()}
⊆↦→cod⊆ {C ↦ C′} s u∈C′
    with s {C ↦ C′} refl
... | refl = u∈C′
⊆↦→cod⊆ {u₁ ⊔ u₂}{v}{w} u⊆v↦w {v′} v′∈u′
    with v′∈u′
... | inj₁ v′∈v₁ =     
      ⊆↦→cod⊆ (λ x → u⊆v↦w (inj₁ x)) v′∈v₁
... | inj₂ v′∈v₂ =
      ⊆↦→cod⊆ (λ x → u⊆v↦w (inj₂ x)) v′∈v₂


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

↦∈→⊆dom : ∀{u v w : Value} {fu : AllFun u}
      → (v ↦ w) ∈ u
        ----------------------------
      → v ⊆ dom u {fu}
↦∈→⊆dom {⊥} {fu = ()} eq 
↦∈→⊆dom {const {B} k} {fu = ()} eq
↦∈→⊆dom {u₁ ↦ u₂}{v}{w} refl {v′} v′∈u₁ = v′∈u₁
↦∈→⊆dom {u₁ ⊔ u₂} {v} {w} {⟨ f1 , f2 ⟩} (inj₁ v↦w∈u₁) {v'} v'∈v =
    inj₁ (↦∈→⊆dom {u₁}{v}{fu = f1} v↦w∈u₁ v'∈v)
↦∈→⊆dom {u₁ ⊔ u₂} {v} {w} {⟨ f1 , f2 ⟩} (inj₂ v↦w∈u₂) {v'} v'∈v =
    inj₂ (↦∈→⊆dom {u₂}{v}{fu = f2} v↦w∈u₂ v'∈v)

⊑-fun-inv′ : ∀{v w v′ w′}
        → v ↦ w ⊑ v′ ↦ w′
          -----------------
        → v′ ⊑ v × w ⊑ w′
⊑-fun-inv′ {v}{w}{v′}{w′} lt
    with ⊑-fun-inv lt refl
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with AllFun∈ f
... | ⟨ u , ⟨ u′ , u↦u′∈Γ ⟩ ⟩
    with Γ⊆v34 u↦u′∈Γ
... | refl =    
  let codΓ⊆w′ = ⊆↦→cod⊆ Γ⊆v34 in
  let u⊆domΓ = ↦∈→⊆dom{Γ}{fu = f} u↦u′∈Γ in
  ⟨ ⊑-trans (⊆→⊑ u⊆domΓ) lt1 , ⊑-trans lt2 (⊆→⊑ codΓ⊆w′) ⟩


ordering : ValueOrdering value_struct
ordering = record
             { _⊑_ = _⊑_
             ; ⊑-⊥ = ⊑-⊥
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-trans = ⊑-trans
             ; ⊑-fun = ⊑-fun′
             ; ⊑-refl = ⊑-refl
             ; ⊑-dist = ⊑-dist
             }

{-

 Consistency

-}

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

~⊔R : ∀{v u₁ u₂} → v ~ u₁ → v ~ u₂
    → v ~ (u₁ ⊔ u₂)
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
~-sym {v ↦ w} {v′ ↦ w′} (inj₁ ⟨ v~v′ , w~w′ ⟩) =
   inj₁ ⟨ ~-sym{v} v~v′ , ~-sym{w} w~w′ ⟩
~-sym {v ↦ w} {v′ ↦ w′} (inj₂ ¬v~v′) =
  inj₂ λ v′~v → ⊥-elim (contradiction (~-sym{v′} v′~v) ¬v~v′)
~-sym {v ↦ w} {u₁ ⊔ u₂} ⟨ fst₁ , snd₁ ⟩ =
    ⟨ ~-sym{v ↦ w}{u₁} fst₁ , ~-sym{v ↦ w}{u₂} snd₁ ⟩
~-sym {u₁ ⊔ u₂} {⊥} _ = tt
~-sym {u₁ ⊔ u₂} {const k} ⟨ fst1 , snd1 ⟩ =
   ⟨ ~-sym{u = u₁} fst1 , ~-sym{u = u₂} snd1 ⟩
~-sym {u₁ ⊔ u₂} {v ↦ v₁} ⟨ fst1 , snd1 ⟩ =
   ⟨ ~-sym{u = u₁} fst1 , ~-sym{u = u₂} snd1 ⟩
~-sym {u₁ ⊔ u₂} {v₁ ⊔ v₂} ⟨ fst1 , snd1 ⟩ 
    with ~-sym {u₁} {v₁ ⊔ v₂} fst1
       | ~-sym {u₂} {v₁ ⊔ v₂} snd1
... | ⟨ v₁~u₁ , v₂~u₁ ⟩ | ⟨ v₁~u₂ , v₂~u₂ ⟩ =
      ⟨ ~⊔R{v = v₁} v₁~u₁ v₁~u₂ , ~⊔R{v = v₂} v₂~u₁ v₂~u₂ ⟩



~-↦-cong : ∀{u v u′ v′} → u ~ u′ → v ~ v′ → (u ↦ v) ~ (u′ ↦ v′)
~-↦-cong = λ z z₁ → inj₁ ⟨ z , z₁ ⟩

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

u~v⊔w : ∀{u v w} → u ~ v → u ~ w → u ~ (v ⊔ w)
u~v⊔w {⊥} {v} {w} u~v u~w = tt
u~v⊔w {const k} {v} {w} u~v u~w = ⟨ u~v , u~w ⟩
u~v⊔w {u₁ ↦ u₂} {v} {w} u~v u~w = ⟨ u~v , u~w ⟩
u~v⊔w {u₁ ⊔ u₂} {v} {w} u~v u~w =
  ⟨ (u~v⊔w {u₁} (proj₁ u~v) (proj₁ u~w)) ,
    (u~v⊔w {u₂} (proj₂ u~v) (proj₂ u~w)) ⟩

~-⊔-cong : ∀{u v u′ v′}
             → (u ~ u′) → (u ~ v′)
             → (v ~ u′) → (v ~ v′)
             → (u ⊔ v) ~ (u′ ⊔ v′)
~-⊔-cong {u}{v}{u′}{v′} u~u′ u~v′ v~u′ v~v′ =
  ⟨ u~v⊔w {u}{u′}{v′} u~u′ u~v′ , u~v⊔w {v}{u′}{v′} v~u′ v~v′ ⟩

atoms→consistent : ∀{u v}
                 → (∀{u′ v′} → u′ ∈ u → v′ ∈ v → u′ ~ v′)
                 → u ~ v
atoms→consistent {⊥} {v} atoms = tt
atoms→consistent {const k} {⊥} atoms = tt
atoms→consistent {const k} {const k′} atoms =
    atoms {const k} {const k′} refl refl
atoms→consistent {const k} {v ↦ w} atoms =
    ⊥-elim (atoms {const k} {v ↦ w} refl refl)
atoms→consistent {const k} {v₁ ⊔ v₂} atoms =
    ⟨ atoms→consistent{const k}{v₁} (λ {u′} {v′} z z₁ → atoms z (inj₁ z₁)) ,
      atoms→consistent{const k}{v₂} (λ {u′} {v′} z z₁ → atoms z (inj₂ z₁)) ⟩
atoms→consistent {u ↦ w} {⊥} atoms = tt
atoms→consistent {u ↦ w} {const k} atoms =
    ⊥-elim (atoms {u ↦ w}{const k} refl refl)
atoms→consistent {u ↦ w} {v₁ ↦ v₂} atoms =
    atoms {u ↦ w} {v₁ ↦ v₂ } refl refl
atoms→consistent {u ↦ w} {v₁ ⊔ v₂} atoms =
    ⟨ atoms→consistent{u ↦ w}{v₁}(λ {u′}{v′} z z₁ → atoms z (inj₁ z₁)) ,
      atoms→consistent{u ↦ w}{v₂} (λ {u′} {v′} z z₁ → atoms z (inj₂ z₁)) ⟩
atoms→consistent {u₁ ⊔ u₂} {v} atoms =
    ⟨ atoms→consistent (λ {u′} {v′} z → atoms (inj₁ z)) ,
      atoms→consistent (λ {u′} {v′} z → atoms (inj₂ z)) ⟩
      

consistent→atoms : ∀ {u v u′ v′} → u ~ v → u′ ∈ u → v′ ∈ v → u′ ~ v′
consistent→atoms {⊥} {v} {u′} {v′} u~v u′∈u v′∈v rewrite u′∈u = tt
consistent→atoms {const {B} k} {⊥} {u′} {v′} u~v u′∈u v′∈v
    rewrite u′∈u | v′∈v = tt
consistent→atoms {const {B} k} {const {B′} k′} {u′} {v′} u~v u′∈u v′∈v
    rewrite u′∈u | v′∈v
    with base-eq? B B′
... | yes refl = u~v
... | no neq = u~v
consistent→atoms {const {B} k} {v ↦ w} {u′} {v′} () u′∈u v′∈v
consistent→atoms {const {B} k} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst' , snd' ⟩ u′∈u
    (inj₁ v′∈v₁) rewrite u′∈u = consistent→atoms{const {B} k} fst' refl v′∈v₁
consistent→atoms {const {B} k} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst' , snd' ⟩ u′∈u
    (inj₂ v′∈v₂) rewrite u′∈u =  consistent→atoms{const {B} k} snd' refl v′∈v₂
consistent→atoms {u ↦ w} {⊥} {u′} {v′} u~v u′∈u v′∈v rewrite u′∈u | v′∈v = tt
consistent→atoms {u ↦ w} {const x} {u′} {v′} () u′∈u v′∈v
consistent→atoms {u ↦ w} {v₁ ↦ v₂} {u′} {v′} (inj₁ ⟨ fst' , snd' ⟩) u′∈u v′∈v
    rewrite u′∈u | v′∈v = inj₁ ⟨ fst' , snd' ⟩
consistent→atoms {u ↦ w} {v₁ ↦ v₂} {u′} {v′} (inj₂ y) u′∈u v′∈v
    rewrite u′∈u | v′∈v = inj₂ y
consistent→atoms {u ↦ w} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst' , snd' ⟩ u′∈u (inj₁ x)
    rewrite u′∈u = consistent→atoms {u ↦ w}{v₁} fst' refl x
consistent→atoms {u ↦ w} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst' , snd' ⟩ u′∈u (inj₂ y)
    rewrite u′∈u = consistent→atoms {u ↦ w}{v₂} snd' refl y
consistent→atoms {u₁ ⊔ u₂} {v} {u′} {v′} ⟨ u₁~v , u₂~v ⟩ (inj₁ u′∈u₁) v′∈v =
    consistent→atoms u₁~v u′∈u₁ v′∈v
consistent→atoms {u₁ ⊔ u₂} {v} {u′} {v′} ⟨ u₁~v , u₂~v ⟩ (inj₂ u′∈u₂) v′∈v =
    consistent→atoms u₂~v u′∈u₂ v′∈v

data wf : Value → Set where
  wf-bot : wf ⊥
  wf-const : ∀{B}{k : base-rep B} → wf (const {B} k)
  wf-fun : ∀{v w} → wf v → wf w → wf (v ↦ w)
  wf-⊔ : ∀{u v} → u ~ v → wf u → wf v → wf (u ⊔ v)

~-refl : ∀{v}{w : wf v} → v ~ v
~-refl {⊥} = tt
~-refl {const {B} k} 
    with base-eq? B B
... | yes eq rewrite eq = refl
... | no neq = neq refl
~-refl {v ↦ w}{wf-fun wfv wfw} =
    inj₁ ⟨ ~-refl {v}{wfv} , ~-refl {w}{wfw} ⟩
~-refl {v₁ ⊔ v₂}{wf-⊔ v₁~v₂ wfv₁ wfv₂} =
    ⟨ ~⊔R {v₁} (~-refl {v₁}{wfv₁}) v₁~v₂ ,
      ~⊔R {v₂} (~-sym {v₁} v₁~v₂) (~-refl {v₂}{wfv₂}) ⟩

u~v⊔w→u~v : ∀{u v w}
          → u ~ v ⊔ w
          → u ~ v
u~v⊔w→u~v {⊥} {v} {w} u~v⊔w = tt
u~v⊔w→u~v {const k} {v} {w} u~v⊔w = proj₁ u~v⊔w
u~v⊔w→u~v {u₁ ↦ u₂} {v} {w} u~v⊔w = proj₁ u~v⊔w
u~v⊔w→u~v {u₁ ⊔ u₂} {v} {w} ⟨ fst₁ , snd₁ ⟩ =
    ⟨ u~v⊔w→u~v {u₁} fst₁ , u~v⊔w→u~v {u₂} snd₁ ⟩

u~v⊔w→u~w : ∀{u v w}
          → u ~ v ⊔ w
          → u ~ w
u~v⊔w→u~w {⊥} {v} {w} u~v⊔w = tt
u~v⊔w→u~w {const x} {v} {w} u~v⊔w = proj₂ u~v⊔w
u~v⊔w→u~w {u ↦ u₁} {v} {w} u~v⊔w = proj₂ u~v⊔w
u~v⊔w→u~w {u₁ ⊔ u₂} {v} {w} ⟨ fst₁ , snd₁ ⟩ =
    ⟨ u~v⊔w→u~w {u₁} fst₁ , u~v⊔w→u~w {u₂} snd₁ ⟩


wf-∈ : ∀{v v′} → v′ ∈ v → wf v → wf v′
wf-∈ {.⊥} {v′} refl wf-bot = wf-bot
wf-∈ {.(const _)} {v′} refl wf-const = wf-const
wf-∈ {.(_ ↦ _)} {v′} refl (wf-fun wfv wfv₁) = wf-fun wfv wfv₁
wf-∈ {.(_ ⊔ _)} {v′} (inj₁ x₁) (wf-⊔ x wfv wfv₁) = wf-∈ x₁ wfv
wf-∈ {.(_ ⊔ _)} {v′} (inj₂ y) (wf-⊔ x wfv wfv₁) = wf-∈ y wfv₁

wf-∈-~ : ∀{u v w} → wf w → u ∈ w → v ∈ w → u ~ v
wf-∈-~ {u}{v}{w} wfw u∈w v∈w =
  consistent→atoms{w}{w}{u}{v} (~-refl{w}{wfw}) u∈w v∈w

wf-⊆-~ : ∀{u v w} → wf w → u ⊆ w → v ⊆ w → u ~ v
wf-⊆-~ {u}{v}{w} wfw u⊆w v⊆w =
  atoms→consistent{u}{v} λ {u′ v′} u′∈u v′∈v →
     wf-∈-~{u′}{v′}{w} wfw (u⊆w u′∈u) (v⊆w v′∈v)

wf-⊆ : ∀{v v′} → v′ ⊆ v → wf v → wf v′
wf-⊆ {v} {⊥} v′⊆v wfv = wf-bot
wf-⊆ {v} {const x} v′⊆v wfv = wf-const
wf-⊆ {v} {v′ ↦ v′₁} v′⊆v wfv
    with v′⊆v refl
... | v′↦v′₁∈v = wf-∈ v′↦v′₁∈v wfv
wf-⊆ {v} {v′ ⊔ v′₁} v′⊔v′₁⊆v wfv
    with ⊔⊆-inv v′⊔v′₁⊆v
... | ⟨ v′⊆v , v′₁⊆v ⟩ =
    wf-⊔ (wf-⊆-~ wfv v′⊆v v′₁⊆v) (wf-⊆ v′⊆v wfv) (wf-⊆ v′₁⊆v wfv)

