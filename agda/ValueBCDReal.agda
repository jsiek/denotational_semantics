{- BCD, exactly as in Barendregt 2013 -}

open import Primitives
open import Structures

open import Data.Nat using (ℕ; suc ; zero; _+_; _≤′_; _<′_; _<_; _≤_;
    z≤n; s≤s; ≤′-refl; ≤′-step) renaming (_⊔_ to max; _≟_ to _=ℕ_)
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
  using (_≡_; _≢_; refl; sym; cong; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)

module ValueBCDReal where

infixr 7 _↦_
infixl 6 _⊔_

data Value : Set where
  ⊥ : Value
  const : ℕ → Value
  _↦_ : Value → Value → Value
  _⊔_ : (u : Value) → (v : Value) → Value

value_struct : ValueStruct
value_struct = record { Value = Value ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_ }

_≟_ : ∀ (x y : Value) → Dec (x ≡ y)
⊥ ≟ ⊥ = yes refl
⊥ ≟ const x = no λ ()
⊥ ≟ (v ↦ v₁) = no (λ ())
⊥ ≟ (v ⊔ v₁) = no (λ ())
const x ≟ ⊥ = no (λ ())
const x ≟ const y
    with x =ℕ y
... | yes refl = yes refl
... | no neq = no G
   where G : ¬ const x ≡ const y
         G refl = neq refl
const x ≟ (v ↦ v₁) = no (λ ())
const x ≟ (v ⊔ v₁) = no (λ ())
(u ↦ u₁) ≟ ⊥ = no (λ ())
(u ↦ u₁) ≟ const x = no (λ ())
(u ↦ u₁) ≟ (v ↦ v₁)
    with u ≟ v | u₁ ≟ v₁
... | yes refl | yes refl = yes refl
... | yes e1 | no e2 = no G
    where G : ¬ u ↦ u₁ ≡ v ↦ v₁
          G refl = e2 refl
(u ↦ u₁) ≟ (v ↦ v₁) | no e1 | _ = no G
    where G : ¬ u ↦ u₁ ≡ v ↦ v₁
          G refl = e1 refl
(u ↦ u₁) ≟ (v ⊔ v₁) = no (λ ())
(u ⊔ u₁) ≟ ⊥ = no (λ ())
(u ⊔ u₁) ≟ const x = no (λ ())
(u ⊔ u₁) ≟ (v ↦ v₁) = no (λ ())
(u ⊔ u₁) ≟ (v ⊔ v₁)
    with u ≟ v | u₁ ≟ v₁
... | yes refl | yes refl = yes refl
... | yes e1 | no e2 = no G
    where G : ¬ u ⊔ u₁ ≡ v ⊔ v₁
          G refl = e2 refl
(u ⊔ u₁) ≟ (v ⊔ v₁) | no e1 | _ = no G
    where G : ¬ u ⊔ u₁ ≡ v ⊔ v₁
          G refl = e1 refl

infix 5 _∈_

_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ const k = u ≡ const k
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

AllBot : (u : Value) → Set
AllBot ⊥ = ⊤
AllBot (const x) = Bot
AllBot (v ↦ w) = AllBot w
AllBot (u ⊔ v) = AllBot u × AllBot v 

AllBot? : (u : Value) → Dec (AllBot u)
AllBot? ⊥ = yes tt
AllBot? (const k) = no (λ z → z)
AllBot? (u₁ ↦ u₂) = AllBot? u₂
AllBot? (u₁ ⊔ u₂)
    with AllBot? u₁ | AllBot? u₂
... | yes x | yes y = yes ⟨ x , y ⟩    
... | yes x | no y = no λ z → y (proj₂ z)    
... | no x | _ = no λ z → x (proj₁ z)     

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

NonFun : (u : Value) → Set
NonFun ⊥ = ⊤
NonFun (const x) = ⊤
NonFun (v ↦ w) = Bot
NonFun (u ⊔ v) = NonFun u ⊎ NonFun v 

NoFun : (u : Value) → Set
NoFun ⊥ = ⊤
NoFun (const x) = ⊤
NoFun (v ↦ w) = Bot
NoFun (u ⊔ v) = NoFun u × NoFun v 

NoFun→NonFun : ∀{u} → NoFun u → NonFun u
NoFun→NonFun {⊥} nfu = tt
NoFun→NonFun {const x} nfu = tt
NoFun→NonFun {u ↦ u₁} nfu = nfu
NoFun→NonFun {u ⊔ u₁} nfu = inj₁ (NoFun→NonFun (proj₁ nfu))

infix 4 _<:_

{- warning, flipped from the standard! (to match ⊑) -}

data _<:_ : Value → Value → Set where

  <:-refl : ∀{v} → v <: v
  
  <:-incl-L : ∀{u v}
         → u <: u ⊔ v
         
  <:-incl-R : ∀{u v}
         → v <: u ⊔ v
         
  <:-glb : ∀{u v w}
      → v <: u
      → w <: u
        -----------
      → v ⊔ w <: u

  <:-trans : ∀{u v w} → u <: v → v <: w → u <: w

  <:-U-top : ∀{v} → ⊥ <: v

  <:-U→ : ∀{v} → v ↦ ⊥ <: ⊥

  <:-→⊔ : ∀{v w w′}
       → v ↦ (w ⊔ w′) <: (v ↦ w) ⊔ (v ↦ w′)

  <:-→ : ∀{v w v′ w′}
       → v′ <: v
       → w <: w′
         -------------------
       → (v ↦ w) <: (v′ ↦ w′)



infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-const : ∀ {k} → const k ⊑ const k

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

  ⊑-↦⊥ : ∀{u v w}
       → AllBot w
         ---------
       → v ↦ w ⊑ u
       
  ⊑-fun : ∀ {u u′ v w}
       → ¬ (AllBot w)
       → u′ ⊆ u
       → (fu′ : AllFun u′)
       → (∀{v′ w′} → AllBot w′ → ¬ (v′ ↦ w′ ∈ u′))
       → dom u′ {fu′} ⊑ v
       → w ⊑ cod u′ {fu′}
         -------------------
       → v ↦ w ⊑ u

       
{-
 v' ⊑ v

 v ↦ (⊥ ⊔ ⊥) ⊑  v' ↦ ⊥

-}  

⊑-refl : ∀{v} → v ⊑ v
⊑-refl {⊥} = ⊑-⊥
⊑-refl {const k} = ⊑-const
⊑-refl {v ↦ w}
    with AllBot? w
... | yes bw = ⊑-↦⊥ bw
... | no w≠⊥ = ⊑-fun{v ↦ w}{v ↦ w} w≠⊥ (λ {u} z → z) tt G (⊑-refl{v}) ⊑-refl
    where G : {v′ w′ : Value} → AllBot w′ → ¬ v′ ↦ w′ ≡ v ↦ w
          G {v′} {⊥} bw refl = w≠⊥ tt
          G {v′} {const x} bw refl = bw
          G {v′} {w′ ↦ w′₁} bw refl = w≠⊥ bw
          G {v′} {w′ ⊔ w′₁} bw refl = w≠⊥ bw

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

⊔⊆-inv : ∀{u v w : Value}
       → (u ⊔ v) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = ⟨ (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x)) ⟩

⊆⊥⊑ : ∀{v w} → v ⊆ ⊥ → v ⊑ w
⊆⊥⊑ {⊥} {w} v⊆⊥ = ⊑-⊥
⊆⊥⊑ {const x} {w} v⊆⊥
    with v⊆⊥ refl
... | ()    
⊆⊥⊑ {v ↦ v₁} {w} v⊆⊥
    with v⊆⊥ refl
... | ()    
⊆⊥⊑ {v₁ ⊔ v₂} {w} v⊆⊥
    with ⊔⊆-inv{w = ⊥} v⊆⊥
... | ⟨ xx , yy ⟩ = ⊑-conj-L (⊆⊥⊑{v₁}{w} xx) (⊆⊥⊑{v₂}{w} yy)

{-
NonFun-⊑ : ∀{v w} → v ⊑ w → NonFun v → NonFun w
NonFun-⊑ {v}{w} v⊑w nfv = {!!}
-}

{-
↦⊑→↦∈ : ∀{v w u}
       → v ↦ w ⊑ u
       → (Σ[ v' ∈ Value ] Σ[ w' ∈ Value ] v' ↦ w' ∈ u) ⊎ u ⊆ ⊥ 
↦⊑→↦∈ {v} {w} {u₁ ⊔ u₂} (⊑-conj-R1 v↦w⊑u₁)
    with ↦⊑→↦∈ {v} {w} {u₁} v↦w⊑u₁
... | inj₁ x = {!!}
... | inj₂ x = {!!}
↦⊑→↦∈ {v} {w} {.(_ ⊔ _)} (⊑-conj-R2 v↦w⊑u) = {!!}
↦⊑→↦∈ {v} {w} {u} (⊑-fun x fu′ v↦w⊑u v↦w⊑u₁) =
  inj₁ ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩
↦⊑→↦∈ {v} {.⊥} {u} (⊑-↦⊥ x) = inj₂ x

↦∈⊑→↦∈ : ∀{v w u u'}
       → v ↦ w ∈ u → u ⊑ u'
       → Σ[ v' ∈ Value ] Σ[ w' ∈ Value ] v' ↦ w' ∈ u'
↦∈⊑→↦∈ {u = ⊥} () u⊑u'
↦∈⊑→↦∈ {u = const k} () u⊑u'
↦∈⊑→↦∈ {u = u ↦ u₁} refl u⊑u' = ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩
↦∈⊑→↦∈ {u = u ⊔ u₁} v↦w∈u u⊑u' = {!!}
-}

factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = (Σ[ fu′ ∈ AllFun u′ ] u′ ⊆ u
                    × (∀{v′ w′} → AllBot w′ → ¬ (v′ ↦ w′ ∈ u′))
                    × dom u′ {fu′} ⊑ v × w ⊑ cod u′ {fu′})

⊑-fun-inv : ∀{u₁ u₂ v w}
      → ¬ AllBot w
      → u₁ ⊑ u₂
      → v ↦ w ∈ u₁
      → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
⊑-fun-inv {u₁₁ ↦ u₂₂} {u₂} w≢⊥ (⊑-↦⊥ xx) refl = ⊥-elim (w≢⊥ xx)
⊑-fun-inv {.⊥} {u₂} {v} {w} w≢⊥ ⊑-⊥ () 
⊑-fun-inv {.(const _)} {.(const _)} {v} {w} w≢⊥ ⊑-const () 
⊑-fun-inv {u11 ⊔ u12} {u₂} {v} {w} w≢⊥ (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₁ x) =
    ⊑-fun-inv w≢⊥ u₁⊑u₂ x 
⊑-fun-inv {u11 ⊔ u12} {u₂} {v} {w} w≢⊥ (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₂ y) =
    ⊑-fun-inv w≢⊥ u₁⊑u₃ y 
⊑-fun-inv {u₁} {u21 ⊔ u22} {v} {w} w≢⊥ (⊑-conj-R1 u₁⊑u₂) v↦w∈u₁ 
    with ⊑-fun-inv {u₁} {u21} {v} {w} w≢⊥ u₁⊑u₂ v↦w∈u₁
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u3⊆u₁ , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
    ⟨ u₃ , ⟨ afu₃ , ⟨ (λ {x} x₁ → inj₁ (u3⊆u₁ x₁)) , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩  
⊑-fun-inv {u₁} {u21 ⊔ u22} {v} {w} w≢⊥ (⊑-conj-R2 u₁⊑u₂) v↦w∈u₁ 
    with ⊑-fun-inv {u₁} {u22} {v} {w} w≢⊥ u₁⊑u₂ v↦w∈u₁
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u3⊆u₁ , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
    ⟨ u₃ , ⟨ afu₃ , ⟨ (λ {x} x₁ → inj₂ (u3⊆u₁ x₁)) , ⟨ du₃⊑v , w⊑codu₃ ⟩ ⟩ ⟩ ⟩  
⊑-fun-inv {u11 ↦ u21} {u₂} {v} {w} w≢⊥
    (⊑-fun{u′ = u′} ≢⊥ u′⊆u₂ afu′ ∉⊥ du′⊑u11 u21⊑cu′) 
    refl =
      ⟨ u′ , ⟨ afu′ , ⟨ u′⊆u₂ , ⟨ ∉⊥ , ⟨ du′⊑u11 , u21⊑cu′ ⟩ ⟩ ⟩ ⟩ ⟩

sub-inv-trans : ∀{u′ u₂ u : Value}
  → (∀{v w} → AllBot w → ¬ (v ↦ w ∈ u′))
  → (fu′ : AllFun u′)  →  u′ ⊆ u
  → (∀{v′ w′} → ¬ AllBot w′ → v′ ↦ w′ ∈ u′ → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
    -------------------------------------------------------------------------
  → Σ[ u₃ ∈ Value ] factor u₂ u₃ (dom u′ {fu′}) (cod u′ {fu′})
sub-inv-trans {⊥} {u₂} {u} ⊥∉  () u′⊆u IH
sub-inv-trans {const k} {u₂} {u} ⊥∉  () u′⊆u IH
sub-inv-trans {u₁′ ↦ u₂′} {u₂} {u} ⊥∉ fu′ u′⊆u IH =
    IH (λ z → ⊥∉ z refl) refl
sub-inv-trans {u₁′ ⊔ u₂′} {u₂} {u} ⊥∉ ⟨ afu₁′ , afu₂′ ⟩ u′⊆u IH
    with sub-inv-trans {u₁′} {u₂} {u} (λ {v} {w} z z₁ → ⊥∉ z (inj₁ z₁)) afu₁′
               (λ {u₁} z → u′⊆u (inj₁ z)) (λ {v′} {w′} ≢⊥ z → IH ≢⊥ (inj₁ z))
    | sub-inv-trans {u₂′} {u₂} {u} (λ {v} {w} z z₁ → ⊥∉ z (inj₂ z₁)) afu₂′
               (λ {u₁} z → u′⊆u (inj₂ z)) (λ {v′} {w′} ≢⊥ z → IH ≢⊥ (inj₂ z))
... | ⟨ u₃ , ⟨ afu₃ , ⟨ u₃⊆ , ⟨ ∉⊥1 , ⟨ du₃⊑ , ⊑cu₃ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ u₄ , ⟨ afu₄ , ⟨ u₄⊆ , ⟨ ∉⊥2 , ⟨ du₄⊑ , ⊑cu₄ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ (u₃ ⊔ u₄) , ⟨ ⟨ afu₃ , afu₄ ⟩ , ⟨ G , ⟨ J , ⟨ H , I ⟩ ⟩ ⟩ ⟩ ⟩
    where
    G : ∀ {u₁} → u₁ ∈ u₃ ⊎ u₁ ∈ u₄ → u₁ ∈ u₂
    G {u₁} (inj₁ x) = u₃⊆ x
    G {u₁} (inj₂ y) = u₄⊆ y

    H : dom u₃ ⊔ dom u₄ ⊑ dom u₁′ ⊔ dom u₂′
    H = ⊑-conj-L (⊑-conj-R1 du₃⊑) (⊑-conj-R2 du₄⊑)

    I : cod u₁′ ⊔ cod u₂′ ⊑ cod u₃ ⊔ cod u₄
    I = ⊑-conj-L (⊑-conj-R1 ⊑cu₃) (⊑-conj-R2 ⊑cu₄)

    J : {v′ w′ : Value} → AllBot w′ → v′ ↦ w′ ∈ u₃ ⊎ v′ ↦ w′ ∈ u₄ → Bot
    J {v′} {w′} bw′ (inj₁ x) = ∉⊥1 bw′ x
    J {v′} {w′} bw′ (inj₂ y) = ∉⊥2 bw′ y


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
  helper d s IH {u₁ ↦ u₂} {v} {w} d≡ s≡ (⊑-↦⊥ bu₂) v⊑w = (⊑-↦⊥ bu₂)
  
  helper d s IH {u₁ ↦ u₂} {v} {w} d≡ s≡
      (⊑-fun{u′ = v′} ≢⊥ v′⊆v afv′ ∉⊥ dv′⊑u₁ u₂⊑cv′) v⊑w
      rewrite d≡ | s≡
      with sub-inv-trans ∉⊥ afv′ v′⊆v
                (λ {v₁}{v₂} ≢⊥ v₁↦v₂∈v′ →
                   ⊑-fun-inv {v′} {w} ≢⊥ (u⊆v⊑w→u⊑w v′⊆v v⊑w) v₁↦v₂∈v′) 
  ... | ⟨ w′ , ⟨ afw′ , ⟨ w′⊆w , ⟨ ∉⊥1 , ⟨ dw′⊑dv′ , cv′⊑cw′ ⟩ ⟩ ⟩ ⟩ ⟩ =
        let dw′⊑u₁ = IH M1 {dom w′}{dom v′}{u₁} refl refl dw′⊑dv′ dv′⊑u₁ in
        let u₂⊑cw′ = IH M2 {u₂}{cod v′}{cod w′} refl refl u₂⊑cv′ cv′⊑cw′ in
        ⊑-fun{u′ = w′} ≢⊥ w′⊆w afw′ ∉⊥1 dw′⊑u₁ u₂⊑cw′
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

AllBot-∈ : ∀{w u}
         → AllBot u
         → w ∈ u
         → AllBot w
AllBot-∈ {w} {⊥} bu refl = tt
AllBot-∈ {w} {const x} bu refl = bu
AllBot-∈ {w} {u ↦ u₁} bu refl = bu
AllBot-∈ {w} {u ⊔ u₁} ⟨ fst₁ , snd₁ ⟩ (inj₁ x) = AllBot-∈ fst₁ x
AllBot-∈ {w} {u ⊔ u₁} ⟨ fst₁ , snd₁ ⟩ (inj₂ y) = AllBot-∈ snd₁ y

AllBot-⊆ : ∀{w u}
         → AllBot u
         → w ⊆ u
         → AllBot w
AllBot-⊆ {⊥} {u} bu w⊆u = AllBot-∈ bu (w⊆u refl)
AllBot-⊆ {const x} {u} bu w⊆u = AllBot-∈ bu (w⊆u refl)
AllBot-⊆ {w ↦ w₁} {u} bu w⊆u = AllBot-∈ bu (w⊆u refl)
AllBot-⊆ {w₁ ⊔ w₂} {u} bu w⊆u
    with ⊔⊆-inv w⊆u
... | ⟨ w₁⊆u , w₂⊆u ⟩ = ⟨ AllBot-⊆ bu w₁⊆u , AllBot-⊆ bu w₂⊆u ⟩


AllBot-cod : ∀{u}
           → AllBot u
           → (fu : AllFun u)
           → AllBot (cod u {fu})
AllBot-cod {⊥} bu ()
AllBot-cod {const x} bu ()
AllBot-cod {u ↦ u₁} bu fu = bu
AllBot-cod {u₁ ⊔ u₂} ⟨ fst₁ , snd₁ ⟩ ⟨ fst₂ , snd₂ ⟩ =
    ⟨ AllBot-cod fst₁ fst₂ , AllBot-cod snd₁ snd₂ ⟩


AllBot-⊑ : ∀{w u}
         → AllBot u
         → w ⊑ u
         → AllBot w
AllBot-⊑ bu ⊑-⊥ = tt
AllBot-⊑ bu ⊑-const = bu
AllBot-⊑ bu (⊑-conj-L w⊑u w⊑u₁) = ⟨ AllBot-⊑ bu w⊑u , AllBot-⊑ bu w⊑u₁ ⟩
AllBot-⊑ bu (⊑-conj-R1 w⊑u) = AllBot-⊑ (proj₁ bu) w⊑u
AllBot-⊑ bu (⊑-conj-R2 w⊑u) = AllBot-⊑ (proj₂ bu) w⊑u
AllBot-⊑ bu (⊑-↦⊥ x) = x
AllBot-⊑ bu (⊑-fun{u′ = u′} bw u′⊆u fu′ ∉⊥ w⊑u w⊑u₁) =
  let bu′ = AllBot-⊆ bu u′⊆u in
  let bcu′ = AllBot-cod{u′} bu′ fu′ in
  AllBot-⊑ bcu′ w⊑u₁


⊑-fun′ : ∀{v w v′ w′}
       → v′ ⊑ v
       → w ⊑ w′
         -------------------
       → (v ↦ w) ⊑ (v′ ↦ w′)
⊑-fun′ {v}{w}{v′}{w′} v′⊑v w⊑w′
    with AllBot? w
... | yes ab = ⊑-↦⊥ ab
... | no nab
    with AllBot? w′
... | yes ab′ =  ⊥-elim (nab (AllBot-⊑ ab′ w⊑w′))
... | no nab′ =    
      ⊑-fun {v′ ↦ w′}{v′ ↦ w′}{v}{w} nab (λ {u} z → z) tt G v′⊑v w⊑w′
    where
    G : ∀ {v′₁ : Value} {w′₁ : Value} →
              AllBot w′₁ → ¬ v′₁ ↦ w′₁ ≡ v′ ↦ w′
    G ab refl = nab′ ab

    
{-
  The traditional distributivity rule is admissible.
 -}


AllBot-⊑-any : ∀{u v} → AllBot u → u ⊑ v
AllBot-⊑-any {⊥} {v} bu = ⊑-⊥
AllBot-⊑-any {const x} {v} ()
AllBot-⊑-any {u ↦ u₁} {v} bu = ⊑-↦⊥ bu
AllBot-⊑-any {u ⊔ u₁} {v} bu =
    ⊑-conj-L (AllBot-⊑-any (proj₁ bu)) (AllBot-⊑-any (proj₂ bu))


⊑-dist : ∀{v w w′}
         ---------------------------------
       → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)
⊑-dist {v}{w}{w′}
    with AllBot? w | AllBot? w′
... | yes bw | yes bw′ = ⊑-↦⊥ ⟨ bw , bw′ ⟩
... | yes bw | no bw′ =
      ⊑-fun {(v ↦ w) ⊔ (v ↦ w′)} {(v ↦ w′)} {v} {w ⊔ w′}
        (λ z → bw′ (proj₂ z))
        (λ {u} → inj₂)
        tt
        G
        ⊑-refl
        (⊑-conj-L (AllBot-⊑-any bw) ⊑-refl)
    where G : {v′ : Value} {w′₁ : Value} →
              AllBot w′₁ → ¬ v′ ↦ w′₁ ≡ v ↦ w′
          G bw1 refl = bw′ bw1

⊑-dist {v}{w}{w′} | no bw | yes bw′ =
    ⊑-fun {(v ↦ w) ⊔ (v ↦ w′)} {(v ↦ w)} {v} {w ⊔ w′}
          (λ z → bw (proj₁ z))
          (λ {u} → inj₁)
          tt
          G
          ⊑-refl
          (⊑-conj-L ⊑-refl (AllBot-⊑-any bw′))
    where G : {v′ : Value} {w′₁ : Value} →
              AllBot w′₁ → ¬ v′ ↦ w′₁ ≡ v ↦ w
          G bw1 refl = bw bw1

⊑-dist {v}{w}{w′} | no bw | no bw′ = 
  ⊑-fun {(v ↦ w) ⊔ (v ↦ w′)} {(v ↦ w) ⊔ (v ↦ w′)} {v} {w ⊔ w′}
        (λ z → bw′ (proj₂ z))
        (λ {u} z → z) ⟨ tt , tt ⟩
        G
        (⊑-conj-L ⊑-refl ⊑-refl)
        ((⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)))
  where G : {v′ : Value} {w′₁ : Value} →
          AllBot w′₁ → ¬ (v′ ↦ w′₁ ≡ v ↦ w ⊎ v′ ↦ w′₁ ≡ v ↦ w′)
        G bw1 (inj₁ refl) = bw bw1
        G bw1 (inj₂ refl) = bw′ bw1

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
⊆↦→cod⊆ {const k} {fu = ()}
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
⊆→⊑ {const k} s with s {const k} refl
... | x = ∈→⊑ x
⊆→⊑ {u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u ⊔ u′} s = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))

↦∈→⊆dom : ∀{u v w : Value} {fu : AllFun u}
      → (v ↦ w) ∈ u
        ----------------------------
      → v ⊆ dom u {fu}
↦∈→⊆dom {⊥} {fu = ()} eq 
↦∈→⊆dom {const k} {fu = ()} eq
↦∈→⊆dom {u₁ ↦ u₂}{v}{w} refl {v′} v′∈u₁ = v′∈u₁
↦∈→⊆dom {u₁ ⊔ u₂} {v} {w} {⟨ f1 , f2 ⟩} (inj₁ v↦w∈u₁) {v'} v'∈v =
    inj₁ (↦∈→⊆dom {u₁}{v}{fu = f1} v↦w∈u₁ v'∈v)
↦∈→⊆dom {u₁ ⊔ u₂} {v} {w} {⟨ f1 , f2 ⟩} (inj₂ v↦w∈u₂) {v'} v'∈v =
    inj₂ (↦∈→⊆dom {u₂}{v}{fu = f2} v↦w∈u₂ v'∈v)

⊑-fun-inv′ : ∀{v w v′ w′}
        → v ↦ w ⊑ v′ ↦ w′  →  ¬ AllBot w
          ---------------
        → v′ ⊑ v × w ⊑ w′
⊑-fun-inv′ {v}{w}{v′}{w′} lt bw 
    with ⊑-fun-inv bw lt refl
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ ∉⊥ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ ⟩
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

<:→⊑ : ∀{u v} → u <: v → u ⊑ v
<:→⊑ {u} {.u} <:-refl = ⊑-refl
<:→⊑ {u} {.(u ⊔ _)} <:-incl-L = ⊑-conj-R1 ⊑-refl
<:→⊑ {u} {.(_ ⊔ u)} <:-incl-R = ⊑-conj-R2 ⊑-refl
<:→⊑ {.(_ ⊔ _)} {v} (<:-glb u<:v u<:v₁) = ⊑-conj-L (<:→⊑ u<:v) (<:→⊑ u<:v₁)
<:→⊑ {u} {v} (<:-trans u<:v u<:v₁) = ⊑-trans (<:→⊑ u<:v) (<:→⊑ u<:v₁)
<:→⊑ {.⊥} {v} <:-U-top = ⊑-⊥
<:→⊑ {.(_ ↦ ⊥)} {.⊥} <:-U→ = ⊑-↦⊥ tt
<:→⊑ {.(_ ↦ (_ ⊔ _))} {.(_ ↦ _ ⊔ _ ↦ _)} <:-→⊔ = ⊑-dist
<:→⊑ {.(_ ↦ _)} {.(_ ↦ _)} (<:-→ u<:v u<:v₁) = ⊑-fun′ (<:→⊑ u<:v) (<:→⊑ u<:v₁)

AllBot<:⊥ : ∀{u} → AllBot u → u <: ⊥
AllBot<:⊥ {⊥} bu = <:-refl
AllBot<:⊥ {const x} ()
AllBot<:⊥ {u ↦ u₁} bu = <:-trans (<:-→ <:-refl (AllBot<:⊥ bu)) <:-U→
AllBot<:⊥ {u ⊔ u₁} bu = <:-glb (AllBot<:⊥ (proj₁ bu)) (AllBot<:⊥ (proj₂ bu))

⊑→<: : ∀{u v} → u ⊑ v → u <: v
⊑→<: {.⊥} {v} ⊑-⊥ = <:-U-top
⊑→<: {.(const _)} {.(const _)} ⊑-const = <:-refl
⊑→<: {.(_ ⊔ _)} {v} (⊑-conj-L u⊑v u⊑v₁) = <:-glb (⊑→<: u⊑v) (⊑→<: u⊑v₁)
⊑→<: {u} {.(_ ⊔ _)} (⊑-conj-R1 u⊑v) = <:-trans (⊑→<: u⊑v) <:-incl-L
⊑→<: {u} {.(_ ⊔ _)} (⊑-conj-R2 u⊑v) = <:-trans (⊑→<: u⊑v) <:-incl-R
⊑→<: {u₁ ↦ u₂} {v} (⊑-↦⊥ bu₂) = <:-trans G H
      where
      G : u₁ ↦ u₂ <: u₁ ↦ ⊥
      G = <:-→ <:-refl (AllBot<:⊥ bu₂)
      H : u₁ ↦ ⊥ <: v
      H = <:-trans <:-U→ <:-U-top
⊑→<: {u₁ ↦ u₂} {v} (⊑-fun x x₁ fu′ x₂ u⊑v u⊑v₁) = {!!}
