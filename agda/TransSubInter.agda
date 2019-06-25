open import Primitives
open import Structures

open import Data.Nat using (ℕ; suc ; zero) renaming (_≟_ to _=ℕ_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Maybe
open import Data.List using (List ; _∷_ ; []; _++_) 
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)

module TransSubInter where


infixr 7 _↦_
infixl 6 _∩_

data Typ : Set where
  U : Typ
  const : ℕ → Typ
  _↦_ : Typ → Typ → Typ
  _∩_ : (A : Typ) → (B : Typ) → Typ

_≟_ : ∀ (x y : Typ) → Dec (x ≡ y)
U ≟ U = yes refl
U ≟ const x = no λ ()
U ≟ (B ↦ B₁) = no (λ ())
U ≟ (B ∩ B₁) = no (λ ())
const x ≟ U = no (λ ())
const x ≟ const y
    with x =ℕ y
... | yes refl = yes refl
... | no neq = no G
   where G : ¬ const x ≡ const y
         G refl = neq refl
const x ≟ (B ↦ B₁) = no (λ ())
const x ≟ (B ∩ B₁) = no (λ ())
(A ↦ A₁) ≟ U = no (λ ())
(A ↦ A₁) ≟ const x = no (λ ())
(A ↦ A₁) ≟ (B ↦ B₁)
    with A ≟ B | A₁ ≟ B₁
... | yes refl | yes refl = yes refl
... | yes e1 | no e2 = no G
    where G : ¬ A ↦ A₁ ≡ B ↦ B₁
          G refl = e2 refl
(A ↦ A₁) ≟ (B ↦ B₁) | no e1 | _ = no G
    where G : ¬ A ↦ A₁ ≡ B ↦ B₁
          G refl = e1 refl
(A ↦ A₁) ≟ (B ∩ B₁) = no (λ ())
(A ∩ A₁) ≟ U = no (λ ())
(A ∩ A₁) ≟ const x = no (λ ())
(A ∩ A₁) ≟ (B ↦ B₁) = no (λ ())
(A ∩ A₁) ≟ (B ∩ B₁)
    with A ≟ B | A₁ ≟ B₁
... | yes refl | yes refl = yes refl
... | yes e1 | no e2 = no G
    where G : ¬ A ∩ A₁ ≡ B ∩ B₁
          G refl = e2 refl
(A ∩ A₁) ≟ (B ∩ B₁) | no e1 | _ = no G
    where G : ¬ A ∩ A₁ ≡ B ∩ B₁
          G refl = e1 refl

infix 5 _∈_

_∈_ : Typ → Typ → Set
A ∈ U = A ≡ U
A ∈ const k = A ≡ const k
A ∈ B ↦ C = A ≡ B ↦ C
A ∈ (B ∩ C) = A ∈ B ⊎ A ∈ C

infix 5 _⊆_

_⊆_ : Typ → Typ → Set
B ⊆ C = ∀{A} → A ∈ B → A ∈ C

AllBot : (A : Typ) → Set
AllBot U = True
AllBot (const x) = False
AllBot (B ↦ C) = AllBot C
AllBot (A ∩ B) = AllBot A × AllBot B 

AllBot? : (A : Typ) → Dec (AllBot A)
AllBot? U = yes tt
AllBot? (const k) = no (λ z → z)
AllBot? (A₁ ↦ A₂) = AllBot? A₂
AllBot? (A₁ ∩ A₂)
    with AllBot? A₁ | AllBot? A₂
... | yes x | yes y = yes ⟨ x , y ⟩    
... | yes x | no y = no λ z → y (proj₂ z)    
... | no x | _ = no λ z → x (proj₁ z)     

AllFun : (A : Typ) → Set
AllFun U = False
AllFun (const x) = False
AllFun (B ↦ C) = True
AllFun (A ∩ B) = AllFun A × AllFun B 

dom : (A : Typ) → ∀{a : AllFun A } → Typ
dom U {()}
dom (const k) {()}
dom (B ↦ C) = B
dom (A ∩ B) { ⟨ fA , fB ⟩ } = dom A {fA} ∩ dom B {fB}

cod : (A : Typ) → ∀{a : AllFun A} → Typ
cod U {()}
cod (const k) {()}
cod (B ↦ C) = C
cod (A ∩ B) { ⟨ fA , fB ⟩ } = cod A {fA} ∩ cod B {fB}


module BCDSubtyping where

  infix 4 _≤_

  data _≤_ : Typ → Typ → Set where

    ≤-refl : ∀{B} → B ≤ B

    ≤-incl-L : ∀{A B}
           → A ∩ B ≤ A

    ≤-incl-R : ∀{A B}
           → A ∩ B ≤ B

    ≤-glb : ∀{A B C}
        → A ≤ B
        → A ≤ C
          -----------
        → A ≤ B ∩ C

    ≤-trans : ∀{A B C} → A ≤ B → B ≤ C → A ≤ C

    ≤-U-top : ∀{B} → B ≤ U

    ≤-U→ : ∀{B} → U ≤ B ↦ U

    ≤-→∩ : ∀{B C C′}
         → (B ↦ C) ∩ (B ↦ C′) ≤ B ↦ (C ∩ C′)

    ≤-→ : ∀{B C B′ C′}
         → B ≤ B′
         → C′ ≤ C
           -------------------
         → (B′ ↦ C′) ≤ (B ↦ C)

module NewSubtyping where

  open import Data.Nat using (_+_; _≤′_; _<′_; _<_; _≤_;
      z≤n; s≤s; ≤′-refl; ≤′-step) renaming (_⊔_ to max)
  open import Data.Nat.Properties
    using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; ≤-step; ⊔-mono-≤;
           +-mono-≤; +-mono-≤-<; +-mono-<-≤; +-comm; +-assoc; n≤1+n; 
           ≤-pred; m≤m+n; n≤m+n; ≤-reflexive; ≤′⇒≤; ≤⇒≤′; +-suc)
  open Data.Nat.Properties.≤-Reasoning using (begin_; _≤⟨_⟩_; _∎)

  infix 4 _<:_

  data _<:_ : Typ → Typ → Set where

    <:-U : ∀ {B} → B <: U

    <:-const : ∀ {k} → const k <: const k

    <:-conj-L : ∀ {A B C}
          → A <: B
          → A <: C
            -----------
          → A <: B ∩ C

    <:-conj-R1 : ∀ {A B C}
         → B <: A
           ------------------
         → B ∩ C <: A

    <:-conj-R2 : ∀ {A B C}
         → C <: A
           -----------
         → B ∩ C <: A

    <:-↦U : ∀{A B C}
         → AllBot C
           ---------
         → A <: B ↦ C

    <:-fun : ∀ {A A′ B C}
         → ¬ (AllBot C)
         → A′ ⊆ A
         → (fA′ : AllFun A′)
         → (∀{B′ C′} → AllBot C′ → ¬ (B′ ↦ C′ ∈ A′))
         → B <: dom A′ {fA′}
         → cod A′ {fA′} <: C
           -------------------
         → A <: B ↦ C

  <:-refl : ∀{B} → B <: B
  <:-refl {U} = <:-U
  <:-refl {const k} = <:-const
  <:-refl {B ↦ C}
      with AllBot? C
  ... | yes bC = <:-↦U bC
  ... | no C≠U = <:-fun {B ↦ C}{B ↦ C} C≠U (λ {u} z → z) tt G
                        (<:-refl {B}) (<:-refl {C})
      where G : {B′ C′ : Typ} → AllBot C′ → ¬ B′ ↦ C′ ≡ B ↦ C
            G {B′} {U} bC refl = C≠U tt
            G {B′} {const x} bC refl = bC
            G {B′} {C′ ↦ C′₁} bC refl = C≠U bC
            G {B′} {C′ ∩ C′₁} bC refl = C≠U bC

  <:-refl {B₁ ∩ B₂} = <:-conj-L (<:-conj-R1 <:-refl) (<:-conj-R2 <:-refl)

  ∩<:R : ∀{B C A}
      → A <: B ∩ C
      → A <: B
  ∩<:R (<:-conj-L A<:B∩C _) = A<:B∩C
  ∩<:R (<:-conj-R1 A<:B∩C) = <:-conj-R1 (∩<:R A<:B∩C)
  ∩<:R (<:-conj-R2 A<:B∩C) = <:-conj-R2 (∩<:R A<:B∩C)

  ∩<:L : ∀{B C A}
      → A <: B ∩ C
      → A <: C
  ∩<:L (<:-conj-L _ A<:B∩C) = A<:B∩C
  ∩<:L (<:-conj-R1 A<:B∩C) = <:-conj-R1 (∩<:L A<:B∩C)
  ∩<:L (<:-conj-R2 A<:B∩C) = <:-conj-R2 (∩<:L A<:B∩C)

  ∩<:-inv : ∀{B C A}
      → A <: B ∩ C
      → A <: B × A <: C
  ∩<:-inv A<:B∩C  = ⟨ ∩<:R A<:B∩C , ∩<:L A<:B∩C ⟩

  ∩⊆-inv : ∀{A B w : Typ}
         → (A ∩ B) ⊆ w
           ---------------
         → A ⊆ w  ×  B ⊆ w
  ∩⊆-inv ABw = ⟨ (λ x → ABw (inj₁ x)) , (λ x → ABw (inj₂ x)) ⟩

  factor : (A : Typ) → (A′ : Typ) → (B : Typ) → (C : Typ) → Set
  factor A A′ B C = (Σ[ fA′ ∈ AllFun A′ ] A′ ⊆ A
                      × (∀{B′ C′} → AllBot C′ → ¬ (B′ ↦ C′ ∈ A′))
                      × B <: dom A′ {fA′} × cod A′ {fA′} <: C)

  <:-fun-inv : ∀{A₁ A₂ B C}
        → ¬ AllBot C
        → A₂ <: A₁
        → B ↦ C ∈ A₁
        → Σ[ A₃ ∈ Typ ] factor A₂ A₃ B C
  <:-fun-inv {A₁₁ ↦ A₂₂} {A₂} C≢U (<:-↦U xx) refl = ⊥-elim (C≢U xx)
  <:-fun-inv {.U} {A₂} {B} {C} C≢U <:-U () 
  <:-fun-inv {.(const _)} {.(const _)} {B} {C} C≢U <:-const () 
  <:-fun-inv {A11 ∩ A12} {A₂} {B} {C} C≢U (<:-conj-L A₁<:A₂ A₁<:A₃) (inj₁ x) =
      <:-fun-inv C≢U A₁<:A₂ x 
  <:-fun-inv {A11 ∩ A12} {A₂} {B} {C} C≢U (<:-conj-L A₁<:A₂ A₁<:A₃) (inj₂ y) =
      <:-fun-inv C≢U A₁<:A₃ y 
  <:-fun-inv {A₁} {A21 ∩ A22} {B} {C} C≢U (<:-conj-R1 A₁<:A₂) B↦C∈A₁ 
      with <:-fun-inv {A₁} {A21} {B} {C} C≢U A₁<:A₂ B↦C∈A₁
  ... | ⟨ A₃ , ⟨ afA₃ , ⟨ A3⊆A₁ , ⟨ dA₃<:B , C<:codA₃ ⟩ ⟩ ⟩ ⟩ =
    ⟨ A₃ , ⟨ afA₃ , ⟨ (λ {x} x₁ → inj₁ (A3⊆A₁ x₁)) , ⟨ dA₃<:B , C<:codA₃ ⟩ ⟩ ⟩ ⟩
  <:-fun-inv {A₁} {A21 ∩ A22} {B} {C} C≢U (<:-conj-R2 A₁<:A₂) B↦C∈A₁ 
      with <:-fun-inv {A₁} {A22} {B} {C} C≢U A₁<:A₂ B↦C∈A₁
  ... | ⟨ A₃ , ⟨ afA₃ , ⟨ A3⊆A₁ , ⟨ dA₃<:B , C<:codA₃ ⟩ ⟩ ⟩ ⟩ =
    ⟨ A₃ , ⟨ afA₃ , ⟨ (λ {x} x₁ → inj₂ (A3⊆A₁ x₁)) , ⟨ dA₃<:B , C<:codA₃ ⟩ ⟩ ⟩ ⟩
  <:-fun-inv {A11 ↦ A21} {A₂} {B} {C} C≢U
      (<:-fun{A′ = A′} ≢U A′⊆A₂ afA′ ∉U dA′<:A11 A21<:cA′) 
      refl =
        ⟨ A′ , ⟨ afA′ , ⟨ A′⊆A₂ , ⟨ ∉U , ⟨ dA′<:A11 , A21<:cA′ ⟩ ⟩ ⟩ ⟩ ⟩


  sub-inv-trans : ∀{A′ A₂ : Typ}
    → (∀{B C} → AllBot C → ¬ (B ↦ C ∈ A′))
    → (fA′ : AllFun A′)
    → (∀{B′ C′} → ¬ AllBot C′ → B′ ↦ C′ ∈ A′ → Σ[ A₃ ∈ Typ ] factor A₂ A₃ B′ C′)
      -------------------------------------------------------------------------
    → Σ[ A₃ ∈ Typ ] factor A₂ A₃ (dom A′ {fA′}) (cod A′ {fA′})
  sub-inv-trans {U} {A₂} U∉  () IH
  sub-inv-trans {const k} {A₂} U∉  () IH
  sub-inv-trans {A₁′ ↦ A₂′} {A₂} U∉ fA′ IH =
      IH (λ z → U∉ z refl) refl
  sub-inv-trans {A₁′ ∩ A₂′} {A₂} U∉ ⟨ afA₁′ , afA₂′ ⟩ IH
      with sub-inv-trans {A₁′} {A₂} (λ {v} {C} z z₁ → U∉ z (inj₁ z₁)) afA₁′
                 (λ {v′} {C′} ≢U z → IH ≢U (inj₁ z))
      | sub-inv-trans {A₂′} {A₂} (λ {v} {C} z z₁ → U∉ z (inj₂ z₁)) afA₂′
                 (λ {v′} {C′} ≢U z → IH ≢U (inj₂ z))
  ... | ⟨ A₃ , ⟨ afA₃ , ⟨ A₃⊆ , ⟨ ∉U1 , ⟨ dA₃<:dA₁′ , cA₁′<:cA₃ ⟩ ⟩ ⟩ ⟩ ⟩
      | ⟨ A₄ , ⟨ afA₄ , ⟨ A₄⊆ , ⟨ ∉U2 , ⟨ dA₄<:dA₂′ , cA₂′<:cA₄ ⟩ ⟩ ⟩ ⟩ ⟩ =
        ⟨ (A₃ ∩ A₄) , ⟨ ⟨ afA₃ , afA₄ ⟩ , ⟨ G , ⟨ J , ⟨ H , I ⟩ ⟩ ⟩ ⟩ ⟩
      where
      G : ∀ {A₁} → A₁ ∈ A₃ ⊎ A₁ ∈ A₄ → A₁ ∈ A₂
      G {A₁} (inj₁ x) = A₃⊆ x
      G {A₁} (inj₂ y) = A₄⊆ y

      H : dom A₁′ ∩ dom A₂′ <: dom A₃ ∩ dom A₄
      H = <:-conj-L (<:-conj-R1 dA₃<:dA₁′) (<:-conj-R2 dA₄<:dA₂′)

      I : cod A₃ ∩ cod A₄ <: cod A₁′ ∩ cod A₂′
      I = <:-conj-L (<:-conj-R1 cA₁′<:cA₃) (<:-conj-R2 cA₂′<:cA₄)

      J : {v′ C′ : Typ} → AllBot C′ → v′ ↦ C′ ∈ A₃ ⊎ v′ ↦ C′ ∈ A₄ → False
      J {v′} {C′} bC′ (inj₁ x) = ∉U1 bC′ x
      J {v′} {C′} bC′ (inj₂ y) = ∉U2 bC′ y


  A∈B<:C→A<:C : ∀{B A C} → C ∈ B → A <: B → A <: C
  A∈B<:C→A<:C {U} C∈B A<:B  rewrite C∈B = A<:B
  A∈B<:C→A<:C {const k} C∈B A<:B rewrite C∈B = A<:B
  A∈B<:C→A<:C {B₁ ↦ B₂} C∈B A<:B rewrite C∈B = A<:B
  A∈B<:C→A<:C {B₁ ∩ B₂}{A}{C} (inj₁ C∈B₁) A<:B =
      A∈B<:C→A<:C {B₁}{A}{C} C∈B₁ (∩<:R A<:B)
  A∈B<:C→A<:C {B₁ ∩ B₂}{A}{C} (inj₂ C∈B₂) A<:B =
      A∈B<:C→A<:C {B₂}{A}{C} C∈B₂ (∩<:L A<:B)

  A⊆B<:C→A<:C : ∀{A B C} → A ⊆ B → C <: B → C <: A
  A⊆B<:C→A<:C {U} {B} {C} A⊆B C<:B = <:-U
  A⊆B<:C→A<:C {const k} {B} {C} A⊆B C<:B = A∈B<:C→A<:C (A⊆B refl) C<:B
  A⊆B<:C→A<:C {A₁ ↦ A₂} {B} {C} A⊆B C<:B = A∈B<:C→A<:C (A⊆B refl) C<:B
  A⊆B<:C→A<:C {A₁ ∩ A₂} {B} {C} A⊆B C<:B =
      <:-conj-L (A⊆B<:C→A<:C A₁⊆B C<:B) (A⊆B<:C→A<:C A₂⊆B C<:B)
      where
      A₁⊆B : A₁ ⊆ B
      A₁⊆B {A′} A′∈A₁ = A⊆B (inj₁ A′∈A₁)
      A₂⊆B : A₂ ⊆ B
      A₂⊆B {A′} A′∈A₂ = A⊆B (inj₂ A′∈A₂)

  depth : (B : Typ) → ℕ
  depth U = zero
  depth (const k) = zero
  depth (B ↦ C) = suc (max (depth B) (depth C))
  depth (B₁ ∩ B₂) = max (depth B₁) (depth B₂)

  size : (B : Typ) → ℕ
  size U = zero
  size (const k) = zero
  size (B ↦ C) = suc (size B + size C)
  size (B₁ ∩ B₂) = suc (size B₁ + size B₂)

  ∈→depth≤ : ∀{B A : Typ} → A ∈ B → depth A ≤ depth B
  ∈→depth≤ {U} {A} A∈B rewrite A∈B = _≤_.z≤n
  ∈→depth≤ {const x} {A} A∈B rewrite A∈B = _≤_.z≤n
  ∈→depth≤ {B ↦ C} {A} A∈B rewrite A∈B = ≤-refl
  ∈→depth≤ {B₁ ∩ B₂} {A} (inj₁ x) =
      ≤-trans (∈→depth≤ {B₁} {A} x) (m≤m⊔n (depth B₁) (depth B₂))
  ∈→depth≤ {B₁ ∩ B₂} {A} (inj₂ y) =
      ≤-trans (∈→depth≤ {B₂} {A} y) (n≤m⊔n (depth B₁) (depth B₂))

  max-lub : ∀{x y z : ℕ} → x ≤ z → y ≤ z → max x y ≤ z
  max-lub {.0} {y} {z} _≤_.z≤n y≤z = y≤z
  max-lub {suc x} {.0} {suc z} (_≤_.s≤s x≤z) _≤_.z≤n = _≤_.s≤s x≤z
  max-lub {suc x} {suc y} {suc z} (_≤_.s≤s x≤z) (_≤_.s≤s y≤z) =
    let max-xy≤z = max-lub {x}{y}{z} x≤z y≤z in
    _≤_.s≤s max-xy≤z

  ⊆→depth≤ : ∀{A B : Typ} → A ⊆ B → depth A ≤ depth B
  ⊆→depth≤ {U} {B} A⊆B = _≤_.z≤n
  ⊆→depth≤ {const x} {B} A⊆B = _≤_.z≤n
  ⊆→depth≤ {A₁ ↦ A₂} {B} A⊆B = ∈→depth≤ (A⊆B refl)
  ⊆→depth≤ {A₁ ∩ A₂} {B} A⊆B
      with ∩⊆-inv A⊆B
  ... | ⟨ A₁⊆B , A₂⊆B ⟩ =
      let A₁≤B = ⊆→depth≤ A₁⊆B in
      let A₂≤B = ⊆→depth≤ A₂⊆B in
      max-lub A₁≤B A₂≤B

  dom-depth-≤ : ∀{A : Typ}{fA : AllFun A} → depth (dom A {fA}) ≤ depth A
  dom-depth-≤ {U}{()}
  dom-depth-≤ {const k}{()}
  dom-depth-≤ {B ↦ C} = ≤-step (m≤m⊔n (depth B) (depth C))
  dom-depth-≤ {A ∩ B} =
    let ih1 = dom-depth-≤ {A} in
    let ih2 = dom-depth-≤ {B} in
    ⊔-mono-≤ ih1 ih2

  cod-depth-≤ : ∀{A : Typ}{fA : AllFun A} → depth (cod A {fA}) ≤ depth A
  cod-depth-≤ {U}{()}
  cod-depth-≤ {const k}{()}
  cod-depth-≤ {B ↦ C} = ≤-step (n≤m⊔n (depth B) (depth C))
  cod-depth-≤ {A ∩ B} {⟨ fA , fB ⟩} =
    let ih1 = cod-depth-≤ {A}{fA} in
    let ih2 = cod-depth-≤ {B}{fB} in
    ⊔-mono-≤ ih1 ih2

  ≤′-trans : ∀{x y z} → x ≤′ y → y ≤′ z → x ≤′ z
  ≤′-trans x≤′y y≤′z = ≤⇒≤′ (≤-trans (≤′⇒≤ x≤′y) (≤′⇒≤ y≤′z))

  data _<<_ : ℕ × ℕ → ℕ × ℕ → Set where
    fst : ∀{x x' y y'} → x <′ x' → ⟨ x , y ⟩ << ⟨ x' , y' ⟩
    snd : ∀{x x' y y'} → x ≤′ x' → y <′ y' → ⟨ x , y ⟩ << ⟨ x' , y' ⟩

  {- 

    The folloCing is based on code from Pierre-EBariste Dagand.
    https://pages.lip6.fr/Pierre-EBariste.Dagand/stAffs/notes/html/BoBe.html
   -}
  <<-Wellfounded : (P : ℕ → ℕ → Set) →
           (∀ x y → (∀ {x' y'} → ⟨ x' , y' ⟩ << ⟨ x , y ⟩ → P x' y') → P x y) →
           ∀ x y → P x y
  <<-Wellfounded P ih x y = ih x y (help x y)
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


  M1 : ∀{A₁ A₂ B C}
      → ⟨ depth A₁ + depth C , size A₁ + size B ⟩ <<
        ⟨ max (depth A₁) (depth A₂) + depth C ,
          suc (size A₁ + size A₂ + size B) ⟩
  M1 {A₁}{A₂}{B}{C} = snd (≤⇒≤′ M1a) (≤⇒≤′ M1b)
        where
        M1a = begin
                 depth A₁ + depth C
               ≤⟨ +-mono-≤ (m≤m⊔n (depth A₁) (depth A₂)) ≤-refl ⟩
                 max (depth A₁) (depth A₂) + depth C
              ∎
        M1b = begin
                 suc (size A₁ + size B)
              ≤⟨ s≤s (+-mono-≤ ≤-refl (n≤m+n (size A₂) (size B))) ⟩
                 suc (size A₁ + (size A₂ + size B))
              ≤⟨ s≤s (≤-reflexive (sym (+-assoc (size A₁) (size A₂) (size B)))) ⟩
                 suc (size A₁ + size A₂ + size B)
              ∎ 

  M2 : ∀{A₁ A₂ B C}
     → ⟨ depth A₂ + depth C , size A₂ + size B ⟩ <<
       ⟨ max (depth A₁) (depth A₂) + depth C ,
         suc (size A₁ + size A₂ + size B) ⟩
  M2 {A₁}{A₂}{B}{C} = snd (≤⇒≤′ M2a) (≤⇒≤′ M2b)
        where
        M2a = begin
                 depth A₂ + depth C
               ≤⟨ +-mono-≤ (n≤m⊔n (depth A₁) (depth A₂)) ≤-refl ⟩
                 max (depth A₁) (depth A₂) + depth C
              ∎
        M2b = begin
                 suc (size A₂ + size B)
              ≤⟨ s≤s (+-mono-≤ (n≤m+n (size A₁) (size A₂)) ≤-refl) ⟩
                 suc ((size A₁ + size A₂) + size B)
              ∎ 

  <:-trans-P : ℕ → ℕ → Set
  <:-trans-P d s = ∀{A B C} → d ≡ depth A + depth C → s ≡ size A + size B
                           → C <: B → B <: A → C <: A

  <:-trans-rec : ∀ d s → <:-trans-P d s
  <:-trans-rec = <<-Wellfounded <:-trans-P helper
    where
    helper : ∀ x y 
           → (∀ {x' y'} → ⟨ x' , y' ⟩ << ⟨ x , y ⟩ → <:-trans-P x' y')
           → <:-trans-P x y
    helper d s IH {.U} {B} {C} d≡ s≡ B<:C <:-U = <:-U
    helper d s IH {.(const _)} {.(const _)} {C} d≡ s≡ B<:C <:-const = B<:C
    helper d s IH {A₁ ∩ A₂} {B} {C} d≡ s≡ B<:C (<:-conj-L A₁<:B A₂<:B) 
        rewrite d≡ | s≡ =
        let A₁<:C = IH (M1{A₁}{C = C}) {A₁}{B}{C} refl refl B<:C A₁<:B  in
        let A₂<:C = IH (M2{A₁}{C = C}) {A₂}{B}{C} refl refl B<:C A₂<:B in
        <:-conj-L A₁<:C A₂<:C
        where
    helper d s IH {A} {B₁ ∩ B₂} {C} d≡ s≡ B₁∩B₂<:C  (<:-conj-R1 A<:B₁) 
        rewrite d≡ | s≡ =
        let B₁<:C = ∩<:R B₁∩B₂<:C in
        IH M3 {A}{B₁}{C} refl refl B₁<:C A<:B₁ 
        where
        M3a = begin
                suc (size A + size B₁)
             ≤⟨ ≤-reflexive (sym (+-suc (size A) (size B₁))) ⟩
                size A + suc (size B₁)
             ≤⟨ +-mono-≤ ≤-refl (s≤s (m≤m+n (size B₁) (size B₂))) ⟩
                size A + suc (size B₁ + size B₂)
             ∎ 
        M3 : ⟨ depth A + depth C , size A + size B₁ ⟩ <<
            ⟨ depth A + depth C , size A + suc (size B₁ + size B₂) ⟩
        M3 = snd (≤⇒≤′ ≤-refl) (≤⇒≤′ M3a)
    helper d s IH {A} {B₁ ∩ B₂} {C} d≡ s≡ B₁∩B₂<:C (<:-conj-R2 A<:B₂) 
        rewrite d≡ | s≡ =
        let B₂<:C = ∩<:L B₁∩B₂<:C in
        IH M4 {A}{B₂}{C} refl refl B₂<:C A<:B₂
        where
        M4a = begin
                suc (size A + size B₂)
             ≤⟨ ≤-reflexive (sym (+-suc (size A) (size B₂))) ⟩
                size A + suc (size B₂)
             ≤⟨ +-mono-≤ ≤-refl (s≤s (n≤m+n (size B₁) (size B₂))) ⟩
                size A + suc (size B₁ + size B₂)
             ∎ 
        M4 : ⟨ depth A + depth C , size A + size B₂ ⟩ <<
            ⟨ depth A + depth C , size A + suc (size B₁ + size B₂) ⟩
        M4 = snd (≤⇒≤′ ≤-refl) (≤⇒≤′ M4a)
    helper d s IH {A₁ ↦ A₂} {B} {C} d≡ s≡ B<:C (<:-↦U bA₂) = (<:-↦U bA₂)

    helper d s IH {A₁ ↦ A₂} {B} {C} d≡ s≡ B<:C
        (<:-fun{A′ = B′} ≢U B′⊆B afB′ ∉U dB′<:A₁ A₂<:cB′) 
        rewrite d≡ | s≡
        with sub-inv-trans ∉U afB′ 
                  (λ {B₁}{B₂} ≢U B₁↦B₂∈B′ →
                     <:-fun-inv {B′} {C} ≢U (A⊆B<:C→A<:C B′⊆B B<:C) B₁↦B₂∈B′) 
    ... | ⟨ C′ , ⟨ afC′ , ⟨ C′⊆C , ⟨ ∉U1 , ⟨ dC′<:dB′ , cB′<:cC′ ⟩ ⟩ ⟩ ⟩ ⟩ =
          let dC′<:A₁ = IH M5 {dom C′}{dom B′}{A₁} refl refl dB′<:A₁ dC′<:dB′ in
          let A₂<:cC′ = IH M6 {A₂}{cod B′}{cod C′} refl refl cB′<:cC′ A₂<:cB′ in
          <:-fun{A′ = C′} ≢U C′⊆C afC′ ∉U1 dC′<:A₁ A₂<:cC′
        where
        dC′≤C : depth (dom C′) ≤ depth C
        dC′≤C = ≤-trans (dom-depth-≤{C′}) (⊆→depth≤ C′⊆C)
        cC′≤C : depth (cod C′) ≤ depth C
        cC′≤C = ≤-trans (cod-depth-≤{C′}) (⊆→depth≤ C′⊆C)

        M5a = begin
                 suc (depth (dom C′) + depth A₁)
              ≤⟨ s≤s (≤-reflexive (+-comm (depth (dom C′)) (depth A₁))) ⟩
                 suc (depth A₁ + depth (dom C′))
              ≤⟨ s≤s (+-mono-≤ (m≤m⊔n (depth A₁) (depth A₂)) dC′≤C) ⟩
                 suc (max (depth A₁) (depth A₂) + depth C)
              ∎ 
        M5 : ⟨ depth (dom C′) + depth A₁ , size (dom C′) + size (dom B′) ⟩
          << ⟨ suc (max (depth A₁) (depth A₂) + depth C) ,
               suc (size A₁ + size A₂ + size B) ⟩
        M5 = fst (≤⇒≤′ M5a)
        M6a = begin
                 suc (depth A₂ + depth (cod C′))
              ≤⟨ s≤s (+-mono-≤ (n≤m⊔n (depth A₁) (depth A₂)) cC′≤C) ⟩
                 suc (max (depth A₁) (depth A₂) + depth C)
              ∎ 
        M6 : ⟨ depth A₂ + depth (cod C′) ,
               size A₂ + size (cod B′) ⟩
          << ⟨ suc (max (depth A₁) (depth A₂) + depth C) ,
               suc (size A₁ + size A₂ + size B) ⟩
        M6 = fst (≤⇒≤′ M6a)


  <:-trans : ∀{A B C} → A <: B → B <: C → A <: C
  <:-trans {A} {B} {C} A<:B B<:C =
      <:-trans-rec (depth C + depth A) (size C + size B) refl refl A<:B B<:C

  {-
    The traditional function subtyping rule is admissible.
   -}

  AllBot-∈ : ∀{C A}
           → AllBot A
           → C ∈ A
           → AllBot C
  AllBot-∈ {C} {U} bA refl = tt
  AllBot-∈ {C} {const x} bA refl = bA
  AllBot-∈ {C} {A ↦ A₁} bA refl = bA
  AllBot-∈ {C} {A ∩ A₁} ⟨ fst₁ , snd₁ ⟩ (inj₁ x) = AllBot-∈ fst₁ x
  AllBot-∈ {C} {A ∩ A₁} ⟨ fst₁ , snd₁ ⟩ (inj₂ y) = AllBot-∈ snd₁ y

  AllBot-⊆ : ∀{C A}
           → AllBot A
           → C ⊆ A
           → AllBot C
  AllBot-⊆ {U} {A} bA C⊆A = AllBot-∈ bA (C⊆A refl)
  AllBot-⊆ {const x} {A} bA C⊆A = AllBot-∈ bA (C⊆A refl)
  AllBot-⊆ {C ↦ C₁} {A} bA C⊆A = AllBot-∈ bA (C⊆A refl)
  AllBot-⊆ {C₁ ∩ C₂} {A} bA C⊆A
      with ∩⊆-inv C⊆A
  ... | ⟨ C₁⊆A , C₂⊆A ⟩ = ⟨ AllBot-⊆ bA C₁⊆A , AllBot-⊆ bA C₂⊆A ⟩


  AllBot-cod : ∀{A}
             → AllBot A
             → (fA : AllFun A)
             → AllBot (cod A {fA})
  AllBot-cod {U} bA ()
  AllBot-cod {const x} bA ()
  AllBot-cod {A ↦ A₁} bA fA = bA
  AllBot-cod {A₁ ∩ A₂} ⟨ fst₁ , snd₁ ⟩ ⟨ fst₂ , snd₂ ⟩ =
      ⟨ AllBot-cod fst₁ fst₂ , AllBot-cod snd₁ snd₂ ⟩


  AllBot-<: : ∀{C A}
           → AllBot A
           → A <: C
           → AllBot C
  AllBot-<: bA <:-U = tt
  AllBot-<: bA <:-const = bA
  AllBot-<: bA (<:-conj-L C<:A C<:A₁) = ⟨ AllBot-<: bA C<:A , AllBot-<: bA C<:A₁ ⟩
  AllBot-<: bA (<:-conj-R1 C<:A) = AllBot-<: (proj₁ bA) C<:A
  AllBot-<: bA (<:-conj-R2 C<:A) = AllBot-<: (proj₂ bA) C<:A
  AllBot-<: bA (<:-↦U x) = x
  AllBot-<: bA (<:-fun{A′ = A′} bC A′⊆A fA′ ∉U C<:A C<:A₁) =
    let bA′ = AllBot-⊆ bA A′⊆A in
    let bcA′ = AllBot-cod{A′} bA′ fA′ in
    AllBot-<: bcA′ C<:A₁


  <:-fun′ : ∀{B C B′ C′}
         → B <: B′
         → C′ <: C
           --------------------
         → (B′ ↦ C′) <: (B ↦ C)
  <:-fun′ {B}{C}{B′}{C′} B′<:B C<:C′
      with AllBot? C
  ... | yes ab = <:-↦U ab
  ... | no nab
      with AllBot? C′
  ... | yes ab′ =  ⊥-elim (nab (AllBot-<: ab′ C<:C′))
  ... | no nab′ =    
        <:-fun {B′ ↦ C′}{B′ ↦ C′}{B}{C} nab (λ {A} z → z) tt G B′<:B C<:C′
      where
      G : ∀ {B′₁ : Typ} {C′₁ : Typ} →
                AllBot C′₁ → ¬ B′₁ ↦ C′₁ ≡ B′ ↦ C′
      G ab refl = nab′ ab

  {-
    The traditional distributivity rule is admissible.
   -}


  AllBot-<:-any : ∀{A B} → AllBot A → B <: A
  AllBot-<:-any {U} {B} bA = <:-U
  AllBot-<:-any {const x} {B} ()
  AllBot-<:-any {A ↦ A₁} {B} bA = <:-↦U bA
  AllBot-<:-any {A ∩ A₁} {B} bA =
      <:-conj-L (AllBot-<:-any (proj₁ bA)) (AllBot-<:-any (proj₂ bA))


  <:-dist : ∀{B C C′}
           ---------------------------------
         → (B ↦ C) ∩ (B ↦ C′) <: B ↦ (C ∩ C′)
  <:-dist {B}{C}{C′}
      with AllBot? C | AllBot? C′
  ... | yes bC | yes bC′ = <:-↦U ⟨ bC , bC′ ⟩
  ... | yes bC | no bC′ =
        <:-fun {(B ↦ C) ∩ (B ↦ C′)} {(B ↦ C′)} {B} {C ∩ C′}
          (λ z → bC′ (proj₂ z))
          (λ {A} → inj₂)
          tt
          G
          <:-refl
          (<:-conj-L (AllBot-<:-any bC) <:-refl)
      where G : {B′ : Typ} {C′₁ : Typ} →
                AllBot C′₁ → ¬ B′ ↦ C′₁ ≡ B ↦ C′
            G bC1 refl = bC′ bC1

  <:-dist {B}{C}{C′} | no bC | yes bC′ =
      <:-fun {(B ↦ C) ∩ (B ↦ C′)} {(B ↦ C)} {B} {C ∩ C′}
            (λ z → bC (proj₁ z))
            (λ {A} → inj₁)
            tt
            G
            <:-refl
            (<:-conj-L <:-refl (AllBot-<:-any bC′))
      where G : {B′ : Typ} {C′₁ : Typ} →
                AllBot C′₁ → ¬ B′ ↦ C′₁ ≡ B ↦ C
            G bC1 refl = bC bC1

  <:-dist {B}{C}{C′} | no bC | no bC′ = 
    <:-fun {(B ↦ C) ∩ (B ↦ C′)} {(B ↦ C) ∩ (B ↦ C′)} {B} {C ∩ C′}
          (λ z → bC′ (proj₂ z))
          (λ {A} z → z) ⟨ tt , tt ⟩
          G
          (<:-conj-L <:-refl <:-refl)
          <:-refl
    where G : {B′ : Typ} {C′₁ : Typ} →
            AllBot C′₁ → ¬ (B′ ↦ C′₁ ≡ B ↦ C ⊎ B′ ↦ C′₁ ≡ B ↦ C′)
          G bC1 (inj₁ refl) = bC bC1
          G bC1 (inj₂ refl) = bC′ bC1

  {-

    The usual inversion rule for function subtyping.

   -}

  AllFun∈ : ∀{A}
        → AllFun A
        → Σ[ B ∈ Typ ] Σ[ C ∈ Typ ] B ↦ C ∈ A
  AllFun∈ {U} ()
  AllFun∈ {const k} ()
  AllFun∈ {B ↦ C} afA = ⟨ B , ⟨ C , refl ⟩ ⟩
  AllFun∈ {A₁ ∩ A₂} ⟨ fst₁ , snd₁ ⟩
      with AllFun∈ {A₁} fst₁
  ... | ⟨ B , ⟨ C , BC∈A ⟩ ⟩ =
        ⟨ B , ⟨ C , inj₁ BC∈A ⟩ ⟩

  ⊆↦→cod⊆ : ∀{A B C : Typ} {fA : AllFun A}
          → A ⊆ B ↦ C
            --------------
          → cod A {fA} ⊆ C
  ⊆↦→cod⊆ {U} {fA = ()}
  ⊆↦→cod⊆ {const k} {fA = ()}
  ⊆↦→cod⊆ {C ↦ C′} s A∈C′
      with s {C ↦ C′} refl
  ... | refl = A∈C′
  ⊆↦→cod⊆ {A₁ ∩ A₂}{B}{C} A⊆B↦C {B′} B′∈A′
      with B′∈A′
  ... | inj₁ B′∈B₁ =     
        ⊆↦→cod⊆ (λ x → A⊆B↦C (inj₁ x)) B′∈B₁
  ... | inj₂ B′∈B₂ =
        ⊆↦→cod⊆ (λ x → A⊆B↦C (inj₂ x)) B′∈B₂


  ∈→<: : ∀{A B : Typ}
      → A ∈ B
        -----
      → B <: A
  ∈→<: {A} {U} refl = <:-U
  ∈→<: {A} {const k} refl = <:-const
  ∈→<: {A} {B ↦ C} refl = <:-refl
  ∈→<: {A} {B₁ ∩ B₂} (inj₁ x) = <:-conj-R1 (∈→<: x)
  ∈→<: {A} {B₁ ∩ B₂} (inj₂ y) = <:-conj-R2 (∈→<: y)

  ⊆→<: : ∀{A B : Typ}
      → A ⊆ B
        -----
      → B <: A
  ⊆→<: {U} s with s {U} refl
  ... | x = <:-U
  ⊆→<: {const k} s with s {const k} refl
  ... | x = ∈→<: x
  ⊆→<: {A ↦ A′} s with s {A ↦ A′} refl
  ... | x = ∈→<: x
  ⊆→<: {A ∩ A′} s =
      <:-conj-L (⊆→<: (λ z → s (inj₁ z))) (⊆→<: (λ z → s (inj₂ z)))

  ↦∈→⊆dom : ∀{A B C : Typ} {fA : AllFun A}
        → (B ↦ C) ∈ A
          ----------------------------
        → B ⊆ dom A {fA}
  ↦∈→⊆dom {U} {fA = ()} eq 
  ↦∈→⊆dom {const k} {fA = ()} eq
  ↦∈→⊆dom {A₁ ↦ A₂}{B}{C} refl {B′} B′∈A₁ = B′∈A₁
  ↦∈→⊆dom {A₁ ∩ A₂} {B} {C} {⟨ f1 , f2 ⟩} (inj₁ B↦C∈A₁) {B'} B'∈B =
      inj₁ (↦∈→⊆dom {A₁}{B}{fA = f1} B↦C∈A₁ B'∈B)
  ↦∈→⊆dom {A₁ ∩ A₂} {B} {C} {⟨ f1 , f2 ⟩} (inj₂ B↦C∈A₂) {B'} B'∈B =
      inj₂ (↦∈→⊆dom {A₂}{B}{fA = f2} B↦C∈A₂ B'∈B)

  <:-fun-inv′ : ∀{B C B′ C′}
          → B′ ↦ C′ <: B ↦ C  →  ¬ AllBot C
            ---------------
          → B <: B′ × C′ <: C
  <:-fun-inv′ {B}{C}{B′}{C′} lt bC 
      with <:-fun-inv bC lt refl
  ... | ⟨ Γ , ⟨ f , ⟨ Γ⊆B34 , ⟨ ∉U , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ ⟩
      with AllFun∈ f
  ... | ⟨ A , ⟨ A′ , A↦A′∈Γ ⟩ ⟩
      with Γ⊆B34 A↦A′∈Γ
  ... | refl =    
    let codΓ⊆C′ = ⊆↦→cod⊆ Γ⊆B34 in
    let A⊆domΓ = ↦∈→⊆dom{Γ}{fA = f} A↦A′∈Γ in
    ⟨ <:-trans lt1 (⊆→<: A⊆domΓ) , <:-trans (⊆→<: codΓ⊆C′) lt2  ⟩

module EquiBNeCBCD where

  open BCDSubtyping
    using (_≤_; ≤-refl; ≤-incl-L; ≤-incl-R; ≤-glb; ≤-trans; ≤-→; ≤-→∩; ≤-U-top;
           ≤-U→)

  open NewSubtyping
    using (_<:_; <:-refl; <:-conj-R1; <:-conj-R2; <:-conj-L; <:-trans;
           <:-U; <:-↦U; <:-dist; <:-fun′; ∩⊆-inv; <:-fun; <:-const)

  ≤→<: : ∀{A B} → B ≤ A → B <: A
  ≤→<: ≤-refl = <:-refl
  ≤→<: ≤-incl-L = <:-conj-R1 <:-refl
  ≤→<: ≤-incl-R = <:-conj-R2 <:-refl
  ≤→<: (≤-glb A≤B A≤B₁) = <:-conj-L (≤→<: A≤B) (≤→<: A≤B₁)
  ≤→<: (≤-trans A≤B A≤B₁) = <:-trans (≤→<: A≤B) (≤→<: A≤B₁)
  ≤→<: ≤-U-top = <:-U
  ≤→<: ≤-U→ = <:-↦U tt
  ≤→<: ≤-→∩ = <:-dist
  ≤→<: (≤-→ A≤B A≤B₁) = <:-fun′ (≤→<: A≤B) (≤→<: A≤B₁)

  AllBot≤U : ∀{A} → AllBot A → U ≤ A
  AllBot≤U {U} bA = ≤-refl
  AllBot≤U {const x} ()
  AllBot≤U {A ↦ A₁} bA = ≤-trans ≤-U→ (≤-→ ≤-refl (AllBot≤U bA))
  AllBot≤U {A ∩ A₁} bA = ≤-glb (AllBot≤U (proj₁ bA)) (AllBot≤U (proj₂ bA))

  ∩≤-inv : ∀{B C A}
      → A ≤ B ∩ C
      → A ≤ B × A ≤ C
  ∩≤-inv ≤-refl = ⟨ ≤-incl-L , ≤-incl-R ⟩
  ∩≤-inv ≤-incl-L =
      ⟨ (≤-trans ≤-incl-L ≤-incl-L) , (≤-trans ≤-incl-L ≤-incl-R ) ⟩
  ∩≤-inv ≤-incl-R =
      ⟨ (≤-trans ≤-incl-R ≤-incl-L) , (≤-trans ≤-incl-R ≤-incl-R) ⟩
  ∩≤-inv (≤-glb B∩C≤A B∩C≤A₁) = ⟨ B∩C≤A , B∩C≤A₁ ⟩
  ∩≤-inv (≤-trans B∩C≤A₁ B∩C≤A ) =
      ⟨ (≤-trans B∩C≤A₁ (proj₁ (∩≤-inv B∩C≤A))) ,
        (≤-trans B∩C≤A₁ (proj₂ (∩≤-inv B∩C≤A))) ⟩

  ∈→≤ : ∀{A B} → A ∈ B → B ≤ A
  ∈→≤ {A} {U} refl = ≤-refl
  ∈→≤ {A} {const x} refl = ≤-refl
  ∈→≤ {A} {B ↦ B₁} refl = ≤-refl
  ∈→≤ {A} {B₁ ∩ B₂} (inj₁ x) = ≤-trans ≤-incl-L (∈→≤ x)
  ∈→≤ {A} {B₁ ∩ B₂} (inj₂ y) = ≤-trans ≤-incl-R (∈→≤ y)

  ⊆→≤ : ∀{A B} → A ⊆ B → B ≤ A
  ⊆→≤ {U} {B} A⊆B = ∈→≤ (A⊆B refl)
  ⊆→≤ {const x} {B} A⊆B = ∈→≤ (A⊆B refl)
  ⊆→≤ {A ↦ A₁} {B} A⊆B = ∈→≤ (A⊆B refl)
  ⊆→≤ {A₁ ∩ A₂} {B} A⊆B
      with ∩⊆-inv A⊆B
  ... | ⟨ A₁⊆B , A₂⊆B ⟩ = ≤-glb (⊆→≤ A₁⊆B) (⊆→≤ A₂⊆B)

  ∩≤∩ : ∀ {B C B′ C′}
      → B ≤ B′  →  C ≤ C′
        -------------------
      → B ∩ C ≤ B′ ∩ C′
  ∩≤∩ d₁ d₂ = ≤-glb (≤-trans  ≤-incl-L d₁) (≤-trans ≤-incl-R d₂)

  Dist∩↦∩ : ∀{B B′ C C′ : Typ}
          → (B ↦ C) ∩ (B′ ↦ C′) ≤ (B ∩ B′) ↦ (C ∩ C′) 
  Dist∩↦∩ = ≤-trans (∩≤∩ (≤-→ ≤-incl-L ≤-refl) (≤-→ ≤-incl-R ≤-refl))
                    ≤-→∩ 

  dB↦cB≤B : ∀{B}{fB : AllFun B}
            → B ≤ dom B {fB} ↦ cod B {fB}
  dB↦cB≤B {U} {()}
  dB↦cB≤B {const x} {()} 
  dB↦cB≤B {B₁ ↦ B₂} {fB} = ≤-refl
  dB↦cB≤B {B₁ ∩ B₂} {⟨ fB1 , fB2 ⟩} =
        let ih1 = dB↦cB≤B {B₁}{fB1}  in
        let ih2 = dB↦cB≤B {B₂}{fB2} in
        ≤-trans (≤-glb (≤-trans ≤-incl-L ih1) (≤-trans ≤-incl-R ih2))
                 Dist∩↦∩ 

  <:→≤ : ∀{A B} → B <: A → B ≤ A
  <:→≤ <:-U = ≤-U-top
  <:→≤ <:-const = ≤-refl
  <:→≤ (<:-conj-L A<:B A<:B₁) = ≤-glb (<:→≤ A<:B) (<:→≤ A<:B₁)
  <:→≤ (<:-conj-R1 A<:B) = ≤-trans ≤-incl-L (<:→≤ A<:B)
  <:→≤ (<:-conj-R2 A<:B) = ≤-trans ≤-incl-R (<:→≤ A<:B)
  <:→≤ {A₁ ↦ A₂} {B} (<:-↦U bA₂) = ≤-trans H G
        where
        G : A₁ ↦ U ≤ A₁ ↦ A₂
        G = ≤-→ ≤-refl (AllBot≤U bA₂)
        H : B ≤ A₁ ↦ U
        H = ≤-trans ≤-U-top ≤-U→ 
  <:→≤ (<:-fun{A′ = B′} nbA₂ B′⊆B fB′ ∉U dB′<:A₁ A₂<:cB′) =
     let dB′≤A₁ = <:→≤ dB′<:A₁ in
     let A₂≤cB′ = <:→≤ A₂<:cB′ in
     let B′≤B = ⊆→≤ B′⊆B in
     ≤-trans B′≤B (≤-trans dB↦cB≤B (≤-→ dB′≤A₁ A₂≤cB′)) 
