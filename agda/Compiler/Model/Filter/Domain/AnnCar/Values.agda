{-# OPTIONS --allow-unsolved-metas #-}

open import Function using (_∘_)
open import Data.Nat using (ℕ; suc ; zero; _+_; _≤′_; _<′_; _<_; _≤_;
    z≤n; s≤s; ≤′-refl; ≤′-step; _≟_) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ≤-step; ⊔-mono-≤;
         +-mono-≤; +-mono-≤-<; +-mono-<-≤; +-comm; +-assoc; n≤1+n;
         ≤-pred; m≤m+n; m≤n+m; ≤-reflexive; ≤′⇒≤; ≤⇒≤′; +-suc;
         mono-≤-distrib-⊔; ⊔-lub; ⊔-assoc; ⊔-comm)
open Data.Nat.Properties.≤-Reasoning using (begin_; _∎; step-≤)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂;
  uncurry)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Product.Properties using (,-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_ ; []; _++_)
open import Data.List.Relation.Binary.Subset.Propositional using ()
  renaming (_⊆_ to _l⊆_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.All 
  using ([]; _∷_; tabulate; all?)
  renaming (All to listAll; head to listhead; tail to listtail; map to allmap; 
            lookup to listlookup)
open import Data.List.Properties using (++-conicalˡ; ∷-dec)
open import Data.Vec using (Vec; []; _∷_; length; head; tail; lookup; zipWith)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using (Pointwise; []; _∷_; head; tail; uncons)
open import Data.Vec.Relation.Unary.All using ([]; _∷_; All; head; tail; map)
open import Data.Vec.Properties using (≡-dec; ∷-injective)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Bool using (Bool; true; false)
  renaming (_≟_ to _b≟_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Product using (_×-dec_)

module Compiler.Model.Filter.Domain.AnnCar.Values where

open import Primitives
open import SetsAsPredicates
open import Compiler.Model.Filter.Domain.Util


infix 4 _∧dec_
infix 3 _∨dec_

_∧dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
(yes p) ∧dec (yes q) = yes ⟨ p , q ⟩
(yes p) ∧dec (no q) = no (λ pq → (q (proj₂ pq)))
(no p) ∧dec decb = no (λ pq → (p (proj₁ pq)))

_∨dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
(yes p) ∨dec decb = yes (inj₁ p)
(no p) ∨dec (yes q) = yes (inj₂ q)
(no p) ∨dec (no q) = no (λ pq → [ p , q ] pq)

¬dec : ∀ {A : Set} → Dec A → Dec (¬ A)
¬dec (yes p) = no (λ ¬p → (¬p p))
¬dec (no p) = yes p

infixr 7 _↦_
infixl 6 _⊔_
infixl 8 tup[_]_
infix 5 _◃_▹_  {- prounounced "split" -}
{- ◂ \tw and \tw2 ▹ (or \tw[right arrow key])  -}


{- Went with half-pair values instead of using ⦅ u , ω ⦆ and ⦅ ω , v ⦆ atoms
  just because breaking ⦅ u , v ⦆ into those two cases and a default non-atomic case
  turned out to be a pain -}
data Value : Set where
  ω : Value {- represents no info -}
  ν : Value
  const : {B : Base} → (k : base-rep B) → Value
  _⊔_ : (u : Value) → (v : Value) → Value
  _↦_ : (v : Value) → (w : Value) → Value
  ⦅_,_∣ : (u : Value) → (b : Bool) → Value
  ∣_⦆ : (v : Value) → Value
  tup[_]_ : {n : ℕ} → (i : Fin n) → Value → Value
  left : (d : Value) → Value
  right : (d : Value) → Value

value_struct : ValueStruct
value_struct = record { Value = Value ; ⊥ = ω ; _↦_ = _↦_ ; _⊔_ = _⊔_}


{- --- Splitting: Atomic and Proper values ---------------------------------- -}

Atomic : Value → Set
Atomic ω = ⊤
Atomic ν = ⊤
Atomic (const k) = ⊤
Atomic ⦅ u , b ∣ = Atomic u
Atomic ∣ v ⦆ = Atomic v
Atomic (tup[ i ] d) = Atomic d
Atomic (v ↦ v₁) = Atomic v₁
Atomic (left d) = Atomic d
Atomic (right d) = Atomic d
Atomic (v ⊔ v₁) = False

atomic? : (v : Value) → Dec (Atomic v)
atomic? ω = yes tt
atomic? ν = yes tt
atomic? (const k) = yes tt
atomic? ⦅ u , b ∣ = atomic? u
atomic? ∣ v ⦆ = atomic? v
atomic? (tup[ i ] d)  = atomic? d
atomic? (v ↦ v₁) = atomic? v₁
atomic? (v ⊔ u) = no (λ z → z)
atomic? (left d) = atomic? d
atomic? (right d) = atomic? d

data _◃_▹_ : (v₁ v v₂ : Value) → Set where
  
  split-⊔ : ∀ {u v}
        ----------------
        → u ◃ u ⊔ v ▹ v

  split-↦ : ∀ {u v v₁ v₂}
        →       v₁ ◃ v ▹ v₂
      -----------------------------
        → u ↦ v₁ ◃ u ↦ v ▹ u ↦ v₂ 

  split-fst : ∀ {u u₁ u₂ b}
        →           u₁ ◃ u ▹ u₂ 
      -------------------------------------
        → ⦅ u₁ , b ∣ ◃ ⦅ u , b ∣ ▹ ⦅ u₂ , b ∣

  split-snd : ∀ {v v₁ v₂}
        →           v₁ ◃ v ▹ v₂
      --------------------------------------
        → ∣ v₁ ⦆ ◃ ∣ v ⦆ ▹ ∣ v₂ ⦆

  split-tup : ∀ {n} {i : Fin n} {d dL dR}
        →           dL ◃ d ▹ dR
      --------------------------------------------------
        → tup[ i ] dL ◃ tup[ i ] d ▹ tup[ i ] dR

  split-left : ∀ {d d₁ d₂}
        → d₁ ◃ d ▹ d₂
      ----------------------------------------------
        → left d₁ ◃ left d ▹ left d₂

  split-right : ∀ {d d₁ d₂}
        → d₁ ◃ d ▹ d₂
      ----------------------------------------------
        → right d₁ ◃ right d ▹ right d₂


split-unique : ∀ {u uL uR} → uL ◃ u ▹ uR → ∀ {uL' uR'} → uL' ◃ u ▹ uR' → uL' ≡ uL × uR' ≡ uR
split-unique {u = .(_ ⊔ _)} split-⊔ split-⊔ = ⟨ refl , refl ⟩
split-unique {u = .( _ ↦ _)} (split-↦ split) (split-↦ split')
   with split-unique split split'
... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
split-unique {u = .(⦅ _ , _ ∣)} (split-fst split) (split-fst split')
   with split-unique split split'
... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
split-unique {u = .(∣ _ ⦆)} (split-snd split) (split-snd split')
   with split-unique split split'
... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
split-unique {u = .(tup[ _ ] _)} (split-tup split) (split-tup split')
   with split-unique split split'
... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
split-unique {u = .(left _)} (split-left split) (split-left split')
   with split-unique split split'
... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
split-unique {u = .(right _)} (split-right split) (split-right split')
   with split-unique split split'
... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩

unsplittable : ∀ v → Atomic v → ∀ {v₁ v₂} → ¬ (v₁ ◃ v ▹ v₂)
unsplittable (v ↦ v₁) åv (split-↦ split) = unsplittable v₁ åv split
unsplittable ⦅ v , b ∣ åv (split-fst split) = unsplittable v åv split
unsplittable ∣ v ⦆ åv (split-snd split) = unsplittable v åv split
unsplittable (tup[ i ] d) åv (split-tup split) = unsplittable d åv split
unsplittable (left d) åv (split-left split) = unsplittable d åv split
unsplittable (right d) åv (split-right split) = unsplittable d åv split


data Proper : Value → Set where
 
  ⊢'-ω : Proper ω

  ⊢'-ν : Proper ν

  ⊢'-const : ∀ {B} k → Proper (const {B} k)

  ⊢'-↦-å : ∀ {V w}
            → (⊢'V : Proper V)
            → (⊢'w : Proper w)
            → (åw :  Atomic w)
            → Proper (V ↦ w)

  ⊢'-fst-å : ∀ {v₁ b} 
            → (⊢'v₁ : Proper v₁)
            → (åv₁ : Atomic v₁)
            → Proper ⦅ v₁ , b ∣
  
  ⊢'-snd-å : ∀ {v₂} 
            → (⊢'v₂ : Proper v₂) 
            → (åv₂ : Atomic v₂)
            → Proper ∣ v₂ ⦆

  ⊢'-tup-å : ∀ {n} {i : Fin n} {d}
           → (⊢'d : Proper d)
           → (åd : Atomic d)
           → Proper (tup[ i ] d)
  
  ⊢'-left-å : ∀ {v}
           → (⊢'v : Proper v)
           → (åv : Atomic v)
           → Proper (left v)

  ⊢'-right-å : ∀ {v}
           → (⊢'v : Proper v)
           → (åv : Atomic v)
           → Proper (right v)

  ⊢'-split : ∀ {v} vL vR
            → (split : vL ◃ v ▹ vR)
            → (⊢'L : Proper vL)
            → (⊢'R : Proper vR)
            → Proper v

proper-left : ∀ {d} → Proper d → Proper (left d)
proper-left ⊢'-ω = ⊢'-left-å ⊢'-ω tt
proper-left ⊢'-ν = ⊢'-left-å ⊢'-ν tt
proper-left (⊢'-const k) = ⊢'-left-å (⊢'-const k) tt
proper-left (⊢'-↦-å Pd₁ Pd₂ åw) = ⊢'-left-å (⊢'-↦-å Pd₁ Pd₂ åw) åw 
proper-left (⊢'-fst-å Pd åv₁) = ⊢'-left-å (⊢'-fst-å Pd åv₁) åv₁
proper-left (⊢'-snd-å Pd åv₂) = ⊢'-left-å (⊢'-snd-å Pd åv₂) åv₂
proper-left (⊢'-tup-å Pd åd) = ⊢'-left-å (⊢'-tup-å Pd åd) åd
proper-left (⊢'-left-å Pd åv) = ⊢'-left-å (proper-left Pd) åv
proper-left (⊢'-right-å Pd åv) = ⊢'-left-å (⊢'-right-å Pd åv) åv
proper-left (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split (left vL) (left vR) (split-left split) (proper-left Pd) (proper-left Pd₁)



proper-right : ∀ {d} → Proper d → Proper (right d)
proper-right ⊢'-ω = ⊢'-right-å ⊢'-ω tt
proper-right ⊢'-ν = ⊢'-right-å ⊢'-ν tt
proper-right (⊢'-const k) = ⊢'-right-å (⊢'-const k) tt
proper-right (⊢'-↦-å Pd₁ Pd₂ åw) =
   ⊢'-right-å (⊢'-↦-å Pd₁ Pd₂ åw) åw
proper-right (⊢'-fst-å Pd åv₁) = ⊢'-right-å (⊢'-fst-å Pd åv₁) åv₁
proper-right (⊢'-snd-å Pd åv₂) = ⊢'-right-å (⊢'-snd-å Pd åv₂) åv₂
proper-right (⊢'-tup-å Pd åd) = ⊢'-right-å (⊢'-tup-å Pd åd) åd
proper-right (⊢'-left-å Pd åv) = ⊢'-right-å (⊢'-left-å Pd åv) åv
proper-right (⊢'-right-å Pd åv) = ⊢'-right-å (proper-right Pd) åv
proper-right (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split (right vL) (right vR) (split-right split) (proper-right Pd) (proper-right Pd₁)

proper-↦ : ∀ {u v} → Proper u → Proper v → Proper (u ↦ v)
proper-↦ {u}{v} Pu Pv with atomic? v
... | yes åv = ⊢'-↦-å Pu Pv åv
... | no ¬åv with Pv
... | ⊢'-ω = ⊥-elim (¬åv tt)
... | ⊢'-ν = ⊥-elim (¬åv tt)
... | ⊢'-const k = ⊥-elim (¬åv tt)
... | ⊢'-↦-å Pv₁ Pv₂ åw = ⊥-elim (¬åv åw)
... | ⊢'-fst-å Pv₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-snd-å Pv₁ åv₂ = ⊥-elim (¬åv åv₂)
... | ⊢'-tup-å Pd åd = ⊥-elim (¬åv åd)
... | ⊢'-left-å Pv₁ åv = ⊥-elim (¬åv åv)
... | ⊢'-right-å Pv₁ åv = ⊥-elim (¬åv åv)
... | ⊢'-split vL vR split Pv₁ Pv₂ = 
   ⊢'-split (u ↦ vL) (u ↦ vR) (split-↦ split) 
            (proper-↦ Pu Pv₁) (proper-↦ Pu Pv₂)

proper-fst : ∀ {d b} → Proper d → Proper ⦅ d , b ∣
proper-fst ⊢'-ω = ⊢'-fst-å ⊢'-ω tt
proper-fst ⊢'-ν = ⊢'-fst-å ⊢'-ν tt
proper-fst (⊢'-const k) = ⊢'-fst-å (⊢'-const k) tt
proper-fst (⊢'-↦-å Pd₁ Pd₂ åw) = ⊢'-fst-å (⊢'-↦-å Pd₁ Pd₂ åw) åw
proper-fst (⊢'-fst-å Pd åv₁) = ⊢'-fst-å (proper-fst Pd) åv₁
proper-fst (⊢'-snd-å Pd åv₂) = ⊢'-fst-å (⊢'-snd-å Pd åv₂) åv₂
proper-fst (⊢'-tup-å Pd åd) = ⊢'-fst-å (⊢'-tup-å Pd åd) åd
proper-fst (⊢'-left-å Pd åv) = ⊢'-fst-å (⊢'-left-å Pd åv) åv
proper-fst (⊢'-right-å Pd åv) = ⊢'-fst-å (⊢'-right-å Pd åv) åv
proper-fst {d}{b} (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split ⦅ vL , b ∣ ⦅ vR , b ∣ (split-fst split) (proper-fst Pd) (proper-fst Pd₁)


proper-snd : ∀ {d} → Proper d → Proper ∣ d ⦆
proper-snd ⊢'-ω = ⊢'-snd-å ⊢'-ω tt
proper-snd ⊢'-ν = ⊢'-snd-å ⊢'-ν tt
proper-snd (⊢'-const k) = ⊢'-snd-å (⊢'-const k) tt
proper-snd (⊢'-↦-å Pd₁ Pd₂ åw) = ⊢'-snd-å (⊢'-↦-å Pd₁ Pd₂ åw) åw
proper-snd (⊢'-fst-å Pd åv₁) = ⊢'-snd-å (⊢'-fst-å Pd åv₁) åv₁
proper-snd (⊢'-snd-å Pd åv₂) = ⊢'-snd-å (proper-snd Pd) åv₂
proper-snd (⊢'-tup-å Pd åd) = ⊢'-snd-å (⊢'-tup-å Pd åd) åd
proper-snd (⊢'-left-å Pd åv) = ⊢'-snd-å (⊢'-left-å Pd åv) åv
proper-snd (⊢'-right-å Pd åv) = ⊢'-snd-å (⊢'-right-å Pd åv) åv
proper-snd (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split ∣ vL ⦆ ∣ vR ⦆ (split-snd split) (proper-snd Pd) (proper-snd Pd₁)


proper-tup : ∀ {n}{i : Fin n}{d} → Proper d → Proper (tup[ i ] d)
proper-tup ⊢'-ω = ⊢'-tup-å ⊢'-ω tt
proper-tup ⊢'-ν = ⊢'-tup-å ⊢'-ν tt
proper-tup (⊢'-const k) = ⊢'-tup-å (⊢'-const k) tt
proper-tup (⊢'-↦-å Pd₁ Pd₂ åw) = ⊢'-tup-å (⊢'-↦-å Pd₁ Pd₂ åw) åw
proper-tup (⊢'-fst-å Pd åv₁) = ⊢'-tup-å (⊢'-fst-å Pd åv₁) åv₁
proper-tup (⊢'-snd-å Pd åv₂) = ⊢'-tup-å (⊢'-snd-å Pd åv₂) åv₂
proper-tup (⊢'-tup-å Pd åd) = ⊢'-tup-å (proper-tup Pd) åd
proper-tup (⊢'-left-å Pd åv) = ⊢'-tup-å (⊢'-left-å Pd åv) åv
proper-tup (⊢'-right-å Pd åv) = ⊢'-tup-å (⊢'-right-å Pd åv) åv
proper-tup {n}{i} (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split (tup[ i ] vL) (tup[ i ] vR) (split-tup split) (proper-tup Pd) (proper-tup Pd₁)


proper : ∀ v → Proper v
proper ω = ⊢'-ω
proper ν = ⊢'-ν
proper (const k) = ⊢'-const k
proper (v ⊔ v₁) = ⊢'-split v v₁ split-⊔ (proper v) (proper v₁)
proper (v ↦ v₁) = proper-↦ (proper v) (proper v₁)
proper ⦅ u , b ∣ = proper-fst (proper u)
proper ∣ v ⦆ = proper-snd (proper v)
proper (tup[ i ] d) = proper-tup (proper d)
proper (left d) = proper-left (proper d)
proper (right d) = proper-right (proper d)



¬å⇒split : ∀ v → ¬ (Atomic v) → Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] v₁ ◃ v ▹ v₂
¬å⇒split v ¬åv with (proper v)
... | ⊢'-ω = ⊥-elim (¬åv tt)
... | ⊢'-ν = ⊥-elim (¬åv tt)
... | ⊢'-const k = ⊥-elim (¬åv tt)
... | ⊢'-↦-å Pv Pv₁ åv₂ = ⊥-elim (¬åv åv₂)
... | ⊢'-fst-å Pu₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-snd-å Pu₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-tup-å Pd åd = ⊥-elim (¬åv åd)
... | ⊢'-left-å Pv åv = ⊥-elim (¬åv åv)
... | ⊢'-right-å Pv åv = ⊥-elim (¬åv åv)
... | ⊢'-split vL vR split Pv Pv₁ = ⟨ vL , ⟨ vR , split ⟩ ⟩

{- Size/Depth -----------------------------------------------------------------}

depth : (v : Value) → ℕ
depth ω = zero
depth ν = zero
depth (const k) = zero
depth ( v ↦ w) = suc (max (depth v) (depth w))
depth (v₁ ⊔ v₂) = max (depth v₁) (depth v₂)
depth ⦅ v , b ∣ = suc (depth v)
depth ∣ v ⦆ = suc (depth v)
depth (tup[ i ] d) = suc (depth d)
depth (left d) = suc (depth d)
depth (right d) = suc (depth d)

size : (v : Value) → ℕ
size ω = zero
size ν = zero
size (const k) = zero
size ( v ↦ w) = suc (size v + size w)
size (v₁ ⊔ v₂) = suc (size v₁ + size v₂)
size ⦅ u , b ∣ = suc (size u)
size ∣ v ⦆ = suc (size v)
size (tup[ i ] d) = suc (size d) 
size (left d) = suc (size d)
size (right d) = suc (size d)



{- Equality -------------------------------------------------------------------}

l⊆→All∈ : ∀ {A : Set} (U V : List A) → U l⊆ V → listAll (λ z → Any (z ≡_) V) U
l⊆→All∈ U V = tabulate

All∈→l⊆ : ∀ {A : Set} {U V : List A} → listAll (λ z → Any (z ≡_) V) U → U l⊆ V
All∈→l⊆ = listlookup

_⊢_l⊆?_ : ∀ {A : Set} (≡? : ∀ (a b : A) → Dec (a ≡ b)) (U V : List A) → Dec (U l⊆ V)
≡? ⊢ U l⊆? V = map′ All∈→l⊆ (l⊆→All∈ U V) (all? (λ x → any? (λ y → ≡? x y) V) U)

l⊆→⊆ : ∀ {A : Set} (U V : List A) → U l⊆ V → mem U ⊆ mem V
l⊆→⊆ U V Ul⊆V d = Ul⊆V {d}

⊆→l⊆ : ∀ {A : Set} (U V : List A) → mem U ⊆ mem V → U l⊆ V
⊆→l⊆ U V U⊆V {d} = U⊆V d

const-inj-base : ∀ {B B' k k'} → const {B} k ≡ const {B'} k' → B ≡ B'
const-inj-base {B}{B'} refl = refl

const-inj : ∀ {B k k'} → const {B} k ≡ const {B} k' → k ≡ k'
const-inj refl = refl

tup-inj-easy : ∀ {n} {i i' : Fin n} {d d'} → (tup[ i ] d) ≡ (tup[ i' ] d') 
   → ⟨ i , d ⟩ ≡ ⟨ i' , d' ⟩
tup-inj-easy refl = refl

tup-inj : ∀ {n n'} {i : Fin n} {i' : Fin n'} {d d'} 
        → (tup[ i ] d) ≡ (tup[ i' ] d') → 
   Σ[ n≡n' ∈ n ≡ n' ] (subst Fin n≡n' i) ≡ i' × d ≡ d'
tup-inj refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

tup-inj-uncurried : ∀ {n n'} {i : Fin n} {i' : Fin n'} {d d'} 
        → (tup[ i ] d) ≡ (tup[ i' ] d') → 
   Σ[ n≡n' ∈ n ≡ n' ] ⟨ (subst Fin n≡n' i) , d ⟩ ≡ ⟨ i' , d' ⟩
tup-inj-uncurried refl = ⟨ refl , refl ⟩

tup-inj-uncurried' : ∀ {n n'} {i : Fin n} {i' : Fin n'} {d d'} 
        → (tup[ i ] d) ≡ (tup[ i' ] d') → (n≡n' : n ≡ n') →
   ⟨ (subst Fin n≡n' i) , d ⟩ ≡ ⟨ i' , d' ⟩
tup-inj-uncurried' refl refl = refl

left-inj : ∀ {v v'} → (left v) ≡ left v' → v ≡ v'
left-inj refl = refl

right-inj : ∀ {v v'} → (right v) ≡ right v' → v ≡ v'
right-inj refl = refl

fst-inj : ∀ {v v' b b'} → ⦅ v , b ∣ ≡ ⦅ v' , b' ∣ → v ≡ v' × b ≡ b'
fst-inj refl = ⟨ refl , refl ⟩

snd-inj : ∀ {v v'} → ∣ v ⦆ ≡ ∣ v' ⦆ → v ≡ v'
snd-inj refl = refl

↦-inj-uncurried : ∀ {V V' w w'} →  V ↦ w ≡  V' ↦ w'
      → ⟨ V , w ⟩ ≡ ⟨ V' , w' ⟩
↦-inj-uncurried refl = refl

⊔-inj : ∀ {d₁ d₂ d₁' d₂'} → d₁ ⊔ d₂ ≡ d₁' ⊔ d₂' → d₁ ≡ d₁' × d₂ ≡ d₂'
⊔-inj refl = ⟨ refl , refl ⟩

_d≟_ : (d₁ : Value) → (d₂ : Value) → Dec (d₁ ≡ d₂)
const {B} k d≟ const {B'} k₁ with base-eq? B B'
... | no neq = no λ z → neq (const-inj-base z)
... | yes refl = map′ (cong (const {B})) const-inj (base-rep-eq? k k₁)
const k d≟ ν = no (λ ())
const k d≟ (V ↦ w) = no (λ ())
const k d≟ ω = no (λ ())
const k d≟ (tup[ i ] d) = no (λ ())
const k d≟ (left v₁) = no (λ ())
const k d≟ (right v₁) = no (λ ())
const k d≟ (u ⊔ v) = no (λ ())
const k d≟ ⦅ v , b ∣ = no (λ ())
const k d≟ ∣ v ⦆ = no (λ ())
(V ↦ w) d≟ const k = no (λ ())
(V ↦ w) d≟ ( V' ↦ w') = 
  map′ (cong (λ z → proj₁ z ↦ (proj₂ z)))
        ↦-inj-uncurried 
        (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((V d≟ V') ×-dec (w d≟ w')))
(V ↦ w) d≟ ν = no (λ ())
(V ↦ w) d≟ ω = no (λ ())
(V ↦ w) d≟ (tup[ i ] d) = no (λ ())
(V ↦ w) d≟ (left v₁) = no (λ ())
(V ↦ w) d≟ (right v₁) = no (λ ())
(V ↦ w) d≟ (u ⊔ v) = no (λ ())
(u₁ ↦ u₂) d≟ ⦅ v , b ∣ = no (λ ())
(u₁ ↦ u₂) d≟ ∣ v ⦆ = no (λ ())
ν d≟ const k = no (λ ())
ν d≟ (V ↦ d₃) = no (λ ())
ν d≟ ν = yes refl
ν d≟ ω = no (λ ())
ν d≟ (tup[ i ] d) = no (λ ())
ν d≟ (left v) = no (λ ())
ν d≟ (right v) = no (λ ())
ν d≟ (u ⊔ v) = no (λ ())
ν d≟ ⦅ v , b ∣ = no (λ ())
ν d≟ ∣ v ⦆ = no (λ ())
ω d≟ const k = no (λ ())
ω d≟ ( V ↦ d₃) = no (λ ())
ω d≟ ν = no (λ ())
ω d≟ ω = yes refl
ω d≟ (tup[ i ] d) = no (λ ())
ω d≟ (left v) = no (λ ())
ω d≟  (right v) = no (λ ())
ω d≟ (u ⊔ v) = no (λ ())
ω d≟ ⦅ v , b ∣ = no (λ ())
ω d≟ ∣ v ⦆ = no (λ ())
(tup[ i ] d) d≟ const k = no (λ ())
(tup[ i ] d) d≟ (V ↦ d₃) = no (λ ())
(tup[ i ] d) d≟ ν = no (λ ())
(tup[ i ] d) d≟ ω = no (λ ())
(tup[_]_ {n} i d) d≟ (tup[_]_ {n'} i' d') with n ≟ n'
... | no neq = no λ z → neq (proj₁ (tup-inj z))
... | yes refl = map′ (cong (λ z → tup[ proj₁ z ] proj₂ z))
        (λ z → tup-inj-uncurried' z refl)
        (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective (i fin≟ i' ×-dec (d d≟ d')))
(tup[ i ] d) d≟ (left v) = no (λ ())
(tup[ i ] d) d≟ (right v) = no (λ ())
(tup[ i ] d) d≟ (u ⊔ v) = no (λ ())
(tup[ i ] d) d≟ ⦅ v , b ∣ = no (λ ())
(tup[ i ] d) d≟ ∣ v ⦆ = no (λ ())
(left v) d≟ const k = no (λ ())
(left v) d≟ (V₁ ↦ d₃) = no (λ ())
(left v) d≟ ν = no (λ ())
(left v) d≟ ω = no (λ ())
(left v) d≟ (tup[ i ] d) = no (λ ())
(left v) d≟ (left v₁) = map′ (cong left) left-inj (v d≟ v₁)
(left v) d≟ (right v₁) = no (λ ())
(left v) d≟ (u ⊔ v₁) = no (λ ())
left u d≟ ⦅ v , b ∣ = no (λ ())
left u d≟ ∣ v ⦆ = no (λ ())
(right v) d≟ const k = no (λ ())
(right v) d≟ (V₁ ↦ d₃) = no (λ ())
(right v) d≟ ν = no (λ ())
(right v) d≟ ω = no (λ ())
(right v) d≟ (tup[ i ] d) = no (λ ())
(right v) d≟ (left v₁) = no (λ ())
(right v) d≟ (right v₁) = map′ (cong right) right-inj (v d≟ v₁)
(right v) d≟ (u ⊔ v₁) = no (λ ())
right u d≟ ⦅ v , b ∣ = no (λ ())
right u d≟ ∣ v ⦆ = no (λ ())
(u ⊔ v) d≟ ω = no (λ ())
(u ⊔ v) d≟ ν = no (λ ())
(u ⊔ v) d≟ const k = no (λ ())
(u ⊔ v) d≟ (d ⊔ d₁) = map′ (uncurry (cong₂ _⊔_)) ⊔-inj ((u d≟ d) ×-dec (v d≟ d₁))
(u ⊔ v) d≟ (d₁ ↦ d₂) = no (λ ())
(u ⊔ v) d≟ (tup[ i ] d) = no (λ ())
(u ⊔ v) d≟ left d = no (λ ())
(u ⊔ v) d≟ right d = no (λ ())
(u ⊔ u₁) d≟ ⦅ v , b ∣ = no (λ ())
(u ⊔ u₁) d≟ ∣ v ⦆ = no (λ ())
⦅ u , b ∣ d≟ ω = no (λ ())
⦅ u , b ∣ d≟ ν = no (λ ())
⦅ u , b ∣ d≟ const k = no (λ ())
⦅ u , b ∣ d≟ (v ⊔ v₁) = no (λ ())
⦅ u , b ∣ d≟ (v₁ ↦ v₂) = no (λ ())
⦅ u , b ∣ d≟ ⦅ v , b' ∣ = 
  map′ (uncurry (cong₂ ⦅_,_∣)) fst-inj ((u d≟ v) ×-dec (b b≟ b'))
⦅ u , b ∣ d≟ ∣ v ⦆ = no (λ ())
⦅ u , b ∣ d≟ (tup[ i ] d) = no (λ ())
⦅ u , b ∣ d≟ left v = no (λ ())
⦅ u , b ∣ d≟ right v = no (λ ())
∣ u ⦆ d≟ ω = no (λ ())
∣ u ⦆ d≟ ν = no (λ ())
∣ u ⦆ d≟ const k = no (λ ())
∣ u ⦆ d≟ (v ⊔ v₁) = no (λ ())
∣ u ⦆ d≟ (v₁ ↦ v₂) = no (λ ())
∣ u ⦆ d≟ ⦅ v , b ∣ = no (λ ())
∣ u ⦆ d≟ ∣ v ⦆ = map′ (cong ∣_⦆) snd-inj (u d≟ v)
∣ u ⦆ d≟ (tup[ i ] d) = no (λ ())
∣ u ⦆ d≟ left v = no (λ ())
∣ u ⦆ d≟ right v = no (λ ())

_l⊆?_ : ∀ (U V : List Value) → Dec (U l⊆ V)
U l⊆? V = _d≟_ ⊢ U l⊆? V

_mem⊆?_ : ∀ (U V : List Value) → Dec (mem U ⊆ mem V)
U mem⊆? V = map′ (l⊆→⊆ U V) (⊆→l⊆ U V) (U l⊆? V)