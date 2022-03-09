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
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
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
open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Product using (_×-dec_)

module Model.Filter.DomainISWIMValues where

open import Primitives
open import SetsAsPredicates
open import Model.Filter.DomainUtil


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
infix 5 _◃_▹_  {- prounounced "split" -}
{- ◂ \tw and \tw2 ▹ (or \tw[right arrow key])  -}


{- Went with half-pair values instead of using ⦅ u , ω ⦆ and ⦅ ω , v ⦆ atoms
  just because breaking ⦅ u , v ⦆ into those two cases and a default non-atomic case
  turned out to be a pain -}
data Value : Set where
  ⊥ : Value {- represents no info -}
  ω : Value {- represents an error -}
  ν : Value
  const : {B : Base} → (k : base-rep B) → Value
  _⊔_ : (u : Value) → (v : Value) → Value
  _↦_ : (v : Value) → (w : Value) → Value
  ⦅_∣ : (u : Value) → Value
  ∣_⦆ : (v : Value) → Value
  ∥_∥ : {n : ℕ} → (ds : Vec Value n) → Value
  left : (d : Value) → Value
  right : (d : Value) → Value

value_struct : ValueStruct
value_struct = record { Value = Value ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_}


{- --- Splitting: Atomic and Proper values ---------------------------------- -}

Atomic : Value → Set
Atomic-tup : ∀ {n} → Vec Value n → Set
Atomic-tup [] = ⊤
Atomic-tup (v ∷ vs) = Atomic v × Atomic-tup vs
Atomic ω = ⊤
Atomic ⊥ = ⊤
Atomic ν = ⊤
Atomic (const k) = ⊤
Atomic ⦅ u ∣ = Atomic u
Atomic ∣ v ⦆ = Atomic v
Atomic ∥ vs ∥ = Atomic-tup vs
Atomic (v ↦ v₁) = Atomic v₁
Atomic (left d) = Atomic d
Atomic (right d) = Atomic d
Atomic (v ⊔ v₁) = Bot

atomic? : (v : Value) → Dec (Atomic v)
atomic-tup? : ∀ {n} → (vs : Vec Value n) → Dec (Atomic-tup vs)
atomic-tup? [] = yes tt
atomic-tup? (v ∷ vs) = (atomic? v) ∧dec (atomic-tup? vs)
atomic? ⊥ = yes tt
atomic? ω = yes tt
atomic? ν = yes tt
atomic? (const k) = yes tt
atomic? ⦅ u ∣ = atomic? u
atomic? ∣ v ⦆ = atomic? v
atomic? ∥ [] ∥ = yes tt
atomic? ∥ v ∷ vs ∥ = (atomic? v) ∧dec (atomic? ∥ vs ∥)
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

  split-fst : ∀ {u u₁ u₂}
        →           u₁ ◃ u ▹ u₂ 
      -------------------------------------
        → ⦅ u₁ ∣ ◃ ⦅ u ∣ ▹ ⦅ u₂ ∣

  split-snd : ∀ {v v₁ v₂}
        →           v₁ ◃ v ▹ v₂
      --------------------------------------
        → ∣ v₁ ⦆ ◃ ∣ v ⦆ ▹ ∣ v₂ ⦆

  split-tup-head : ∀ {n v v₁ v₂} {vs : Vec Value n}
        →                v₁ ◃ v ▹ v₂ 
      --------------------------------------------------
        → ∥ (v₁ ∷ vs) ∥ ◃ ∥ v ∷ vs ∥ ▹ ∥ (v₂ ∷ vs) ∥

  split-tup-tail : ∀ {n v} {vs vs₁ vs₂ : Vec Value n}
        → Atomic v
        →       (∥ vs₁ ∥) ◃ ∥ vs ∥ ▹ (∥ vs₂ ∥) 
      --------------------------------------------------
        → ∥ v ∷ vs₁ ∥ ◃ ∥ v ∷ vs ∥ ▹ ∥ (v ∷ vs₂) ∥

  split-left : ∀ {d d₁ d₂}
        → d₁ ◃ d ▹ d₂
      ----------------------------------------------
        → left d₁ ◃ left d ▹ left d₂

  split-right : ∀ {d d₁ d₂}
        → d₁ ◃ d ▹ d₂
      ----------------------------------------------
        → right d₁ ◃ right d ▹ right d₂


data Proper : Value → Set where
 
  ⊢'-⊥ : Proper ⊥

  ⊢'-ω : Proper ω

  ⊢'-ν : Proper ν

  ⊢'-const : ∀ {B} k → Proper (const {B} k)

  ⊢'-↦-å : ∀ {V w}
            → (⊢'V : Proper V)
            → (⊢'w : Proper w)
            → (åw :  Atomic w)
            → Proper (V ↦ w)

  ⊢'-fst-å : ∀ {v₁} 
            → (⊢'v₁ : Proper v₁)
            → (åv₁ : Atomic v₁)
            → Proper ⦅ v₁ ∣
  
  ⊢'-snd-å : ∀ {v₂} 
            → (⊢'v₂ : Proper v₂) 
            → (åv₂ : Atomic v₂)
            → Proper ∣ v₂ ⦆
  
  ⊢'-nil : Proper ∥ [] ∥

  ⊢'-tup-å : ∀ {n v vs}
           → (⊢'v : Proper v)
           → (⊢'vs : Proper (∥_∥ {n} vs))
           → (åv : Atomic v)
           → (åvs : Atomic ∥ vs ∥)
           → Proper ∥ v ∷ vs ∥
  
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
proper-left ⊢'-⊥ = ⊢'-left-å ⊢'-⊥ tt
proper-left (⊢'-const k) = ⊢'-left-å (⊢'-const k) tt
proper-left (⊢'-↦-å Pd₁ Pd₂ åw) = ⊢'-left-å (⊢'-↦-å Pd₁ Pd₂ åw) åw 
proper-left (⊢'-fst-å Pd åv₁) = ⊢'-left-å (⊢'-fst-å Pd åv₁) åv₁
proper-left (⊢'-snd-å Pd åv₂) = ⊢'-left-å (⊢'-snd-å Pd åv₂) åv₂
proper-left ⊢'-nil = ⊢'-left-å ⊢'-nil tt
proper-left (⊢'-tup-å Pd Pd₁ åv åvs) = ⊢'-left-å (⊢'-tup-å Pd Pd₁ åv åvs) ⟨ åv , åvs ⟩
proper-left (⊢'-left-å Pd åv) = ⊢'-left-å (proper-left Pd) åv
proper-left (⊢'-right-å Pd åv) = ⊢'-left-å (⊢'-right-å Pd åv) åv
proper-left (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split (left vL) (left vR) (split-left split) (proper-left Pd) (proper-left Pd₁)



proper-right : ∀ {d} → Proper d → Proper (right d)
proper-right ⊢'-⊥ = ⊢'-right-å ⊢'-⊥ tt
proper-right ⊢'-ω = ⊢'-right-å ⊢'-ω tt
proper-right ⊢'-ν = ⊢'-right-å ⊢'-ν tt
proper-right (⊢'-const k) = ⊢'-right-å (⊢'-const k) tt
proper-right (⊢'-↦-å Pd₁ Pd₂ åw) =
   ⊢'-right-å (⊢'-↦-å Pd₁ Pd₂ åw) åw
proper-right (⊢'-fst-å Pd åv₁) = ⊢'-right-å (⊢'-fst-å Pd åv₁) åv₁
proper-right (⊢'-snd-å Pd åv₂) = ⊢'-right-å (⊢'-snd-å Pd åv₂) åv₂
proper-right ⊢'-nil = ⊢'-right-å ⊢'-nil tt
proper-right (⊢'-tup-å Pd Pd₁ åv åvs) = ⊢'-right-å (⊢'-tup-å Pd Pd₁ åv åvs) ⟨ åv , åvs ⟩
proper-right (⊢'-left-å Pd åv) = ⊢'-right-å (⊢'-left-å Pd åv) åv
proper-right (⊢'-right-å Pd åv) = ⊢'-right-å (proper-right Pd) åv
proper-right (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split (right vL) (right vR) (split-right split) (proper-right Pd) (proper-right Pd₁)

proper-↦ : ∀ {u v} → Proper u → Proper v → Proper (u ↦ v)
proper-↦ {u}{v} Pu Pv with atomic? v
... | yes åv = ⊢'-↦-å Pu Pv åv
... | no ¬åv with Pv
... | ⊢'-⊥ = ⊥-elim (¬åv tt)
... | ⊢'-ω = ⊥-elim (¬åv tt)
... | ⊢'-ν = ⊥-elim (¬åv tt)
... | ⊢'-const k = ⊥-elim (¬åv tt)
... | ⊢'-↦-å Pv₁ Pv₂ åw = ⊥-elim (¬åv åw)
... | ⊢'-fst-å Pv₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-snd-å Pv₁ åv₂ = ⊥-elim (¬åv åv₂)
... | ⊢'-nil = ⊥-elim (¬åv tt)
... | ⊢'-tup-å Pv₁ Pv₂ åv åvs = ⊥-elim (¬åv ⟨ åv , åvs ⟩)
... | ⊢'-left-å Pv₁ åv = ⊥-elim (¬åv åv)
... | ⊢'-right-å Pv₁ åv = ⊥-elim (¬åv åv)
... | ⊢'-split vL vR split Pv₁ Pv₂ = 
   ⊢'-split (u ↦ vL) (u ↦ vR) (split-↦ split) 
            (proper-↦ Pu Pv₁) (proper-↦ Pu Pv₂)

proper-fst : ∀ {d} → Proper d → Proper ⦅ d ∣
proper-fst ⊢'-⊥ = ⊢'-fst-å ⊢'-⊥ tt
proper-fst ⊢'-ω = ⊢'-fst-å ⊢'-ω tt
proper-fst ⊢'-ν = ⊢'-fst-å ⊢'-ν tt
proper-fst (⊢'-const k) = ⊢'-fst-å (⊢'-const k) tt
proper-fst (⊢'-↦-å Pd₁ Pd₂ åw) = ⊢'-fst-å (⊢'-↦-å Pd₁ Pd₂ åw) åw
proper-fst (⊢'-fst-å Pd åv₁) = ⊢'-fst-å (proper-fst Pd) åv₁
proper-fst (⊢'-snd-å Pd åv₂) = ⊢'-fst-å (⊢'-snd-å Pd åv₂) åv₂
proper-fst ⊢'-nil = ⊢'-fst-å ⊢'-nil tt
proper-fst (⊢'-tup-å Pd Pd₁ åv åvs) = ⊢'-fst-å (⊢'-tup-å Pd Pd₁ åv åvs) ⟨ åv , åvs ⟩
proper-fst (⊢'-left-å Pd åv) = ⊢'-fst-å (⊢'-left-å Pd åv) åv
proper-fst (⊢'-right-å Pd åv) = ⊢'-fst-å (⊢'-right-å Pd åv) åv
proper-fst (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split ⦅ vL ∣ ⦅ vR ∣ (split-fst split) (proper-fst Pd) (proper-fst Pd₁)


proper-snd : ∀ {d} → Proper d → Proper ∣ d ⦆
proper-snd ⊢'-⊥ = ⊢'-snd-å ⊢'-⊥ tt
proper-snd ⊢'-ω = ⊢'-snd-å ⊢'-ω tt
proper-snd ⊢'-ν = ⊢'-snd-å ⊢'-ν tt
proper-snd (⊢'-const k) = ⊢'-snd-å (⊢'-const k) tt
proper-snd (⊢'-↦-å Pd₁ Pd₂ åw) = ⊢'-snd-å (⊢'-↦-å Pd₁ Pd₂ åw) åw
proper-snd (⊢'-fst-å Pd åv₁) = ⊢'-snd-å (⊢'-fst-å Pd åv₁) åv₁
proper-snd (⊢'-snd-å Pd åv₂) = ⊢'-snd-å (proper-snd Pd) åv₂
proper-snd ⊢'-nil = ⊢'-snd-å ⊢'-nil tt
proper-snd (⊢'-tup-å Pd Pd₁ åv åvs) = ⊢'-snd-å (⊢'-tup-å Pd Pd₁ åv åvs) ⟨ åv , åvs ⟩
proper-snd (⊢'-left-å Pd åv) = ⊢'-snd-å (⊢'-left-å Pd åv) åv
proper-snd (⊢'-right-å Pd åv) = ⊢'-snd-å (⊢'-right-å Pd åv) åv
proper-snd (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split ∣ vL ⦆ ∣ vR ⦆ (split-snd split) (proper-snd Pd) (proper-snd Pd₁)

proper-tup-atomic-head : ∀ {n v vs} → Proper v → Proper (∥_∥ {n} vs) → Atomic v → Proper ∥ v ∷ vs ∥
proper-tup-atomic-head Pd ⊢'-nil åv = ⊢'-tup-å Pd ⊢'-nil åv tt
proper-tup-atomic-head Pv (⊢'-tup-å Pvs Pvs₁ åv₁ åvs) åv = 
  ⊢'-tup-å Pv (proper-tup-atomic-head Pvs Pvs₁ åv₁) åv ⟨ åv₁ , åvs ⟩
proper-tup-atomic-head {.(suc _)} {v} {v' ∷ vs} Pv (⊢'-split ∥ vL ∷ vs ∥ ∥ vR ∷ vs ∥ (split-tup-head split) Pvs Pvs₁) åv = 
  ⊢'-split ∥ v ∷ vL ∷ vs ∥ ∥ v ∷ vR ∷ vs ∥ (split-tup-tail åv (split-tup-head split)) 
          (proper-tup-atomic-head Pv Pvs åv) (proper-tup-atomic-head Pv Pvs₁ åv)
proper-tup-atomic-head {.(suc _)} {v} {v' ∷ vs} Pv (⊢'-split ∥ v' ∷ vsL ∥ ∥ v' ∷ vsR ∥ (split-tup-tail x split) Pvs Pvs₁) åv = 
  ⊢'-split ∥ v ∷ v' ∷ vsL ∥ ∥ v ∷ v' ∷ vsR ∥ (split-tup-tail åv (split-tup-tail x split)) 
          (proper-tup-atomic-head Pv Pvs åv) (proper-tup-atomic-head Pv Pvs₁ åv)


proper-tup : ∀ {n v vs} → Proper v → Proper (∥_∥ {n} vs) → Proper ∥ v ∷ vs ∥
proper-tup {n}{v}{vs} Pv Pvs with atomic? v
... | yes åv = proper-tup-atomic-head Pv Pvs åv
... | no ¬åv with Pv
... | ⊢'-⊥ = ⊥-elim (¬åv tt)
... | ⊢'-ω = ⊥-elim (¬åv tt)
... | ⊢'-ν = ⊥-elim (¬åv tt)
... | ⊢'-const k = ⊥-elim (¬åv tt)
... | ⊢'-↦-å Pu₁ Pu₂ åv₂ = ⊥-elim (¬åv åv₂)
... | ⊢'-fst-å Pu₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-snd-å Pu₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-nil = ⊥-elim (¬åv tt)
... | ⊢'-tup-å Pu₁ Pu₂ åv' åvs = ⊥-elim (¬åv ⟨ åv' , åvs ⟩)
... | ⊢'-left-å Pd åd = ⊥-elim (¬åv åd)
... | ⊢'-right-å Pd åd = ⊥-elim (¬åv åd)
... | ⊢'-split vL vR split Pv₁ Pv₂ =  
   ⊢'-split ∥ vL ∷ vs ∥ ∥ vR ∷ vs ∥ (split-tup-head split) 
            (proper-tup Pv₁ Pvs) (proper-tup Pv₂ Pvs)

proper : ∀ v → Proper v
proper ⊥ = ⊢'-⊥
proper ω = ⊢'-ω
proper ν = ⊢'-ν
proper (const k) = ⊢'-const k
proper (v ⊔ v₁) = ⊢'-split v v₁ split-⊔ (proper v) (proper v₁)
proper (v ↦ v₁) = proper-↦ (proper v) (proper v₁)
proper ⦅ u ∣ = proper-fst (proper u)
proper ∣ v ⦆ = proper-snd (proper v)
proper ∥ [] ∥ = ⊢'-nil
proper ∥ v ∷ vs ∥ = proper-tup (proper v) (proper ∥ vs ∥)
proper (left d) = proper-left (proper d)
proper (right d) = proper-right (proper d)


unsplittable : ∀ v → Atomic v → ∀ {v₁ v₂} → ¬ (v₁ ◃ v ▹ v₂)
unsplittable (v ↦ v₁) åv (split-↦ split) = unsplittable v₁ åv split
unsplittable ⦅ v ∣ åv (split-fst split) = unsplittable v åv split
unsplittable ∣ v ⦆ åv (split-snd split) = unsplittable v åv split
unsplittable ∥ v ∷ vs ∥ åv (split-tup-head split) = unsplittable v (proj₁ åv) split
unsplittable ∥ v ∷ vs ∥ åv (split-tup-tail x split) = unsplittable ∥ vs ∥ (proj₂ åv) split
unsplittable (left d) åv (split-left split) = unsplittable d åv split
unsplittable (right d) åv (split-right split) = unsplittable d åv split

¬å⇒split : ∀ v → ¬ (Atomic v) → Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] v₁ ◃ v ▹ v₂
¬å⇒split v ¬åv with (proper v)
... | ⊢'-⊥ = ⊥-elim (¬åv tt)
... | ⊢'-ω = ⊥-elim (¬åv tt)
... | ⊢'-ν = ⊥-elim (¬åv tt)
... | ⊢'-const k = ⊥-elim (¬åv tt)
... | ⊢'-↦-å Pv Pv₁ åv₂ = ⊥-elim (¬åv åv₂)
... | ⊢'-fst-å Pu₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-snd-å Pu₁ åv₁ = ⊥-elim (¬åv åv₁)
... | ⊢'-nil = ⊥-elim (¬åv tt)
... | ⊢'-tup-å Pv Pv₁ åv åvs = ⊥-elim (¬åv ⟨ åv , åvs ⟩)
... | ⊢'-left-å Pv åv = ⊥-elim (¬åv åv)
... | ⊢'-right-å Pv åv = ⊥-elim (¬åv åv)
... | ⊢'-split vL vR split Pv Pv₁ = ⟨ vL , ⟨ vR , split ⟩ ⟩

{- Size/Depth -----------------------------------------------------------------}

depth : (v : Value) → ℕ
tup-depth : ∀ {n} (vs : Vec Value n) → ℕ
tup-depth {zero} [] = zero
tup-depth {suc n} (v ∷ vs) = max (depth v) (tup-depth vs)
depth ω = zero
depth ⊥ = zero
depth ν = zero
depth (const k) = zero
depth ( v ↦ w) = suc (max (depth v) (depth w))
depth (v₁ ⊔ v₂) = max (depth v₁) (depth v₂)
depth ⦅ v ∣ = suc (depth v)
depth ∣ v ⦆ = suc (depth v)
depth ∥ vs ∥ = suc (tup-depth vs)
depth (left d) = suc (depth d)
depth (right d) = suc (depth d)

size : (v : Value) → ℕ
tup-size : ∀ {n} (vs : Vec Value n) → ℕ
tup-size {zero} [] = zero
tup-size {suc n} (v ∷ vs) = suc (size v + tup-size vs)
size ω = zero
size ⊥ = zero
size ν = zero
size (const k) = zero
size ( v ↦ w) = suc (size v + size w)
size (v₁ ⊔ v₂) = suc (size v₁ + size v₂)
size ⦅ u ∣ = suc (size u)
size ∣ v ⦆ = suc (size v)
size (∥_∥ {n} vs) = suc (tup-size vs)
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

tup-inj-easy : ∀ {n ds ds'} → ∥_∥ {n} ds ≡ ∥_∥ {n} ds' → ds ≡ ds'
tup-inj-easy refl = refl

tup-inj : ∀ {n n' ds ds'} → ∥_∥ {n} ds ≡ ∥_∥ {n'} ds' → 
   Σ[ n≡n' ∈ n ≡ n' ] (subst (Vec Value) n≡n' ds) ≡ ds'
tup-inj refl = ⟨ refl , refl ⟩

left-inj : ∀ {v v'} → (left v) ≡ left v' → v ≡ v'
left-inj refl = refl

right-inj : ∀ {v v'} → (right v) ≡ right v' → v ≡ v'
right-inj refl = refl

fst-inj : ∀ {v v'} → ⦅ v ∣ ≡ ⦅ v' ∣ → v ≡ v'
fst-inj refl = refl

snd-inj : ∀ {v v'} → ∣ v ⦆ ≡ ∣ v' ⦆ → v ≡ v'
snd-inj refl = refl

↦-inj-uncurried : ∀ {V V' w w'} →  V ↦ w ≡  V' ↦ w'
      → ⟨ V , w ⟩ ≡ ⟨ V' , w' ⟩
↦-inj-uncurried refl = refl

⊔-inj : ∀ {d₁ d₂ d₁' d₂'} → d₁ ⊔ d₂ ≡ d₁' ⊔ d₂' → d₁ ≡ d₁' × d₂ ≡ d₂'
⊔-inj refl = ⟨ refl , refl ⟩

_d≟_ : (d₁ : Value) → (d₂ : Value) → Dec (d₁ ≡ d₂)
_ds≟_ : ∀ {n} → (ds₁ ds₂ : Vec Value n) → Dec (ds₁ ≡ ds₂)
const {B} k d≟ const {B'} k₁ with base-eq? B B'
... | no neq = no λ z → neq (const-inj-base z)
... | yes refl = map′ (cong (const {B})) const-inj (base-rep-eq? k k₁)
const k d≟ ν = no (λ ())
const k d≟ (V ↦ w) = no (λ ())
const k d≟ ω = no (λ ())
const k d≟ ∥ ds ∥ = no (λ ())
const k d≟ (left v₁) = no (λ ())
const k d≟ (right v₁) = no (λ ())
const k d≟ (u ⊔ v) = no (λ ())
const k d≟ ⦅ v ∣ = no (λ ())
const k d≟ ∣ v ⦆ = no (λ ())
(V ↦ w) d≟ const k = no (λ ())
(V ↦ w) d≟ ( V' ↦ w') = 
  map′ (cong (λ z → proj₁ z ↦ (proj₂ z)))
        ↦-inj-uncurried 
        (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((V d≟ V') ×-dec (w d≟ w')))
(V ↦ w) d≟ ν = no (λ ())
(V ↦ w) d≟ ω = no (λ ())
(V ↦ w) d≟ ∥ ds ∥ = no (λ ())
(V ↦ w) d≟ (left v₁) = no (λ ())
(V ↦ w) d≟ (right v₁) = no (λ ())
(V ↦ w) d≟ (u ⊔ v) = no (λ ())
(u₁ ↦ u₂) d≟ ⦅ v ∣ = no (λ ())
(u₁ ↦ u₂) d≟ ∣ v ⦆ = no (λ ())
ν d≟ const k = no (λ ())
ν d≟ (V ↦ d₃) = no (λ ())
ν d≟ ν = yes refl
ν d≟ ω = no (λ ())
ν d≟ ∥ ds ∥ = no (λ ())
ν d≟ (left v) = no (λ ())
ν d≟ (right v) = no (λ ())
ν d≟ (u ⊔ v) = no (λ ())
ν d≟ ⦅ v ∣ = no (λ ())
ν d≟ ∣ v ⦆ = no (λ ())
ω d≟ const k = no (λ ())
ω d≟ ( V ↦ d₃) = no (λ ())
ω d≟ ν = no (λ ())
ω d≟ ω = yes refl
ω d≟ ∥ ds ∥ = no (λ ())
ω d≟ (left v) = no (λ ())
ω d≟  (right v) = no (λ ())
ω d≟ (u ⊔ v) = no (λ ())
ω d≟ ⦅ v ∣ = no (λ ())
ω d≟ ∣ v ⦆ = no (λ ())
∥ ds ∥ d≟ const k = no (λ ())
∥ ds ∥ d≟ (V ↦ d₃) = no (λ ())
∥ ds ∥ d≟ ν = no (λ ())
∥ ds ∥ d≟ ω = no (λ ())
∥_∥ {n} ds d≟ ∥_∥ {n'} ds' with n ≟ n'
... | no neq = no λ z → neq (proj₁ (tup-inj z))
... | yes refl = map′ (cong ∥_∥) tup-inj-easy (ds ds≟ ds')
∥ ds ∥ d≟ (left v) = no (λ ())
∥ ds ∥ d≟  (right v) = no (λ ())
∥ ds ∥ d≟ (u ⊔ v) = no (λ ())
∥ ds ∥ d≟ ⦅ v ∣ = no (λ ())
∥ ds ∥ d≟ ∣ v ⦆ = no (λ ())
(left v) d≟ const k = no (λ ())
(left v) d≟ (V₁ ↦ d₃) = no (λ ())
(left v) d≟ ν = no (λ ())
(left v) d≟ ω = no (λ ())
(left v) d≟ ∥ ds ∥ = no (λ ())
(left v) d≟ (left v₁) = map′ (cong left) left-inj (v d≟ v₁)
(left v) d≟ (right v₁) = no (λ ())
(left v) d≟ (u ⊔ v₁) = no (λ ())
left u d≟ ⦅ v ∣ = no (λ ())
left u d≟ ∣ v ⦆ = no (λ ())
(right v) d≟ const k = no (λ ())
(right v) d≟ (V₁ ↦ d₃) = no (λ ())
(right v) d≟ ν = no (λ ())
(right v) d≟ ω = no (λ ())
(right v) d≟ ∥ ds ∥ = no (λ ())
(right v) d≟ (left v₁) = no (λ ())
(right v) d≟ (right v₁) = map′ (cong right) right-inj (v d≟ v₁)
(right v) d≟ (u ⊔ v₁) = no (λ ())
right u d≟ ⦅ v ∣ = no (λ ())
right u d≟ ∣ v ⦆ = no (λ ())
(u ⊔ v) d≟ ω = no (λ ())
(u ⊔ v) d≟ ν = no (λ ())
(u ⊔ v) d≟ const k = no (λ ())
(u ⊔ v) d≟ (d ⊔ d₁) = map′ (uncurry (cong₂ _⊔_)) ⊔-inj ((u d≟ d) ×-dec (v d≟ d₁))
(u ⊔ v) d≟ (d₁ ↦ d₂) = no (λ ())
(u ⊔ v) d≟ ∥ ds ∥ = no (λ ())
(u ⊔ v) d≟ left d = no (λ ())
(u ⊔ v) d≟ right d = no (λ ())
(u ⊔ u₁) d≟ ⦅ v ∣ = no (λ ())
(u ⊔ u₁) d≟ ∣ v ⦆ = no (λ ())
⦅ u ∣ d≟ ω = no (λ ())
⦅ u ∣ d≟ ν = no (λ ())
⦅ u ∣ d≟ const k = no (λ ())
⦅ u ∣ d≟ (v ⊔ v₁) = no (λ ())
⦅ u ∣ d≟ (v₁ ↦ v₂) = no (λ ())
⦅ u ∣ d≟ ⦅ v ∣ = map′ (cong ⦅_∣) fst-inj (u d≟ v)
⦅ u ∣ d≟ ∣ v ⦆ = no (λ ())
⦅ u ∣ d≟ ∥ ds ∥ = no (λ ())
⦅ u ∣ d≟ left v = no (λ ())
⦅ u ∣ d≟ right v = no (λ ())
∣ u ⦆ d≟ ω = no (λ ())
∣ u ⦆ d≟ ν = no (λ ())
∣ u ⦆ d≟ const k = no (λ ())
∣ u ⦆ d≟ (v ⊔ v₁) = no (λ ())
∣ u ⦆ d≟ (v₁ ↦ v₂) = no (λ ())
∣ u ⦆ d≟ ⦅ v ∣ = no (λ ())
∣ u ⦆ d≟ ∣ v ⦆ = map′ (cong ∣_⦆) snd-inj (u d≟ v)
∣ u ⦆ d≟ ∥ ds ∥ = no (λ ())
∣ u ⦆ d≟ left v = no (λ ())
∣ u ⦆ d≟ right v = no (λ ())
⊥ d≟ ⊥ = yes refl
⊥ d≟ ω = no (λ ())
⊥ d≟ ν = no (λ ())
⊥ d≟ const k = no (λ ())
⊥ d≟ (v ⊔ v₁) = no (λ ())
⊥ d≟ (v ↦ v₁) = no (λ ())
⊥ d≟ ⦅ v ∣ = no (λ ())
⊥ d≟ ∣ v ⦆ = no (λ ())
⊥ d≟ ∥ ds ∥ = no (λ ())
⊥ d≟ left v = no (λ ())
⊥ d≟ right v = no (λ ())
ω d≟ ⊥ = no (λ ())
ν d≟ ⊥ = no (λ ())
const k d≟ ⊥ = no (λ ())
(u ⊔ u₁) d≟ ⊥ = no (λ ())
(u ↦ u₁) d≟ ⊥ = no (λ ())
⦅ u ∣ d≟ ⊥ = no (λ ())
∣ u ⦆ d≟ ⊥ = no (λ ())
∥ ds ∥ d≟ ⊥ = no (λ ())
left u d≟ ⊥ = no (λ ())
right u d≟ ⊥ = no (λ ())
[] ds≟ [] = yes refl
(d ∷ ds) ds≟ (d' ∷ ds') = map′ (uncurry (cong₂ _∷_)) ∷-injective ((d d≟ d') ×-dec (ds ds≟ ds'))

_l⊆?_ : ∀ (U V : List Value) → Dec (U l⊆ V)
U l⊆? V = _d≟_ ⊢ U l⊆? V

_mem⊆?_ : ∀ (U V : List Value) → Dec (mem U ⊆ mem V)
U mem⊆? V = map′ (l⊆→⊆ U V) (⊆→l⊆ U V) (U l⊆? V)