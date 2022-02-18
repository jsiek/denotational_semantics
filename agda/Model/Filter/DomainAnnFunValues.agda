
open import Function using (_∘_)
open import Data.Nat using (ℕ; suc ; zero; _+_; _≤′_; _<′_; _<_; _≤_;
    z≤n; s≤s; ≤′-refl; ≤′-step; _≟_) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ≤-step; ⊔-mono-≤;
         +-mono-≤; +-mono-≤-<; +-mono-<-≤; +-comm; +-assoc; n≤1+n;
         ≤-pred; m≤m+n; m≤n+m; ≤-reflexive; ≤′⇒≤; ≤⇒≤′; +-suc;
         mono-≤-distrib-⊔; ⊔-lub; ⊔-assoc; ⊔-comm)
open Data.Nat.Properties.≤-Reasoning using (begin_; _∎; step-≤)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_ ; []; _++_)
open import Data.Vec using (Vec; []; _∷_; length; head; tail; lookup; zipWith)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using (Pointwise; []; _∷_; head; tail; uncons)
open import Data.Vec.Relation.Unary.All using ([]; _∷_; All; head; tail; map)
open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)

module Model.Filter.DomainAnnFunValues where

open import Primitives
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

infixr 7 _⊢_↦_
infixl 6 _⊔_
infix 5 _◃_▹_  {- prounounced "split" -}
{- ◂ \tw and \tw2 ▹ (or \tw[right arrow key])  -}

data Value : Set where
  ω : Value
  ν : Value
  const : {B : Base} → (k : base-rep B) → Value
  _⊔_ : (u : Value) → (v : Value) → Value
  _⊢_↦_ : (FV : Value) → (v : Value) → (w : Value) → Value
  ⦅_,_⦆ : (d₁ : Value) → (d₂ : Value) → Value
  ∥_∥ : {n : ℕ} → (ds : Vec Value n) → Value
  left : (d : Value) → Value
  right : (d : Value) → Value

value_struct : ValueStruct
value_struct = record { Value = Value ; ⊥ = ω ; _↦_ = (λ x y → ω ⊢ x ↦ y) ; _⊔_ = _⊔_}

Atomic : Value → Set
Atomic-tup : ∀ {n} → Vec Value n → Set
Atomic-tup [] = ⊤
Atomic-tup (v ∷ vs) = Atomic v × Atomic-tup vs
Atomic ω = ⊤
Atomic ν = ⊤
Atomic (const k) = ⊤
Atomic ⦅ v , v₁ ⦆ = Atomic v × Atomic v₁
Atomic ∥ vs ∥ = Atomic-tup vs
Atomic (FV ⊢ v ↦ v₁) = Atomic v₁
Atomic (left d) = Atomic d
Atomic (right d) = Atomic d
Atomic (v ⊔ v₁) = Bot

atomic? : (v : Value) → Dec (Atomic v)
atomic-tup? : ∀ {n} → (vs : Vec Value n) → Dec (Atomic-tup vs)
atomic-tup? [] = yes tt
atomic-tup? (v ∷ vs) = (atomic? v) ∧dec (atomic-tup? vs)
atomic? ω = yes tt
atomic? ν = yes tt
atomic? (const k) = yes tt
atomic? ⦅ v , v₁ ⦆ = (atomic? v) ∧dec (atomic? v₁)
atomic? ∥ [] ∥ = yes tt
atomic? ∥ v ∷ vs ∥ = (atomic? v) ∧dec (atomic? ∥ vs ∥)
atomic? (FV ⊢ v ↦ v₁) = atomic? v₁
atomic? (v ⊔ u) = no (λ z → z)
atomic? (left d) = atomic? d
atomic? (right d) = atomic? d

data Flat : Value → Set where
  flat-atom : ∀ {v} → Atomic v → Flat v
  flat-⊔ : ∀ {u v} → Flat u → Flat v → Flat (u ⊔ v)

_⊔flat_ : Σ[ v ∈ Value ] Flat v → Σ[ w ∈ Value ] Flat w → Σ[ vw ∈ Value ] Flat vw
⟨ v , flatv ⟩ ⊔flat ⟨ w , flatw ⟩ = ⟨ v ⊔ w , flat-⊔ flatv flatw ⟩

data _◃_▹_ : (v₁ v v₂ : Value) → Set where
  
  split-⊔ : ∀ {u v}
        ----------------
        → u ◃ u ⊔ v ▹ v
  
  split-↦ : ∀ {FV u v v₁ v₂}
        →       v₁ ◃ v ▹ v₂
      -----------------------------
        → FV ⊢ u ↦ v₁ ◃ FV ⊢ u ↦ v ▹ FV ⊢ u ↦ v₂ 

  split-pair-fst : ∀ {u u₁ u₂ v}
        →           u₁ ◃ u ▹ u₂ 
      -------------------------------------
        → ⦅ u₁ , v ⦆ ◃ ⦅ u , v ⦆ ▹ ⦅ u₂ , v ⦆

  split-pair-snd : ∀ {u v v₁ v₂}
        → Atomic u
        →           v₁ ◃ v ▹ v₂
      --------------------------------------
        → ⦅ u , v₁ ⦆ ◃ ⦅ u , v ⦆ ▹ ⦅ u , v₂ ⦆

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
 
  ⊢'-ω : Proper ω

  ⊢'-ν : Proper ν

  ⊢'-const : ∀ {B} k → Proper (const {B} k)

  ⊢'-↦-å : ∀ {FV v₁ v₂}
            → (⊢'v₂ : Proper v₂)
            → (⊢'v₁ : Proper v₁)
            → (åv₂ :  Atomic v₂)
            → Proper (FV ⊢ v₁ ↦ v₂)

  ⊢'-pair-å : ∀ {v₁ v₂} 
            → (⊢'v₁ : Proper v₁) → (⊢'v₂ : Proper v₂) 
            → (åv₁ : Atomic v₁) → (åv₂ : Atomic v₂)
            → Proper ⦅ v₁ , v₂ ⦆
  
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
proper-left (⊢'-const k) = ⊢'-left-å (⊢'-const k) tt
proper-left (⊢'-↦-å Pd Pd₁ åv₂) = ⊢'-left-å (⊢'-↦-å Pd Pd₁ åv₂) åv₂
proper-left (⊢'-pair-å Pd Pd₁ åv₁ åv₂) = ⊢'-left-å (⊢'-pair-å Pd Pd₁ åv₁ åv₂) ⟨ åv₁ , åv₂ ⟩
proper-left ⊢'-nil = ⊢'-left-å ⊢'-nil tt
proper-left (⊢'-tup-å Pd Pd₁ åv åvs) = ⊢'-left-å (⊢'-tup-å Pd Pd₁ åv åvs) ⟨ åv , åvs ⟩
proper-left (⊢'-left-å Pd åv) = ⊢'-left-å (proper-left Pd) åv
proper-left (⊢'-right-å Pd åv) = ⊢'-left-å (⊢'-right-å Pd åv) åv
proper-left (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split (left vL) (left vR) (split-left split) (proper-left Pd) (proper-left Pd₁)

proper-right : ∀ {d} → Proper d → Proper (right d)
proper-right ⊢'-ω = ⊢'-right-å ⊢'-ω tt
proper-right ⊢'-ν = ⊢'-right-å ⊢'-ν tt
proper-right (⊢'-const k) = ⊢'-right-å (⊢'-const k) tt
proper-right (⊢'-↦-å Pd Pd₁ åv₂) = ⊢'-right-å (⊢'-↦-å Pd Pd₁ åv₂) åv₂
proper-right (⊢'-pair-å Pd Pd₁ åv₁ åv₂) = ⊢'-right-å (⊢'-pair-å Pd Pd₁ åv₁ åv₂) ⟨ åv₁ , åv₂ ⟩
proper-right ⊢'-nil = ⊢'-right-å ⊢'-nil tt
proper-right (⊢'-tup-å Pd Pd₁ åv åvs) = ⊢'-right-å (⊢'-tup-å Pd Pd₁ åv åvs) ⟨ åv , åvs ⟩
proper-right (⊢'-left-å Pd åv) = ⊢'-right-å (⊢'-left-å Pd åv) åv
proper-right (⊢'-right-å Pd åv) = ⊢'-right-å (proper-right Pd) åv
proper-right (⊢'-split vL vR split Pd Pd₁) = 
  ⊢'-split (right vL) (right vR) (split-right split) (proper-right Pd) (proper-right Pd₁)


proper-↦ : ∀ {FV u v} → Proper u → Proper v → Proper (FV ⊢ u ↦ v)
proper-↦ Pu ⊢'-ω = ⊢'-↦-å ⊢'-ω Pu tt
proper-↦ Pu ⊢'-ν = ⊢'-↦-å ⊢'-ν Pu tt
proper-↦ Pu (⊢'-const k) = ⊢'-↦-å (⊢'-const k) Pu tt
proper-↦ Pu (⊢'-↦-å Pv Pv₁ åv₂) = ⊢'-↦-å (proper-↦ Pv₁ Pv) Pu åv₂
proper-↦ Pu (⊢'-pair-å Pv Pv₁ åv₁ åv₂) = 
  ⊢'-↦-å (⊢'-pair-å Pv Pv₁ åv₁ åv₂) Pu ⟨ åv₁ , åv₂ ⟩
proper-↦ Pu ⊢'-nil = ⊢'-↦-å ⊢'-nil Pu tt
proper-↦ Pu (⊢'-tup-å Pv Pv₁ åv åvs) = 
  ⊢'-↦-å (⊢'-tup-å Pv Pv₁ åv åvs) Pu ⟨ åv , åvs ⟩
proper-↦ Pu (⊢'-left-å Pv åv) = ⊢'-↦-å (⊢'-left-å Pv åv) Pu åv
proper-↦ Pu (⊢'-right-å Pv åv) = ⊢'-↦-å (⊢'-right-å Pv åv) Pu åv
proper-↦ {FV} {u} Pu (⊢'-split vL vR split Pv Pv₁) = 
  ⊢'-split (FV ⊢ u ↦ vL) (FV ⊢ u ↦ vR) (split-↦ split) (proper-↦ Pu Pv) (proper-↦ Pu Pv₁)

proper-pair-atomic-1 : ∀ {u v} → Proper u → Proper v → Atomic u → Proper ⦅ u , v ⦆
proper-pair-atomic-1 Pu ⊢'-ω åu = ⊢'-pair-å Pu ⊢'-ω åu tt
proper-pair-atomic-1 Pu ⊢'-ν åu = ⊢'-pair-å Pu ⊢'-ν åu tt
proper-pair-atomic-1 Pu (⊢'-const k) åu = ⊢'-pair-å Pu (⊢'-const k) åu tt
proper-pair-atomic-1 Pu (⊢'-↦-å Pv Pv₁ åv₂) åu = ⊢'-pair-å Pu (⊢'-↦-å Pv Pv₁ åv₂) åu åv₂
proper-pair-atomic-1 Pu (⊢'-pair-å Pv Pv₁ åv₁ åv₂) åu = ⊢'-pair-å Pu (proper-pair-atomic-1 Pv Pv₁ åv₁) åu ⟨ åv₁ , åv₂ ⟩
proper-pair-atomic-1 Pu ⊢'-nil åu = ⊢'-pair-å Pu ⊢'-nil åu tt
proper-pair-atomic-1 Pu (⊢'-tup-å Pv Pv₁ åv åvs) åu = ⊢'-pair-å Pu (⊢'-tup-å Pv Pv₁ åv åvs) åu ⟨ åv , åvs ⟩
proper-pair-atomic-1 Pu (⊢'-left-å Pd åd) åu = ⊢'-pair-å Pu (⊢'-left-å Pd åd) åu åd
proper-pair-atomic-1 Pu (⊢'-right-å Pd åd) åu = ⊢'-pair-å Pu (⊢'-right-å Pd åd) åu åd
proper-pair-atomic-1 {u} Pu (⊢'-split vL vR split Pv Pv₁) åu = 
  ⊢'-split ⦅ u , vL ⦆ ⦅ u , vR ⦆ (split-pair-snd åu split)
     (proper-pair-atomic-1 Pu Pv åu) (proper-pair-atomic-1 Pu Pv₁ åu)

proper-pair : ∀ {u v} → Proper u → Proper v → Proper ⦅ u , v ⦆
proper-pair {u} {v} Pu Pv with atomic? u
... | yes åu = proper-pair-atomic-1 Pu Pv åu
... | no ¬åu with Pu
... | ⊢'-ω = ⊥-elim (¬åu tt)
... | ⊢'-ν = ⊥-elim (¬åu tt)
... | ⊢'-const k = ⊥-elim (¬åu tt)
... | ⊢'-↦-å Pu₁ Pu₂ åv₂ = ⊥-elim (¬åu åv₂)
... | ⊢'-pair-å Pu₁ Pu₂ åv₁ åv₂ = ⊥-elim (¬åu ⟨ åv₁ , åv₂ ⟩)
... | ⊢'-nil = ⊥-elim (¬åu tt)
... | ⊢'-tup-å Pu₁ Pu₂ åv åvs = ⊥-elim (¬åu ⟨ åv , åvs ⟩)
... | ⊢'-left-å Pd åd = ⊥-elim (¬åu åd)
... | ⊢'-right-å Pd åd = ⊥-elim (¬åu åd)
... | ⊢'-split vL vR split Pu₁ Pu₂ = 
  ⊢'-split ⦅ vL , v ⦆ ⦅ vR , v ⦆ (split-pair-fst split) 
           (proper-pair Pu₁ Pv) (proper-pair Pu₂ Pv) 


proper-tup-atomic-head : ∀ {n v vs} → Proper v → Proper (∥_∥ {n} vs) → Atomic v → Proper ∥ v ∷ vs ∥
proper-tup-atomic-head Pv ⊢'-nil åv = ⊢'-tup-å Pv ⊢'-nil åv tt
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
... | ⊢'-ω = ⊥-elim (¬åv tt)
... | ⊢'-ν = ⊥-elim (¬åv tt)
... | ⊢'-const k = ⊥-elim (¬åv tt)
... | ⊢'-↦-å Pu₁ Pu₂ åv₂ = ⊥-elim (¬åv åv₂)
... | ⊢'-pair-å Pu₁ Pu₂ åv₁ åv₂ = ⊥-elim (¬åv ⟨ åv₁ , åv₂ ⟩)
... | ⊢'-nil = ⊥-elim (¬åv tt)
... | ⊢'-tup-å Pu₁ Pu₂ åv' åvs = ⊥-elim (¬åv ⟨ åv' , åvs ⟩)
... | ⊢'-left-å Pd åd = ⊥-elim (¬åv åd)
... | ⊢'-right-å Pd åd = ⊥-elim (¬åv åd)
... | ⊢'-split vL vR split Pv₁ Pv₂ =  
   ⊢'-split ∥ vL ∷ vs ∥ ∥ vR ∷ vs ∥ (split-tup-head split) 
            (proper-tup Pv₁ Pvs) (proper-tup Pv₂ Pvs)


proper : ∀ v → Proper v
proper ω = ⊢'-ω
proper ν = ⊢'-ν
proper (const k) = ⊢'-const k
proper (v ⊔ v₁) = ⊢'-split v v₁ split-⊔ (proper v) (proper v₁)
proper (FV ⊢ v ↦ v₁) = proper-↦ (proper v) (proper v₁)
proper ⦅ v , v₁ ⦆ = proper-pair (proper v) (proper v₁)
proper ∥ [] ∥ = ⊢'-nil
proper ∥ v ∷ vs ∥ = proper-tup (proper v) (proper ∥ vs ∥)
proper (left d) = proper-left (proper d)
proper (right d) = proper-right (proper d)

unsplittable : ∀ v → Atomic v → ∀ {v₁ v₂} → ¬ (v₁ ◃ v ▹ v₂)
unsplittable (FV ⊢ v ↦ v₁) åv (split-↦ split) = unsplittable v₁ åv split
unsplittable ⦅ v , v₁ ⦆ åv (split-pair-fst split) = unsplittable v (proj₁ åv) split
unsplittable ⦅ v , v₁ ⦆ åv (split-pair-snd x split) = unsplittable v₁ (proj₂ åv) split
unsplittable ∥ v ∷ vs ∥ åv (split-tup-head split) = unsplittable v (proj₁ åv) split
unsplittable ∥ v ∷ vs ∥ åv (split-tup-tail x split) = unsplittable ∥ vs ∥ (proj₂ åv) split
unsplittable (left d) åv (split-left split) = unsplittable d åv split
unsplittable (right d) åv (split-right split) = unsplittable d åv split

depth : (v : Value) → ℕ
tup-depth : ∀ {n} (vs : Vec Value n) → ℕ
tup-depth {zero} [] = zero
tup-depth {suc n} (v ∷ vs) = max (depth v) (tup-depth vs)
depth ω = zero
depth ν = zero
depth (const k) = zero
depth (FV ⊢ v ↦ w) = suc (max (depth v) (depth w))
depth (v₁ ⊔ v₂) = max (depth v₁) (depth v₂)
depth ⦅ v₁ , v₂ ⦆ = suc (max (depth v₁) (depth v₂))
depth ∥ vs ∥ = suc (tup-depth vs)
depth (left d) = suc (depth d)
depth (right d) = suc (depth d)

size : (v : Value) → ℕ
tup-size : ∀ {n} (vs : Vec Value n) → ℕ
tup-size {zero} [] = zero
tup-size {suc n} (v ∷ vs) = suc (size v + tup-size vs)
size ω = zero
size ν = zero
size (const k) = zero
size (FV ⊢ v ↦ w) = suc (size v + size w)
size (v₁ ⊔ v₂) = suc (size v₁ + size v₂)
size ⦅ v₁ , v₂ ⦆ = suc (size v₁ + size v₂)
size (∥_∥ {n} vs) = suc (tup-size vs)
size (left d) = suc (size d)
size (right d) = suc (size d)

