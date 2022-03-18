{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat using (ℕ; suc ; zero; _+_; _≤′_; _<′_; _<_; _≤_;
    z≤n; s≤s; ≤′-refl; ≤′-step; _≟_) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ≤-step; ⊔-mono-≤;
         +-mono-≤; +-mono-≤-<; +-mono-<-≤; +-comm; +-assoc; n≤1+n;
         ≤-pred; m≤m+n; m≤n+m; ≤-reflexive; ≤′⇒≤; ≤⇒≤′; +-suc)
open Data.Nat.Properties.≤-Reasoning using (begin_; _∎; step-≤)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.List using (List; _∷_ ; [])
open import Data.Vec using (Vec; []; _∷_; length; head; tail)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_; head; tail)
open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)

module Model.Filter.DomainAnnFunConsistent where

  open import Primitives
  open import Model.Filter.DomainUtil
  open import Model.Filter.DomainAnnFunValues
  open import Model.Filter.DomainAnnFunOrdering


  {-
  Consistency
  -}

  infix 4 _~_

  {-
  question, should (FV ⊢ν) be consistent with functions?
  ... it would allow unioning... but that's something that shouldn't appear in our semantics
  -}
  _~_ : Value → Value → Set
  ω ~ v = True
  (u₁ ⊔ u₂) ~ v = u₁ ~ v × u₂ ~ v
  (FV ⊢ν) ~ v₁ ⊔ v₂ = (FV ⊢ν) ~ v₁ × (FV ⊢ν) ~ v₂
  const x ~ v₁ ⊔ v₂ = const x ~ v₁ × const x ~ v₂
  FV ⊢ u ↦ u₁ ~ v₁ ⊔ v₂ = FV ⊢ u ↦ u₁ ~ v₁ × FV ⊢ u ↦ u₁ ~ v₂
  ⦅ u ∣ ~ v₁ ⊔ v₂ = ⦅ u ∣ ~ v₁ × ⦅ u ∣ ~ v₂
  ∣ u₁ ⦆ ~ v₁ ⊔ v₂ = ∣ u₁ ⦆ ~ v₁ × ∣ u₁ ⦆ ~ v₂
  (tup[ i ] d) ~ v₁ ⊔ v₂ = (tup[ i ] d) ~ v₁ × (tup[ i ] d) ~ v₂
  left u ~ v ⊔ v₁ = left u ~ v × left u ~ v₁
  right u ~ v ⊔ v₁ = right u ~ v × right u ~ v₁
  (FV ⊢ν) ~ ω = True
  (FV ⊢ν) ~ (FV' ⊢ν) = True
  (FV ⊢ν) ~ const x = False
  (FV ⊢ν) ~ FV' ⊢ v ↦ v₁ = True
  (FV ⊢ν) ~ ⦅ v ∣ = False
  (FV ⊢ν) ~ ∣ v₁ ⦆ = False
  (FV ⊢ν) ~ (tup[ i ] d) = False
  (FV ⊢ν) ~ left v = False
  (FV ⊢ν) ~ right v = False
  const {B} k ~ ω = True
  const {B} k ~ (FV ⊢ν) = False
  const {B} k ~ const {B′} k′
    = Σ[ B≡ ∈ B ≡ B′ ] (subst base-rep B≡ k) ≡ k′ 
  const {B} k ~ ⦅ v₁ ∣ = False
  const {B} k ~ ∣ v₂ ⦆ = False
  const {B} k ~ (tup[ i ] d) = False
  const {B} k ~ FV ⊢ v ↦ w = False
  const k ~ left v = False
  const k ~ right v = False
  ⦅ u ∣ ~ ω = True
  ⦅ u ∣ ~ (v ⊢ν) = False
  ⦅ u ∣ ~ const k = False
  ⦅ u ∣ ~ v ⊢ v₁ ↦ v₂ = False
  ⦅ u ∣ ~ ⦅ v ∣ = u ~ v
  ⦅ u ∣ ~ ∣ v ⦆ = True
  ⦅ u ∣ ~ (tup[ i ] d) = False
  ⦅ u ∣ ~ left v = False
  ⦅ u ∣ ~ right v = False
  ∣ u ⦆ ~ ω = True
  ∣ u ⦆ ~ (v ⊢ν) = False
  ∣ u ⦆ ~ const k = False
  ∣ u ⦆ ~ v ⊢ v₁ ↦ v₂ = False
  ∣ u ⦆ ~ ⦅ v ∣ = True
  ∣ u ⦆ ~ ∣ v ⦆ = u ~ v
  ∣ u ⦆ ~ (tup[ i ] d) = False
  ∣ u ⦆ ~ left v = False
  ∣ u ⦆ ~ right v = False
  (tup[ i ] d) ~ ω = True
  (tup[ i ] d) ~ (FV ⊢ν) = False
  (tup[ i ] d) ~ const k = False
  (tup[ i ] d) ~ ⦅ v ∣ = False
  (tup[ i ] d) ~ ∣ v₁ ⦆ = False
  (tup[_]_ {n} i d) ~ (tup[_]_ {n'} i' d') 
    = Σ[ n≡ ∈ n ≡ n' ] ((¬ ((subst Fin n≡ i) ≡ i')) ⊎ ((subst Fin n≡ i) ≡ i' × d ~ d'))
  (tup[ i ] d) ~ FV ⊢ v ↦ w = False
  (tup[ i ] d) ~ left v = False
  (tup[ i ] d) ~ right v = False
  FV ⊢ v ↦ w ~ ω = True
  FV ⊢ v ↦ w ~ (FV' ⊢ν) = True
  FV ⊢ v ↦ w ~ const k = False
  FV ⊢ v ↦ w ~ ⦅ v₁ ∣ = False
  FV ⊢ v ↦ w ~ ∣ v₂ ⦆ = False
  FV ⊢ v ↦ w ~ (tup[ i ] d) = False
  FV ⊢ v ↦ w ~ FV' ⊢ v' ↦ w' = (¬ (v ~ v') ⊎ w ~ w')
  FV ⊢ u ↦ u₁ ~ left v = False
  FV ⊢ u ↦ u₁ ~ right v = False
  left u ~ ω = True
  left u ~ (FV ⊢ν) = False
  left u ~ const k = False
  left u ~ FV ⊢ v ↦ v₁ = False
  left u ~ ⦅ v ∣ = False
  left u ~ ∣ v₁ ⦆ = False
  left u ~ (tup[ i ] d) = False
  left u ~ left v = u ~ v
  left u ~ right v = False
  right u ~ ω = True
  right u ~ (FV ⊢ν) = False
  right u ~ const k = False
  right u ~ FV ⊢ v ↦ v₁ = False
  right u ~ ⦅ v ∣ = False
  right u ~ ∣ v₁ ⦆ = False
  right u ~ (tup[ i ] d) = False
  right u ~ left v = False
  right u ~ right v = u ~ v

  ~-const-inv : ∀ {B k k'} → const {B} k ~ const k' 
    → k ≡ k'
  ~-const-inv ⟨ refl , snd ⟩ = snd

  ~-tup-inv : ∀ {n}{i i' : Fin n}{d d'} → tup[ i ] d ~ tup[ i' ] d'
    → (¬ (i ≡ i')) ⊎ (i ≡ i' × d ~ d')
  ~-tup-inv ⟨ refl , snd ⟩ = snd

  _~?_ : (u : Value) → (v : Value) → Dec (u ~ v)
  ω ~? v = yes tt
  (u ⊢ν) ~? ω = yes tt
  (u ⊢ν) ~? (v ⊢ν) = yes tt
  (u ⊢ν) ~? const k = no (λ z → z)
  (u ⊢ν) ~? (v ⊔ v₁) = ((u ⊢ν) ~? v) ×-dec ((u ⊢ν) ~? v₁) 
  (u ⊢ν) ~? (v ⊢ v₁ ↦ v₂) = yes tt
  (u ⊢ν) ~? ⦅ v ∣ = no (λ z → z)
  (u ⊢ν) ~? ∣ v ⦆ = no (λ z → z)
  (u ⊢ν) ~? (tup[ i ] d) = no (λ z → z)
  (u ⊢ν) ~? left v = no (λ z → z)
  (u ⊢ν) ~? right v = no (λ z → z)
  const k ~? ω = yes tt
  const k ~? (v ⊢ν) = no (λ z → z)
  (const {B} k) ~? (const {B′} k′)
      with base-eq? B B′
  ... | no neq = no (λ z → neq (proj₁ z))
  ... | yes refl with base-rep-eq? k k′
  ... | yes refl = yes ⟨ refl , refl ⟩
  ... | no neq = no λ z → neq (~-const-inv z)
  const k ~? (v ⊔ v₁) = (const k ~? v) ×-dec (const k ~? v₁)
  const k ~? (v ⊢ v₁ ↦ v₂) = no (λ z → z)
  const k ~? ⦅ v ∣ = no (λ z → z)
  const k ~? ∣ v ⦆ = no (λ z → z)
  const k ~? (tup[ i ] d) = no (λ z → z)
  const k ~? left v = no (λ z → z)
  const k ~? right v = no (λ z → z)
  (u ⊔ u₁) ~? v = (u ~? v) ×-dec (u₁ ~? v)
  (u ⊢ u₁ ↦ u₂) ~? ω = yes tt
  (u ⊢ u₁ ↦ u₂) ~? (v ⊢ν) = yes tt
  (u ⊢ u₁ ↦ u₂) ~? const k = no (λ z → z)
  (u ⊢ u₁ ↦ u₂) ~? (v ⊔ v₁) = ((u ⊢ u₁ ↦ u₂) ~? v) ×-dec ((u ⊢ u₁ ↦ u₂) ~? v₁)
  (u ⊢ u₁ ↦ u₂) ~? (v ⊢ v₁ ↦ v₂) = (¬dec (u₁ ~? v₁) ∨dec (u₂ ~? v₂))
  (u ⊢ u₁ ↦ u₂) ~? ⦅ v ∣ = no (λ z → z)
  (u ⊢ u₁ ↦ u₂) ~? ∣ v ⦆ = no (λ z → z)
  (u ⊢ u₁ ↦ u₂) ~? (tup[ i ] d) = no (λ z → z)
  (u ⊢ u₁ ↦ u₂) ~? left v = no (λ z → z)
  (u ⊢ u₁ ↦ u₂) ~? right v = no (λ z → z)
  ⦅ u ∣ ~? ω = yes tt
  ⦅ u ∣ ~? (v ⊢ν) = no (λ z → z)
  ⦅ u ∣ ~? const k = no (λ z → z)
  ⦅ u ∣ ~? (v ⊔ v₁) = (⦅ u ∣ ~? v) ×-dec (⦅ u ∣ ~? v₁)
  ⦅ u ∣ ~? (v ⊢ v₁ ↦ v₂) = no (λ z → z)
  ⦅ u ∣ ~? ⦅ v ∣ = u ~? v
  ⦅ u ∣ ~? ∣ v ⦆ = yes tt
  ⦅ u ∣ ~? (tup[ i ] d) = no (λ z → z)
  ⦅ u ∣ ~? left v = no (λ z → z)
  ⦅ u ∣ ~? right v = no (λ z → z)
  ∣ u ⦆ ~? ω = yes tt
  ∣ u ⦆ ~? (v ⊢ν) = no (λ z → z)
  ∣ u ⦆ ~? const k = no (λ z → z)
  ∣ u ⦆ ~? (v ⊔ v₁) = (∣ u ⦆ ~? v) ×-dec (∣ u ⦆ ~? v₁)
  ∣ u ⦆ ~? (v ⊢ v₁ ↦ v₂) = no (λ z → z)
  ∣ u ⦆ ~? ⦅ v ∣ = yes tt
  ∣ u ⦆ ~? ∣ v ⦆ = u ~? v
  ∣ u ⦆ ~? (tup[ i ] d) = no (λ z → z)
  ∣ u ⦆ ~? left v = no (λ z → z)
  ∣ u ⦆ ~? right v = no (λ z → z)
  (tup[ i ] d) ~? ω = yes tt
  (tup[ i ] d) ~? (v ⊢ν) = no (λ z → z)
  (tup[ i ] d) ~? const k = no (λ z → z)
  (tup[ i ] d) ~? (v ⊔ v₁) = ((tup[ i ] d) ~? v) ×-dec ((tup[ i ] d) ~? v₁)
  (tup[ i ] d) ~? (v ⊢ v₁ ↦ v₂) = no (λ z → z)
  (tup[ i ] d) ~? ⦅ v ∣ = no (λ z → z)
  (tup[ i ] d) ~? ∣ v ⦆ = no (λ z → z)
  (tup[_]_ {n} i d) ~? (tup[_]_ {n'} i' d') with n ≟ n'
  ... | no neq = no (λ z → neq (proj₁ z))
  ... | yes refl with i fin≟ i'
  ... | no neq = yes ⟨ refl , inj₁ neq ⟩
  ... | yes refl with d ~? d'
  ... | yes d~ = yes ⟨ refl , inj₂ ⟨ refl , d~ ⟩ ⟩
  ... | no ¬d~ = no λ z → ¬d~ ([ (λ x → ⊥-elim (x refl)) 
                               , (λ x → proj₂ x) ] (~-tup-inv {n}{i}{i'}{d} z))
  (tup[ i ] d) ~? left v = no (λ z → z)
  (tup[ i ] d) ~? right v = no (λ z → z)
  left u ~? ω = yes tt
  left u ~? (v ⊢ν) = no (λ z → z)
  left u ~? const k = no (λ z → z)
  left u ~? (v ⊔ v₁) = (left u ~? v) ×-dec (left u ~? v₁)
  left u ~? (v ⊢ v₁ ↦ v₂) = no (λ z → z)
  left u ~? ⦅ v ∣ = no (λ z → z)
  left u ~? ∣ v ⦆ = no (λ z → z)
  left u ~? (tup[ i ] d) = no (λ z → z)
  left u ~? left v = u ~? v
  left u ~? right v = no (λ z → z)
  right u ~? ω = yes tt
  right u ~? (v ⊢ν) = no (λ z → z)
  right u ~? const k = no (λ z → z)
  right u ~? (v ⊔ v₁) = (right u ~? v) ×-dec (right u ~? v₁)
  right u ~? (v ⊢ v₁ ↦ v₂) = no (λ z → z)
  right u ~? ⦅ v ∣ = no (λ z → z)
  right u ~? ∣ v ⦆ = no (λ z → z)
  right u ~? (tup[ i ] d) = no (λ z → z)
  right u ~? left v = no (λ z → z)
  right u ~? right v = u ~? v

  ~-⊔-R : ∀ v {u₁ u₂} → v ~ u₁ → v ~ u₂
    → v ~ (u₁ ⊔ u₂)
  ~-⊔-R ω v~u₁ v~u₂ = tt
  ~-⊔-R (FV ⊢ν) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (const k) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (⦅ v₁ ∣) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (∣ v₂ ⦆) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (tup[ i ] d) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (FV ⊢ v ↦ w) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (v₁ ⊔ v₂) v~u₁ v~u₂ =
    ⟨ ~-⊔-R v₁ (proj₁ v~u₁) (proj₁ v~u₂) , ~-⊔-R v₂ (proj₂ v~u₁) (proj₂ v~u₂) ⟩
  ~-⊔-R (left v) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (right v) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩

  ~-⊔-R-inv : ∀ v {u₁ u₂} → v ~ (u₁ ⊔ u₂) → v ~ u₁ × v ~ u₂
  ~-⊔-R-inv ω v~u = ⟨ tt , tt ⟩
  ~-⊔-R-inv (FV ⊢ν) v~u = v~u
  ~-⊔-R-inv (const x) v~u = v~u
  ~-⊔-R-inv (FV ⊢ v ↦ v₁) v~u = v~u
  ~-⊔-R-inv (v ⊔ v₁) ⟨ v~u , v₁~u ⟩ with ~-⊔-R-inv v v~u | ~-⊔-R-inv v₁ v₁~u
  ... | ⟨ v~u₁ , v~u₂ ⟩ | ⟨ v₁~u₁ , v₁~u₂ ⟩ =
    ⟨ ⟨ v~u₁ , v₁~u₁ ⟩ , ⟨ v~u₂ , v₁~u₂ ⟩ ⟩
  ~-⊔-R-inv (⦅ v ∣) v~u = v~u
  ~-⊔-R-inv (∣ v₁ ⦆) v~u = v~u
  ~-⊔-R-inv (tup[ i ] d) v~u = v~u
  ~-⊔-R-inv (left v) v~u = v~u
  ~-⊔-R-inv (right v) v~u = v~u

  ~-⊔-cong : ∀{u v u′ v′}
    → (u ~ u′) → (u ~ v′)
    → (v ~ u′) → (v ~ v′)
    → (u ⊔ v) ~ (u′ ⊔ v′)
  ~-⊔-cong {u}{v}{u′}{v′} u~u′ u~v′ v~u′ v~v′ =
    ⟨ ~-⊔-R u u~u′ u~v′ , ~-⊔-R  v v~u′ v~v′ ⟩

  ~-↦ : {v w v′ w′ : Value} →
      ¬ v ~ v′ ⊎ w ~ w′ → v ~ v′ × w ~ w′ ⊎ ¬ v ~ v′
  ~-↦ (inj₁ x) = inj₂ x
  ~-↦ {v}{w}{v'}{w'} (inj₂ y) with v ~? v' 
  ... | yes v~v' = inj₁ ⟨ v~v' , y ⟩
  ... | no ¬v~v' = inj₂ ¬v~v'    

  ~-sym : ∀ u v → u ~ v → v ~ u
  ~-sym ω ω u~v = tt
  ~-sym ω (v ⊢ν) u~v = tt
  ~-sym ω (const k) u~v = tt
  ~-sym ω (v ⊔ v₁) u~v = ⟨ ~-sym ω v tt , ~-sym ω v₁ tt ⟩
  ~-sym ω (v ⊢ v₁ ↦ v₂) u~v = tt
  ~-sym ω ⦅ v ∣ u~v = tt
  ~-sym ω ∣ v ⦆ u~v = tt
  ~-sym ω (tup[ i ] d) u~v = tt
  ~-sym ω (left v) u~v = tt
  ~-sym ω (right v) u~v = tt
  ~-sym (u ⊢ν) ω u~v = tt
  ~-sym (u ⊢ν) (v ⊢ν) u~v = tt
  ~-sym (u ⊢ν) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (u ⊢ν) v fst , ~-sym (u ⊢ν) v₁ snd ⟩
  ~-sym (u ⊢ν) (v ⊢ v₁ ↦ v₂) u~v = tt
  ~-sym (const k) ω u~v = tt
  ~-sym (const {B} k) (const {B'} k₁) ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  ~-sym (const k) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (const k) v fst , ~-sym (const k) v₁ snd ⟩
  ~-sym (u ⊔ u₁) v ⟨ fst , snd ⟩ = ~-⊔-R v (~-sym u v fst) (~-sym u₁ v snd)
  ~-sym (u ⊢ u₁ ↦ u₂) ω u~v = tt
  ~-sym (u ⊢ u₁ ↦ u₂) (v ⊢ν) u~v = tt
  ~-sym (u ⊢ u₁ ↦ u₂) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (u ⊢ u₁ ↦ u₂) v fst , ~-sym (u ⊢ u₁ ↦ u₂) v₁ snd ⟩
  ~-sym (u ⊢ u₁ ↦ u₂) (v ⊢ v₁ ↦ v₂) (inj₁ x) = inj₁ (λ x' → x (~-sym v₁ u₁ x'))
  ~-sym (u ⊢ u₁ ↦ u₂) (v ⊢ v₁ ↦ v₂) (inj₂ y) = inj₂ (~-sym u₂ v₂ y)
  ~-sym ⦅ u ∣ ω u~v = tt
  ~-sym ⦅ u ∣ (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym ⦅ u ∣ v fst , ~-sym ⦅ u ∣ v₁ snd ⟩
  ~-sym ⦅ u ∣ ⦅ v ∣ u~v = ~-sym u v u~v
  ~-sym ⦅ u ∣ ∣ v ⦆ u~v = tt
  ~-sym ∣ u ⦆ ω u~v = tt
  ~-sym ∣ u ⦆ (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym ∣ u ⦆ v fst , ~-sym ∣ u ⦆ v₁ snd ⟩
  ~-sym ∣ u ⦆ ⦅ v ∣ u~v = tt
  ~-sym ∣ u ⦆ ∣ v ⦆ u~v = ~-sym u v u~v
  ~-sym (tup[ i ] d) ω u~v = tt
  ~-sym (tup[ i ] d) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (tup[ i ] d) v fst , ~-sym (tup[ i ] d) v₁ snd ⟩
  ~-sym (tup[_]_ {n} i d) (tup[_]_ {n'} i' d') ⟨ refl , inj₁ neq ⟩ = 
    ⟨ refl , inj₁ (λ z → neq (sym z)) ⟩
  ~-sym (tup[_]_ {n} i d) (tup[_]_ {n'} i' d') ⟨ refl , inj₂ ⟨ refl , d~ ⟩ ⟩ =
     ⟨ refl , inj₂ ⟨ refl , ~-sym d d' d~ ⟩ ⟩
  ~-sym (left u) ω u~v = tt
  ~-sym (left u) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (left u) v fst , ~-sym (left u) v₁ snd ⟩
  ~-sym (left u) (left v) u~v = ~-sym u v u~v
  ~-sym (right u) ω u~v = tt
  ~-sym (right u) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (right u) v fst , ~-sym (right u) v₁ snd ⟩
  ~-sym (right u) (right v) u~v = ~-sym u v u~v


  ~-split : ∀ {u u₁ u₂} → u₁ ◃ u ▹ u₂ → ∀ v → u₁ ~ v → u₂ ~ v → u ~ v
  ~-split split-⊔ v ~L ~R = ⟨ ~L , ~R ⟩
  ~-split (split-↦ split) ω ~L ~R = tt
  ~-split (split-↦ split) (FV ⊢ν) ~L ~R = ~R
  ~-split (split-↦ split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split (split-↦ split) v fst fst₁ , ~-split (split-↦ split) v₁ snd snd₁ ⟩
  ~-split (split-↦ split) (FV ⊢ v ↦ v₁) (inj₁ x) ~R = inj₁ x
  ~-split (split-↦ split) (FV ⊢ v ↦ v₁) (inj₂ y) (inj₁ x) = inj₁ x
  ~-split (split-↦ split) (FV ⊢ v ↦ v₁) (inj₂ y) (inj₂ y₁) = inj₂ (~-split split v₁ y y₁)
  ~-split (split-fst split) ω ~L ~R = tt
  ~-split (split-fst split) ∣ v ⦆ ~L ~R = tt
  ~-split (split-fst split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split (split-fst split) v fst fst₁ 
    , ~-split (split-fst split) v₁ snd snd₁ ⟩
  ~-split (split-fst split) (⦅ v ∣) ~L ~R = ~-split split v ~L ~R
  ~-split (split-snd split) ω tt tt = tt
  ~-split (split-snd split) ⦅ v ∣ ~L ~R = tt
  ~-split (split-snd split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split (split-snd split) v fst fst₁ 
    , ~-split (split-snd split) v₁ snd snd₁ ⟩
  ~-split (split-snd split) (∣ v₁ ⦆) ~L ~R = ~-split split v₁ ~L ~R
  ~-split (split-tup split) ω ~L ~R = tt
  ~-split (split-tup split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split (split-tup split) v fst fst₁ 
    , ~-split (split-tup split) v₁ snd snd₁ ⟩
  ~-split (split-tup {n} split) (tup[_]_ {n'} i' d') ⟨ refl , ~L ⟩ ⟨ refl , ~R ⟩ 
   = ⟨ refl , [ (λ z → inj₁ z) 
             , (λ z → [ (λ z' → ⊥-elim (z' (proj₁ z))) 
                      , (λ z' → inj₂ ⟨ proj₁ z' , ~-split split d' (proj₂ z) (proj₂ z') ⟩) ] ~R ) ] ~L ⟩
  ~-split (split-left split) ω u₁~v u₂~v = tt
  ~-split (split-left split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ =
   ⟨ ~-split (split-left split) v fst fst₁ , ~-split (split-left split) v₁ snd snd₁ ⟩
  ~-split (split-left split) (left v) u₁~v u₂~v = 
    ~-split split v u₁~v u₂~v
  ~-split (split-right split) ω u₁~v u₂~v = tt 
  ~-split (split-right split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
   ⟨ ~-split (split-right split) v fst fst₁ , ~-split (split-right split) v₁ snd snd₁ ⟩
  ~-split (split-right split) (right v) u₁~v u₂~v = 
    ~-split split v u₁~v u₂~v

  ~-split-inv : ∀ {u u₁ u₂} → u₁ ◃ u ▹ u₂ → ∀ v → u ~ v → u₁ ~ v × u₂ ~ v
  ~-split-inv split-⊔ v u~v = u~v
  ~-split-inv (split-↦ split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-↦ split) (FV ⊢ν) u~v = ⟨ u~v , u~v ⟩
  ~-split-inv (split-↦ split) (v ⊔ v₁) ⟨ fst , snd ⟩
     with ~-split-inv (split-↦ split) v fst | ~-split-inv (split-↦ split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-↦ split) (FV ⊢ v ↦ v₁) (inj₁ x) = ⟨ inj₁ x , inj₁ x ⟩
  ~-split-inv (split-↦ split) (FV ⊢ v ↦ v₁) (inj₂ y) with ~-split-inv split v₁ y
  ... | ⟨ L~ , R~ ⟩ = ⟨ inj₂ L~ , inj₂ R~ ⟩
  ~-split-inv (split-fst split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-fst split) ∣ v ⦆ u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-fst split) (v ⊔ v₁) ⟨ fst , snd ⟩
    with ~-split-inv (split-fst split) v fst | ~-split-inv (split-fst split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-fst split) (⦅ v ∣) u~v = ~-split-inv split v u~v
  ~-split-inv (split-snd split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-snd split) ⦅ v ∣ u~v = ⟨ tt , tt ⟩ 
  ~-split-inv (split-snd split) (v ⊔ v₁) ⟨ fst , snd ⟩ 
    with ~-split-inv (split-snd split) v fst | ~-split-inv (split-snd split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-snd split) (∣ v₁ ⦆) u~v = ~-split-inv split v₁ u~v
  ~-split-inv (split-tup split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-tup split) (v ⊔ v₁) ⟨ fst , snd ⟩
    with ~-split-inv (split-tup split) v fst | ~-split-inv (split-tup split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-tup {n} split) (tup[_]_ {.n} i' d') ⟨ refl , inj₁ x ⟩ = 
    ⟨ ⟨ refl , inj₁ x ⟩ , ⟨ refl , inj₁ x ⟩ ⟩
  ~-split-inv (split-tup {n} split) (tup[_]_ {.n} i' d') ⟨ refl , inj₂ ⟨ refl , d~ ⟩ ⟩ 
     with ~-split-inv split d' d~
  ... | ⟨ ~dL , ~dR ⟩ = 
    ⟨ ⟨ refl , inj₂ ⟨ refl , ~dL ⟩ ⟩ , ⟨ refl , inj₂ ⟨ refl , ~dR ⟩ ⟩ ⟩
  
  ~-split-inv (split-left split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-left split) (v ⊔ v₁) ⟨ fst , snd ⟩
    with ~-split-inv (split-left split) v fst | ~-split-inv (split-left split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-left split) (left v) u~v = ~-split-inv split v u~v
  ~-split-inv (split-right split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-right split) (v ⊔ v₁) ⟨ fst , snd ⟩
    with ~-split-inv (split-right split) v fst | ~-split-inv (split-right split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-right split) (right v) u~v = ~-split-inv split v u~v


  sc : Value → Set 
  sc v = v ~ v

  sc? : (v : Value) → Dec (sc v)
  sc? v = v ~? v


  data wf : Value → Set where
    wf-ω : wf ω
    wf-ν : ∀ {FV} → (wfFV : wf FV) → wf (FV ⊢ν)
    wf-const : ∀ {B} k → wf (const {B} k)
    wf-fun : ∀ {FV u v} → (wfFV : wf FV) → (wfu : wf u) → (wfv : wf v) → wf (FV ⊢ u ↦ v)
    wf-⊔ : ∀ {u v} → (u~v : u ~ v) → (wfu : wf u) → (wfv : wf v) → wf (u ⊔ v)
    wf-fst : ∀ {u} → (wfu : wf u) → wf ⦅ u ∣
    wf-snd : ∀ {v} → (wfv : wf v) → wf ∣ v ⦆
    wf-tup : ∀ {n} {i : Fin n} {d} → (wfd : wf d) → wf (tup[ i ] d)
    wf-left : ∀ {d} → (wfd : wf d) → wf (left d)
    wf-right : ∀ {d} → (wfd : wf d) → wf (right d)


  wf-fun-inv : ∀ {FV u v} → wf (FV ⊢ u ↦ v) → wf FV × wf u × wf v
  wf-fun-inv (wf-fun wfFV wfu wfv) = ⟨ wfFV , ⟨ wfu , wfv ⟩ ⟩

  wf-ν-inv : ∀ {FV} → wf (FV ⊢ν) → wf FV
  wf-ν-inv (wf-ν wfFV) = wfFV

  wf-⊔-inv : ∀ {u v} → wf (u ⊔ v) → u ~ v × wf u × wf v
  wf-⊔-inv (wf-⊔ u~v wf⊔ wf⊔₁) = ⟨ u~v , ⟨ wf⊔ , wf⊔₁ ⟩ ⟩

  wf-fst-inv : ∀ {d} → wf ⦅ d ∣ → wf d
  wf-fst-inv (wf-fst wfd) = wfd

  wf-snd-inv : ∀ {d} → wf ∣ d ⦆ → wf d
  wf-snd-inv (wf-snd wfd) = wfd
  
  wf-tup-inv : ∀ {n} {i : Fin n} {d} → wf (tup[ i ] d) → wf d
  wf-tup-inv (wf-tup wfd) = wfd

  wf-left-inv : ∀ {d} → wf (left d) → wf d
  wf-left-inv (wf-left wfd) = wfd

  wf-right-inv : ∀ {d} → wf (right d) → wf d
  wf-right-inv (wf-right wfd) = wfd

  wf? : (v : Value) → Dec (wf v)
  wf? ω = yes wf-ω
  wf? (FV ⊢ν) with wf? FV
  ... | no ¬wfFV = no (λ z → ¬wfFV (wf-ν-inv z))
  ... | yes wfFV = yes (wf-ν wfFV)
  wf? (const k) = yes (wf-const k)
  wf? (v ⊔ v₁) with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (proj₁ (proj₂ (wf-⊔-inv z))))
  ... | yes wfv with wf? v₁
  ... | no ¬wfv₁ = no (λ z → ¬wfv₁ (proj₂ (proj₂ (wf-⊔-inv z))))
  ... | yes wfv₁ with v ~? v₁
  ... | no ¬v~v₁ = no (λ z → ¬v~v₁ (proj₁ (wf-⊔-inv z)))
  ... | yes v~v₁ = yes (wf-⊔ v~v₁ wfv wfv₁) 
  wf? (FV ⊢ v ↦ v₁) with wf? FV
  ... | no ¬wfFV = no (λ z → ¬wfFV (proj₁ (wf-fun-inv z)))
  ... | yes wfFV with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (proj₁ (proj₂ (wf-fun-inv z))))
  ... | yes wfv with wf? v₁
  ... | no ¬wfv₁ = no λ z → ¬wfv₁ (proj₂ (proj₂ (wf-fun-inv z)))
  ... | yes wfv₁ = yes (wf-fun wfFV wfv wfv₁)
  wf? (⦅ v ∣) with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (wf-fst-inv z))
  ... | yes wfv = yes (wf-fst wfv)
  wf? (∣ v ⦆) with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (wf-snd-inv z))
  ... | yes wfv = yes (wf-snd wfv)
  wf? (tup[ i ] d) with wf? d
  ... | no ¬wfd = no (λ z → ¬wfd (wf-tup-inv z))
  ... | yes wfd = yes (wf-tup wfd)
  wf? (left d) with wf? d
  ... | no ¬wfd = no (λ z → ¬wfd (wf-left-inv z))
  ... | yes wfd = yes (wf-left wfd)
  wf? (right d) with wf? d
  ... | no ¬wfd = no (λ z → ¬wfd (wf-right-inv z))
  ... | yes wfd = yes (wf-right wfd)

  sc-å : ∀ v → Atomic v → sc v
  sc-å ω åv = tt
  sc-å (FV ⊢ν) åv = tt
  sc-å (const {B} k) åv = ⟨ refl , refl ⟩
  sc-å (FV ⊢ v ↦ v₁) åv₁ = inj₂ (sc-å v₁ åv₁)
  sc-å ⦅ d ∣ åd = sc-å d åd
  sc-å ∣ d ⦆ åd = sc-å d åd
  sc-å (tup[ i ] d) åv = ⟨ refl , inj₂ ⟨ refl , sc-å d åv ⟩ ⟩
  sc-å (left d) åd = sc-å d åd
  sc-å (right d) åd = sc-å d åd

  sc-⊔ : ∀ u v → sc u → sc v → u ~ v → sc (u ⊔ v)
  sc-⊔ u v scu scv u~v = ~-⊔-cong {u}{v}{u}{v} scu u~v (~-sym u v u~v) scv
  
  sc-↦ : ∀ {FV} u v → ((¬ (sc u)) ⊎ sc v) → sc (FV ⊢ u ↦ v)
  sc-↦ u v (inj₁ x) = inj₁ x
  sc-↦ u v (inj₂ y) = inj₂ y

  sc-tup : ∀ d → sc d → ∀ {n}{i : Fin n} → sc (tup[ i ] d)
  sc-tup d scd {n} = ⟨ refl , inj₂ ⟨ refl , scd ⟩ ⟩

  sc-tup-inv : ∀ {n}{i : Fin n} d → sc (tup[ i ] d) → sc d
  sc-tup-inv {n} d ⟨ refl , inj₁ x ⟩ = ⊥-elim (x refl)
  sc-tup-inv {n} d ⟨ refl , inj₂ ⟨ refl , scd ⟩ ⟩ = scd

  sc-split : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → sc v₁ → sc v₂ → v₁ ~ v₂ → sc v
  sc-split (split-⊔ {v₁}{v₂}) scL scR L~R = sc-⊔ v₁ v₂ scL scR L~R
  sc-split (split-↦ split) (inj₁ x) (inj₁ x₁) L~R = inj₁ x₁
  sc-split (split-↦ split) (inj₁ x) (inj₂ y) L~R = inj₁ x
  sc-split (split-↦ split) (inj₂ y) (inj₁ x) L~R = inj₁ x
  sc-split (split-↦ split) (inj₂ y) (inj₂ y₁) (inj₁ x)  = inj₁ x
  sc-split (split-↦ split) (inj₂ y) (inj₂ y₁) (inj₂ y₂) = inj₂ (sc-split split y y₁ y₂)
  sc-split (split-fst split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂
  sc-split (split-snd split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂
  sc-split (split-tup {n} {i} {d} {dL} {dR} split) ⟨ refl , inj₁ x ⟩ ⟨ refl , ~R ⟩ ⟨ refl , L~R ⟩ = ⊥-elim (x refl)
  sc-split (split-tup {n} {i} {d} {dL} {dR} split) ⟨ refl , inj₂ y ⟩ ⟨ refl , inj₁ x ⟩ ⟨ refl , L~R ⟩ = ⊥-elim (x refl)
  sc-split (split-tup {n} {i} {d} {dL} {dR} split) ⟨ refl , inj₂ y ⟩ ⟨ refl , inj₂ y₁ ⟩ ⟨ refl , inj₁ L~R ⟩ = ⊥-elim (L~R refl) 
  sc-split (split-tup {n} {i} {d} {dL} {dR} split) ⟨ refl , inj₂ y ⟩ ⟨ refl , inj₂ y₁ ⟩ ⟨ refl , inj₂ L~R ⟩ = 
    ⟨ refl , inj₂ ⟨ refl , sc-split split (proj₂ y) (proj₂ y₁) (proj₂ L~R) ⟩ ⟩
  sc-split (split-left split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂
  sc-split (split-right split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂

  sc-split-inv : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → sc v → sc v₁ × sc v₂ × v₁ ~ v₂
  sc-split-inv (split-⊔ {v₁}{v₂}) ⟨ fst , snd ⟩ = ⟨ proj₁ (~-⊔-R-inv v₁ fst) , ⟨ proj₂ (~-⊔-R-inv v₂ snd) , proj₂ (~-⊔-R-inv v₁ fst) ⟩ ⟩
  sc-split-inv (split-↦ split) (inj₁ ¬scu) = ⟨ inj₁ ¬scu  , ⟨ inj₁ ¬scu , inj₁ ¬scu ⟩ ⟩
  sc-split-inv (split-↦ split) (inj₂ scv) with sc-split-inv split scv
  ... | ⟨ scv₁ , ⟨ scv₂ , v₁~v₂ ⟩ ⟩  = ⟨ inj₂ scv₁ , ⟨ inj₂ scv₂ , inj₂ v₁~v₂ ⟩ ⟩
  sc-split-inv (split-fst split) scd = sc-split-inv split scd
  sc-split-inv (split-snd split) scd = sc-split-inv split scd
  sc-split-inv (split-tup {n}{i}{d} split) scd with sc-split-inv split (sc-tup-inv d scd)
  ... | ⟨ scdL , ⟨ scdR , L~R ⟩ ⟩ = 
    ⟨ ⟨ refl , inj₂ ⟨ refl , scdL ⟩ ⟩ , ⟨ ⟨ refl , inj₂ ⟨ refl , scdR ⟩ ⟩ 
    , ⟨ refl , inj₂ ⟨ refl , L~R ⟩ ⟩ ⟩ ⟩
  sc-split-inv (split-left split) scd = sc-split-inv split scd
  sc-split-inv (split-right split) scd = sc-split-inv split scd

  ~-refl : ∀ {v} → wf v → v ~ v
  ~-refl wf-ω = tt
  ~-refl (wf-ν wfFV) = tt
  ~-refl (wf-const {B} k) = ⟨ refl , refl ⟩
  ~-refl (wf-fun wfFV wfv wfv₁) = inj₂ (~-refl wfv₁)
  ~-refl (wf-⊔ {u}{v} u~v wfv wfv₁) = 
    ~-⊔-cong {u}{v}{u}{v} (~-refl wfv) u~v (~-sym u v u~v) (~-refl wfv₁)
  ~-refl (wf-fst wfd) = ~-refl wfd
  ~-refl (wf-snd wfd) = ~-refl wfd
  ~-refl (wf-tup wfd) = ⟨ refl , inj₂ ⟨ refl , ~-refl wfd ⟩ ⟩
  ~-refl (wf-left wfd) = ~-refl wfd
  ~-refl (wf-right wfd) = ~-refl wfd



  wf→sc : ∀ v → wf v → v ~ v
  wf→sc v wfv = ~-refl wfv

  wf-split : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → v₁ ~ v₂ → wf v₁ → wf v₂ → wf v
  wf-split split-⊔ = wf-⊔
  wf-split (split-↦ split) (inj₁ x) (wf-fun wfFVL wfL wfL₁) (wf-fun wfFVR wfR wfR₁) 
    = ⊥-elim (x (~-refl wfR))
  wf-split (split-↦ split) (inj₂ y) (wf-fun wfFVL wfL wfL₁) (wf-fun wfFVR wfR wfR₁) 
    = wf-fun wfFVR wfR (wf-split split y wfL₁ wfR₁)
  wf-split (split-fst split) ~fst (wf-fst wfL) (wf-fst wfR) = wf-fst (wf-split split ~fst wfL wfR)
  wf-split (split-snd split) ~snd (wf-snd wfL) (wf-snd wfR) = wf-snd (wf-split split ~snd wfL wfR)
  wf-split (split-tup split) ⟨ refl , inj₁ x ⟩ (wf-tup wfL) (wf-tup wfR) = ⊥-elim (x refl)
  wf-split (split-tup split) ⟨ refl , inj₂ y ⟩ (wf-tup wfL) (wf-tup wfR) = 
    wf-tup (wf-split split (proj₂ y) wfL wfR)
  wf-split (split-left split) d₁~d₂ (wf-left wfd₁) (wf-left wfd₂) = wf-left (wf-split split  d₁~d₂ wfd₁ wfd₂)
  wf-split (split-right split) d₁~d₂ (wf-right wfd₁) (wf-right wfd₂) = wf-right (wf-split split  d₁~d₂ wfd₁ wfd₂)

  wf-split-inv : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → wf v → v₁ ~ v₂ × wf v₁ × wf v₂
  wf-split-inv split-⊔ wfv = wf-⊔-inv wfv
  wf-split-inv (split-↦ split) (wf-fun wfFV wfv wfv₁) = 
    ⟨ inj₂ (proj₁ (wf-split-inv split wfv₁)) , ⟨ wf-fun wfFV wfv (proj₁ (proj₂ (wf-split-inv split wfv₁))) 
    , wf-fun wfFV wfv (proj₂ (proj₂ (wf-split-inv split wfv₁))) ⟩ ⟩
  wf-split-inv (split-fst split) (wf-fst wfv) = 
    ⟨ proj₁ (wf-split-inv split wfv) , ⟨ wf-fst (proj₁ (proj₂ (wf-split-inv split wfv))) 
    , wf-fst (proj₂ (proj₂ (wf-split-inv split wfv))) ⟩ ⟩
  wf-split-inv (split-snd split) (wf-snd wfv) = 
    ⟨ proj₁ (wf-split-inv split wfv) , ⟨ wf-snd (proj₁ (proj₂ (wf-split-inv split wfv))) 
    , wf-snd (proj₂ (proj₂ (wf-split-inv split wfv))) ⟩ ⟩
  wf-split-inv (split-tup split) (wf-tup wfd) =
    ⟨ ⟨ refl , inj₂ ⟨ refl , proj₁ (wf-split-inv split wfd) ⟩ ⟩ 
    , ⟨ wf-tup (proj₁ (proj₂ (wf-split-inv split wfd))) 
    , wf-tup (proj₂ (proj₂ (wf-split-inv split wfd))) ⟩ ⟩
  wf-split-inv (split-left split) (wf-left wfd) with wf-split-inv split wfd
  ... | ⟨ d~ , ⟨ wfd1 , wfd2 ⟩ ⟩ = ⟨ d~ , ⟨ wf-left wfd1 , wf-left wfd2 ⟩ ⟩
  wf-split-inv (split-right split) (wf-right wfd) with wf-split-inv split wfd
  ... | ⟨ d~ , ⟨ wfd1 , wfd2 ⟩ ⟩ = ⟨ d~ , ⟨ wf-right wfd1 , wf-right wfd2 ⟩ ⟩


  consistent-⊑-lemma : ∀ {u u'}
      → u' ⊑ u
      → ∀ v
      → u ~ v
      → u' ~ v
  consistent-⊑-lemma ⊑-ω v u~v = tt
  consistent-⊑-lemma ⊑-ν-ν ω u~v = tt
  consistent-⊑-lemma ⊑-ν-ν (v ⊢ν) u~v = tt
  consistent-⊑-lemma ⊑-ν-ν (v ⊔ v₁) u~v = 
    ⟨ consistent-⊑-lemma ⊑-ν-ν v (proj₁ u~v) , consistent-⊑-lemma ⊑-ν-ν v₁ (proj₂ u~v) ⟩
  consistent-⊑-lemma ⊑-ν-ν (v ⊢ v₁ ↦ v₂) u~v = tt
  consistent-⊑-lemma ⊑-ν-↦ ω u~v = tt
  consistent-⊑-lemma ⊑-ν-↦ (FV ⊢ν) u~v = tt
  consistent-⊑-lemma ⊑-ν-↦ (v ⊔ v₁) ⟨ fst , snd ⟩ = 
    ⟨ consistent-⊑-lemma ⊑-ν-↦ v fst , consistent-⊑-lemma ⊑-ν-↦ v₁ snd ⟩
  consistent-⊑-lemma ⊑-ν-↦ (FV ⊢ v ↦ v₁) u~v = tt
  consistent-⊑-lemma ⊑-const v u~v = u~v
  consistent-⊑-lemma (⊑-⊔-R1-å åu ⊑u) v u~v = consistent-⊑-lemma ⊑u v (proj₁ u~v)
  consistent-⊑-lemma (⊑-⊔-R2-å åu ⊑u) v u~v = consistent-⊑-lemma ⊑u v (proj₂ u~v)
  consistent-⊑-lemma (⊑-fst-å åu ⊑u) ω u~v = tt
  consistent-⊑-lemma (⊑-fst-å åu ⊑u) (v ⊔ v₁) u~v = 
    ⟨ consistent-⊑-lemma (⊑-fst-å åu ⊑u) v (proj₁ u~v) , consistent-⊑-lemma (⊑-fst-å åu ⊑u) v₁ (proj₂ u~v) ⟩
  consistent-⊑-lemma (⊑-fst-å åu ⊑u) ⦅ v ∣ u~v = consistent-⊑-lemma ⊑u v u~v
  consistent-⊑-lemma (⊑-fst-å åu ⊑u) ∣ v ⦆ u~v = tt
  consistent-⊑-lemma (⊑-snd-å åu ⊑u) ω u~v = tt
  consistent-⊑-lemma (⊑-snd-å åu ⊑u) (v ⊔ v₁) u~v = 
    ⟨ consistent-⊑-lemma (⊑-snd-å åu ⊑u) v (proj₁ u~v) , consistent-⊑-lemma (⊑-snd-å åu ⊑u) v₁ (proj₂ u~v) ⟩
  consistent-⊑-lemma (⊑-snd-å åu ⊑u) ⦅ v ∣ u~v = tt
  consistent-⊑-lemma (⊑-snd-å åu ⊑u) ∣ v ⦆ u~v = consistent-⊑-lemma ⊑u v u~v
  consistent-⊑-lemma (⊑-tup-å åd ⊑d) ω u~v = tt
  consistent-⊑-lemma (⊑-tup-å åd ⊑d) (v ⊔ v₁) ⟨ fst , snd ⟩ = 
    ⟨ consistent-⊑-lemma (⊑-tup-å åd ⊑d) v fst 
    , consistent-⊑-lemma (⊑-tup-å åd ⊑d) v₁ snd ⟩
  consistent-⊑-lemma (⊑-tup-å åd ⊑d) (tup[ i ] d) ⟨ refl , inj₁ x ⟩ = ⟨ refl , inj₁ x ⟩
  consistent-⊑-lemma (⊑-tup-å åd ⊑d) (tup[ i ] d) ⟨ refl , inj₂ ⟨ refl , d~ ⟩ ⟩ = 
    ⟨ refl , inj₂ ⟨ refl , consistent-⊑-lemma ⊑d d d~ ⟩ ⟩
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) ω u~v = tt
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) (FV ⊢ν) u~v = tt
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) (v ⊔ v₁) ⟨ fst , snd ⟩ = 
    ⟨ consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) v fst
    , consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) v₁ snd ⟩
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) (FV ⊢ v ↦ v₁) (inj₁ x) = 
    inj₁ (λ z → x (consistent-⊑-lemma ⊑u v z))
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) (FV ⊢ v ↦ v₁) (inj₂ y) =
    inj₂ (consistent-⊑-lemma ⊑u₁ v₁ y)
  consistent-⊑-lemma (⊑-left-å åu ⊑u) ω u~v = tt
  consistent-⊑-lemma (⊑-left-å åu ⊑u) (left v) u~v = consistent-⊑-lemma ⊑u v u~v
  consistent-⊑-lemma (⊑-left-å åu ⊑u) (v ⊔ v₁) u~v = 
    ⟨ consistent-⊑-lemma (⊑-left-å åu ⊑u) v (proj₁ u~v) 
    , consistent-⊑-lemma (⊑-left-å åu ⊑u) v₁ (proj₂ u~v) ⟩
  consistent-⊑-lemma (⊑-right-å åu ⊑u) ω u~v = tt
  consistent-⊑-lemma (⊑-right-å åu ⊑u) (v ⊔ v₁) u~v = 
    ⟨ consistent-⊑-lemma (⊑-right-å åu ⊑u) v (proj₁ u~v) 
    , consistent-⊑-lemma (⊑-right-å åu ⊑u) v₁ (proj₂ u~v) ⟩
  consistent-⊑-lemma (⊑-right-å åu ⊑u) (right v) u~v = consistent-⊑-lemma ⊑u v u~v
  consistent-⊑-lemma (⊑-split split ⊑u ⊑u₁) v u~v with consistent-⊑-lemma ⊑u v u~v | consistent-⊑-lemma ⊑u₁ v u~v
  ... | u₁~v | u₂~v = ~-split split v u₁~v u₂~v


  consistent-⊑ : ∀ {u v u' v'}
        → u ~ v
        → u' ⊑ u → v' ⊑ v
        → u' ~ v'
  consistent-⊑ {u} {v} {u'} {v'} u~v ⊑u ⊑v = ~-sym v' u' (consistent-⊑-lemma ⊑v u' (~-sym u' v (consistent-⊑-lemma ⊑u v u~v))) 


  consistent : Consistent value_struct ordering
  consistent = record {
      _~_ = _~_
    ; wf = wf
    ; wf-bot = wf-ω
    ; wf-⊔ = wf-⊔
    ; wf-fun = wf-fun wf-ω
    ; wf-fun-inv = λ {v}{w} z → proj₂ (wf-fun-inv {ω}{v}{w} z)
    ; ~-refl = λ {v}{wfv} → ~-refl wfv
    ; ~-sym = λ {u}{v} → ~-sym u v
    ; ~-⊑ = consistent-⊑
    ; ~-↦-cong = λ _ → inj₂
    ; ~-↦ = λ {v}{w}{v'}{w'} z → ~-↦ {v}{w}{v'}{w'} z
    ; ~-⊔-cong = λ {u}{v}{u′}{v′} → ~-⊔-cong {u}{v}{u′}{v′}
    }



{-




u~v⊔w→u~v : ∀{u v w}
  → u ~ v ⊔ w
  → u ~ v
u~v⊔w→u~v {u} u~v⊔w = proj₁ (~⊔R-inv u u~v⊔w)

u~v⊔w→u~w : ∀{u v w}
  → u ~ v ⊔ w
  → u ~ w
u~v⊔w→u~w {u} u~v⊔w = proj₂ (~⊔R-inv u u~v⊔w)




pair-≡ : ∀ {u₁ u₂ v₁ v₂} → ⦅ u₁ , u₂ ⦆ ≡ ⦅ v₁ , v₂ ⦆ → u₁ ≡ v₁ × u₂ ≡ v₂
pair-≡ refl = ⟨ refl , refl ⟩




k⊑v→k′⊑v→k′≡k : ∀{b : Base}{k k′ : base-rep b}{v : Value}
              → wf v
              → const {b} k ⊑ v → const {b} k′ ⊑ v
              → k ≡ k′
k⊑v→k′⊑v→k′≡k {b}{k}{k′}{v} wfv k⊑v k′⊑v
    with base-eq? b b | consistent-⊑{v}{v} (~-refl{v} wfv) k⊑v k′⊑v
... | no neq | k~k′ = ⊥-elim (neq refl)
... | yes refl | k~k′ =  k~k′




-}