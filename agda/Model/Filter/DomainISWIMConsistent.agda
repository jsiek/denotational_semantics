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
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)

module Model.Filter.DomainISWIMConsistent where

  open import Primitives
  open import Model.Filter.DomainUtil
  open import Model.Filter.DomainISWIMValues
  open import Model.Filter.DomainISWIMOrdering


  {-
  Consistency
  -}

  infix 4 _~_

  {-
  question, should ν be consistent with functions?
  ... it would allow unioning... but that's something that shouldn't appear in our semantics
  -}
  _~_ : Value → Value → Set
  ω ~ v = True
  (u₁ ⊔ u₂) ~ v = u₁ ~ v × u₂ ~ v
  ν ~ v₁ ⊔ v₂ = ν ~ v₁ × ν ~ v₂
  const x ~ v₁ ⊔ v₂ = const x ~ v₁ × const x ~ v₂
  u ↦ u₁ ~ v₁ ⊔ v₂ = u ↦ u₁ ~ v₁ × u ↦ u₁ ~ v₂
  ⦅ u ∣ ~ v₁ ⊔ v₂ = ⦅ u ∣ ~ v₁ × ⦅ u ∣ ~ v₂
  ∣ u₁ ⦆ ~ v₁ ⊔ v₂ = ∣ u₁ ⦆ ~ v₁ × ∣ u₁ ⦆ ~ v₂
  ∥ us ∥ ~ v₁ ⊔ v₂ = ∥ us ∥ ~ v₁ × ∥ us ∥ ~ v₂
  left u ~ v ⊔ v₁ = left u ~ v × left u ~ v₁
  right u ~ v ⊔ v₁ = right u ~ v × right u ~ v₁
  ν ~ ω = True
  ν ~ ν = True
  ν ~ const x = False
  ν ~ v ↦ v₁ = True
  ν ~ ⦅ v ∣ = False
  ν ~ ∣ v₁ ⦆ = False
  ν ~ ∥ vs ∥ = False
  ν ~ left v = False
  ν ~ right v = False
  const {B} k ~ ω = True
  const {B} k ~ ν = False
  const {B} k ~ const {B′} k′
    with base-eq? B B′
  ... | yes eq rewrite eq = k ≡ k′
  ... | no neq = False
  const {B} k ~ ⦅ v₁ ∣ = False
  const {B} k ~ ∣ v₂ ⦆ = False
  const {B} k ~ ∥ vs ∥ = False
  const {B} k ~ v ↦ w = False
  const k ~ left v = False
  const k ~ right v = False
  ⦅ u ∣ ~ ω = True
  ⦅ u ∣ ~ ν = False
  ⦅ u ∣ ~ const k = False
  ⦅ u ∣ ~ v₁ ↦ v₂ = False
  ⦅ u ∣ ~ ⦅ v ∣ = u ~ v
  ⦅ u ∣ ~ ∣ v ⦆ = True
  ⦅ u ∣ ~ ∥ ds ∥ = False
  ⦅ u ∣ ~ left v = False
  ⦅ u ∣ ~ right v = False
  ∣ u ⦆ ~ ω = True
  ∣ u ⦆ ~ ν = False
  ∣ u ⦆ ~ const k = False
  ∣ u ⦆ ~ v₁ ↦ v₂ = False
  ∣ u ⦆ ~ ⦅ v ∣ = True
  ∣ u ⦆ ~ ∣ v ⦆ = u ~ v
  ∣ u ⦆ ~ ∥ ds ∥ = False
  ∣ u ⦆ ~ left v = False
  ∣ u ⦆ ~ right v = False
  ∥ us ∥ ~ ω = True
  ∥ us ∥ ~ ν = False
  ∥ us ∥ ~ const k = False
  ∥ us ∥ ~ ⦅ v ∣ = False
  ∥ us ∥ ~ ∣ v₁ ⦆ = False
  ∥ [] ∥ ~ ∥ [] ∥ = True
  ∥ [] ∥ ~ ∥ v ∷ vs ∥ = False
  ∥ u ∷ us ∥ ~ ∥ [] ∥ = False
  ∥ u ∷ us ∥ ~ ∥ v ∷ vs ∥ = u ~ v × ∥ us ∥ ~ ∥ vs ∥
  ∥ us ∥ ~ v ↦ w = False
  ∥ ds ∥ ~ left v = False
  ∥ ds ∥ ~ right v = False
  v ↦ w ~ ω = True
  v ↦ w ~ ν = True
  v ↦ w ~ const k = False
  v ↦ w ~ ⦅ v₁ ∣ = False
  v ↦ w ~ ∣ v₂ ⦆ = False
  v ↦ w ~ ∥ vs ∥ = False
  v ↦ w ~ v' ↦ w' = (¬ (v ~ v') ⊎ w ~ w')
  u ↦ u₁ ~ left v = False
  u ↦ u₁ ~ right v = False
  left u ~ ω = True
  left u ~ ν = False
  left u ~ const k = False
  left u ~ v ↦ v₁ = False
  left u ~ ⦅ v ∣ = False
  left u ~ ∣ v₁ ⦆ = False
  left u ~ ∥ ds ∥ = False
  left u ~ left v = u ~ v
  left u ~ right v = False
  right u ~ ω = True
  right u ~ ν = False
  right u ~ const k = False
  right u ~ v ↦ v₁ = False
  right u ~ ⦅ v ∣ = False
  right u ~ ∣ v₁ ⦆ = False
  right u ~ ∥ ds ∥ = False
  right u ~ left v = False
  right u ~ right v = u ~ v

  _~?_ : (u : Value) → (v : Value) → Dec (u ~ v)
  ω ~? v = yes tt
  ν ~? ω = yes tt
  ν ~? ν = yes tt
  ν ~? const k = no (λ z → z)
  ν ~? (v ⊔ v₁) = (ν ~? v) ×-dec (ν ~? v₁) 
  ν ~? (v₁ ↦ v₂) = yes tt
  ν ~? ⦅ v ∣ = no (λ z → z)
  ν ~? ∣ v ⦆ = no (λ z → z)
  ν ~? ∥ ds ∥ = no (λ z → z)
  ν ~? left v = no (λ z → z)
  ν ~? right v = no (λ z → z)
  const k ~? ω = yes tt
  const k ~? ν = no (λ z → z)
  (const {B} k) ~? (const {B′} k′)
      with base-eq? B B′
  ... | yes eq rewrite eq = base-rep-eq? k k′
  ... | no neq = no (λ z → z)
  const k ~? (v ⊔ v₁) = (const k ~? v) ×-dec (const k ~? v₁)
  const k ~? (v₁ ↦ v₂) = no (λ z → z)
  const k ~? ⦅ v ∣ = no (λ z → z)
  const k ~? ∣ v ⦆ = no (λ z → z)
  const k ~? ∥ ds ∥ = no (λ z → z)
  const k ~? left v = no (λ z → z)
  const k ~? right v = no (λ z → z)
  (u ⊔ u₁) ~? v = (u ~? v) ×-dec (u₁ ~? v)
  (u₁ ↦ u₂) ~? ω = yes tt
  (u₁ ↦ u₂) ~? ν = yes tt
  (u₁ ↦ u₂) ~? const k = no (λ z → z)
  (u₁ ↦ u₂) ~? (v ⊔ v₁) = ((u₁ ↦ u₂) ~? v) ×-dec ((u₁ ↦ u₂) ~? v₁)
  (u₁ ↦ u₂) ~? (v₁ ↦ v₂) = (¬dec (u₁ ~? v₁) ∨dec (u₂ ~? v₂))
  (u₁ ↦ u₂) ~? ⦅ v ∣ = no (λ z → z)
  (u₁ ↦ u₂) ~? ∣ v ⦆ = no (λ z → z)
  (u₁ ↦ u₂) ~? ∥ ds ∥ = no (λ z → z)
  (u₁ ↦ u₂) ~? left v = no (λ z → z)
  (u₁ ↦ u₂) ~? right v = no (λ z → z)
  ⦅ u ∣ ~? ω = yes tt
  ⦅ u ∣ ~? ν = no (λ z → z)
  ⦅ u ∣ ~? const k = no (λ z → z)
  ⦅ u ∣ ~? (v ⊔ v₁) = (⦅ u ∣ ~? v) ×-dec (⦅ u ∣ ~? v₁)
  ⦅ u ∣ ~? (v₁ ↦ v₂) = no (λ z → z)
  ⦅ u ∣ ~? ⦅ v ∣ = u ~? v
  ⦅ u ∣ ~? ∣ v ⦆ = yes tt
  ⦅ u ∣ ~? ∥ ds ∥ = no (λ z → z)
  ⦅ u ∣ ~? left v = no (λ z → z)
  ⦅ u ∣ ~? right v = no (λ z → z)
  ∣ u ⦆ ~? ω = yes tt
  ∣ u ⦆ ~? ν = no (λ z → z)
  ∣ u ⦆ ~? const k = no (λ z → z)
  ∣ u ⦆ ~? (v ⊔ v₁) = (∣ u ⦆ ~? v) ×-dec (∣ u ⦆ ~? v₁)
  ∣ u ⦆ ~? (v₁ ↦ v₂) = no (λ z → z)
  ∣ u ⦆ ~? ⦅ v ∣ = yes tt
  ∣ u ⦆ ~? ∣ v ⦆ = u ~? v
  ∣ u ⦆ ~? ∥ ds ∥ = no (λ z → z)
  ∣ u ⦆ ~? left v = no (λ z → z)
  ∣ u ⦆ ~? right v = no (λ z → z)
  ∥ ds ∥ ~? ω = yes tt
  ∥ ds ∥ ~? ν = no (λ z → z)
  ∥ ds ∥ ~? const k = no (λ z → z)
  ∥ ds ∥ ~? (v ⊔ v₁) = (∥ ds ∥ ~? v) ×-dec (∥ ds ∥ ~? v₁)
  ∥ ds ∥ ~? (v₁ ↦ v₂) = no (λ z → z)
  ∥ ds ∥ ~? ⦅ v ∣ = no (λ z → z)
  ∥ ds ∥ ~? ∣ v ⦆ = no (λ z → z)
  ∥ [] ∥ ~? ∥ [] ∥ = yes tt
  ∥ [] ∥ ~? ∥ x ∷ ds₁ ∥ = no (λ z → z)
  ∥ x ∷ ds ∥ ~? ∥ [] ∥ = no (λ z → z)
  ∥ x ∷ ds ∥ ~? ∥ x₁ ∷ ds₁ ∥ = (x ~? x₁) ×-dec (∥ ds ∥ ~? ∥ ds₁ ∥)
  ∥ ds ∥ ~? left v = no (λ z → z)
  ∥ ds ∥ ~? right v = no (λ z → z)
  left u ~? ω = yes tt
  left u ~? ν = no (λ z → z)
  left u ~? const k = no (λ z → z)
  left u ~? (v ⊔ v₁) = (left u ~? v) ×-dec (left u ~? v₁)
  left u ~? (v₁ ↦ v₂) = no (λ z → z)
  left u ~? ⦅ v ∣ = no (λ z → z)
  left u ~? ∣ v ⦆ = no (λ z → z)
  left u ~? ∥ ds ∥ = no (λ z → z)
  left u ~? left v = u ~? v
  left u ~? right v = no (λ z → z)
  right u ~? ω = yes tt
  right u ~? ν = no (λ z → z)
  right u ~? const k = no (λ z → z)
  right u ~? (v ⊔ v₁) = (right u ~? v) ×-dec (right u ~? v₁)
  right u ~? (v₁ ↦ v₂) = no (λ z → z)
  right u ~? ⦅ v ∣ = no (λ z → z)
  right u ~? ∣ v ⦆ = no (λ z → z)
  right u ~? ∥ ds ∥ = no (λ z → z)
  right u ~? left v = no (λ z → z)
  right u ~? right v = u ~? v

  ~-⊔-R : ∀ v {u₁ u₂} → v ~ u₁ → v ~ u₂
    → v ~ (u₁ ⊔ u₂)
  ~-⊔-R ω v~u₁ v~u₂ = tt
  ~-⊔-R ν v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (const k) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (⦅ v₁ ∣) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (∣ v₂ ⦆) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R ∥ vs ∥ v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (v ↦ w) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (v₁ ⊔ v₂) v~u₁ v~u₂ =
    ⟨ ~-⊔-R v₁ (proj₁ v~u₁) (proj₁ v~u₂) , ~-⊔-R v₂ (proj₂ v~u₁) (proj₂ v~u₂) ⟩
  ~-⊔-R (left v) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
  ~-⊔-R (right v) v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩

  ~-⊔-R-inv : ∀ v {u₁ u₂} → v ~ (u₁ ⊔ u₂) → v ~ u₁ × v ~ u₂
  ~-⊔-R-inv ω v~u = ⟨ tt , tt ⟩
  ~-⊔-R-inv ν v~u = v~u
  ~-⊔-R-inv (const x) v~u = v~u
  ~-⊔-R-inv (v ↦ v₁) v~u = v~u
  ~-⊔-R-inv (v ⊔ v₁) ⟨ v~u , v₁~u ⟩ with ~-⊔-R-inv v v~u | ~-⊔-R-inv v₁ v₁~u
  ... | ⟨ v~u₁ , v~u₂ ⟩ | ⟨ v₁~u₁ , v₁~u₂ ⟩ =
    ⟨ ⟨ v~u₁ , v₁~u₁ ⟩ , ⟨ v~u₂ , v₁~u₂ ⟩ ⟩
  ~-⊔-R-inv (⦅ v ∣) v~u = v~u
  ~-⊔-R-inv (∣ v₁ ⦆) v~u = v~u
  ~-⊔-R-inv ∥ vs ∥ v~u = v~u
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
  ~-sym ω ν u~v = tt
  ~-sym ω (const k) u~v = tt
  ~-sym ω (v ⊔ v₁) u~v = ⟨ ~-sym ω v tt , ~-sym ω v₁ tt ⟩
  ~-sym ω (v₁ ↦ v₂) u~v = tt
  ~-sym ω ⦅ v ∣ u~v = tt
  ~-sym ω ∣ v ⦆ u~v = tt
  ~-sym ω ∥ ds ∥ u~v = tt
  ~-sym ω (left v) u~v = tt
  ~-sym ω (right v) u~v = tt
  ~-sym ν ω u~v = tt
  ~-sym ν ν u~v = tt
  ~-sym ν (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym ν v fst , ~-sym ν v₁ snd ⟩
  ~-sym ν (v₁ ↦ v₂) u~v = tt
  ~-sym (const k) ω u~v = tt
  ~-sym (const {B} k) (const {B'} k₁) u~v with base-eq? B B'
  ... | no neq = ⊥-elim u~v
  ... | yes refl with base-eq? B B
  ... | no neq = neq refl
  ... | yes refl = sym u~v
  ~-sym (const k) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (const k) v fst , ~-sym (const k) v₁ snd ⟩
  ~-sym (u ⊔ u₁) v ⟨ fst , snd ⟩ = ~-⊔-R v (~-sym u v fst) (~-sym u₁ v snd)
  ~-sym (u₁ ↦ u₂) ω u~v = tt
  ~-sym (u₁ ↦ u₂) ν u~v = tt
  ~-sym (u₁ ↦ u₂) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (u₁ ↦ u₂) v fst , ~-sym (u₁ ↦ u₂) v₁ snd ⟩
  ~-sym (u₁ ↦ u₂) (v₁ ↦ v₂) (inj₁ x) = inj₁ (λ x' → x (~-sym v₁ u₁ x'))
  ~-sym (u₁ ↦ u₂) (v₁ ↦ v₂) (inj₂ y) = inj₂ (~-sym u₂ v₂ y)
  ~-sym ⦅ u ∣ ω u~v = tt
  ~-sym ⦅ u ∣ (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym ⦅ u ∣ v fst , ~-sym ⦅ u ∣ v₁ snd ⟩
  ~-sym ⦅ u ∣ ⦅ v ∣ u~v = ~-sym u v u~v
  ~-sym ⦅ u ∣ ∣ v ⦆ u~v = tt
  ~-sym ∣ u ⦆ ω u~v = tt
  ~-sym ∣ u ⦆ (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym ∣ u ⦆ v fst , ~-sym ∣ u ⦆ v₁ snd ⟩
  ~-sym ∣ u ⦆ ⦅ v ∣ u~v = tt
  ~-sym ∣ u ⦆ ∣ v ⦆ u~v = ~-sym u v u~v
  ~-sym ∥ ds ∥ ω u~v = tt
  ~-sym ∥ ds ∥ (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym ∥ ds ∥ v fst , ~-sym ∥ ds ∥ v₁ snd ⟩
  ~-sym ∥ [] ∥ ∥ [] ∥ u~v = tt
  ~-sym ∥ x ∷ ds ∥ ∥ x₁ ∷ ds₁ ∥ ⟨ fst , snd ⟩ = ⟨ ~-sym x x₁ fst , ~-sym ∥ ds ∥ ∥ ds₁ ∥ snd ⟩
  ~-sym (left u) ω u~v = tt
  ~-sym (left u) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (left u) v fst , ~-sym (left u) v₁ snd ⟩
  ~-sym (left u) (left v) u~v = ~-sym u v u~v
  ~-sym (right u) ω u~v = tt
  ~-sym (right u) (v ⊔ v₁) ⟨ fst , snd ⟩ = ⟨ ~-sym (right u) v fst , ~-sym (right u) v₁ snd ⟩
  ~-sym (right u) (right v) u~v = ~-sym u v u~v

  ~-split : ∀ {u u₁ u₂} → u₁ ◃ u ▹ u₂ → ∀ v → u₁ ~ v → u₂ ~ v → u ~ v
  ~-split split-⊔ v ~L ~R = ⟨ ~L , ~R ⟩
  ~-split (split-↦ split) ω ~L ~R = tt
  ~-split (split-↦ split) ν ~L ~R = ~R
  ~-split (split-↦ split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split (split-↦ split) v fst fst₁ , ~-split (split-↦ split) v₁ snd snd₁ ⟩
  ~-split (split-↦ split) (v ↦ v₁) (inj₁ x) ~R = inj₁ x
  ~-split (split-↦ split) (v ↦ v₁) (inj₂ y) (inj₁ x) = inj₁ x
  ~-split (split-↦ split) (v ↦ v₁) (inj₂ y) (inj₂ y₁) = inj₂ (~-split split v₁ y y₁)
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
  ~-split (split-tup-head split) ω ~L ~R = tt
  ~-split (split-tup-head split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split (split-tup-head split) v fst fst₁ 
    , ~-split (split-tup-head split) v₁ snd snd₁ ⟩
  ~-split (split-tup-head split) ∥ v ∷ vs ∥ ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split split v fst fst₁ , snd₁ ⟩
  ~-split (split-tup-tail x split) ω tt tt = tt
  ~-split (split-tup-tail x split) (v ⊔ v₁) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ ~-split (split-tup-tail x split) v fst fst₁ 
    , ~-split (split-tup-tail x split) v₁ snd snd₁ ⟩
  ~-split (split-tup-tail x split) ∥ v ∷ vs ∥ ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ = 
    ⟨ fst₁ , ~-split split ∥ vs ∥ snd snd₁ ⟩
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
  ~-split-inv (split-↦ split) ν u~v = ⟨ u~v , u~v ⟩
  ~-split-inv (split-↦ split) (v ⊔ v₁) ⟨ fst , snd ⟩
     with ~-split-inv (split-↦ split) v fst | ~-split-inv (split-↦ split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-↦ split) (v ↦ v₁) (inj₁ x) = ⟨ inj₁ x , inj₁ x ⟩
  ~-split-inv (split-↦ split) (v ↦ v₁) (inj₂ y) with ~-split-inv split v₁ y
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
  ~-split-inv (split-tup-head split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-tup-head split) (v ⊔ v₁) ⟨ fst , snd ⟩
    with ~-split-inv (split-tup-head split) v fst | ~-split-inv (split-tup-head split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-tup-head split) ∥ x ∷ vs ∥ ⟨ fst , snd ⟩ with ~-split-inv split x fst
  ... | ⟨ L~ , R~ ⟩ = ⟨ ⟨ L~ , snd ⟩ , ⟨ R~ , snd ⟩ ⟩
  ~-split-inv (split-tup-tail x split) ω u~v = ⟨ tt , tt ⟩
  ~-split-inv (split-tup-tail x split) (v ⊔ v₁) ⟨ fst , snd ⟩
    with ~-split-inv (split-tup-tail x split) v fst | ~-split-inv (split-tup-tail x split) v₁ snd
  ... | ⟨ fstL~ , fstR~ ⟩ | ⟨ sndL~ , sndR~ ⟩ = ⟨ ⟨ fstL~ , sndL~ ⟩ , ⟨ fstR~ , sndR~ ⟩ ⟩
  ~-split-inv (split-tup-tail x split) ∥ x₁ ∷ vs ∥ ⟨ fst , snd ⟩ with ~-split-inv split ∥ vs ∥ snd
  ... | ⟨ L~ , R~ ⟩ = ⟨ ⟨ fst , L~ ⟩ , ⟨ fst , R~ ⟩ ⟩
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
    wf-ν : wf ν
    wf-const : ∀ {B} k → wf (const {B} k)
    wf-fun : ∀ {u v} → (wfu : wf u) → (wfv : wf v) → wf (u ↦ v)
    wf-⊔ : ∀ {u v} → (u~v : u ~ v) → (wfu : wf u) → (wfv : wf v) → wf (u ⊔ v)
    wf-fst : ∀ {u} → (wfu : wf u) → wf ⦅ u ∣
    wf-snd : ∀ {v} → (wfv : wf v) → wf ∣ v ⦆
    wf-nil : wf (∥ [] ∥)
    wf-tup : ∀ {n v vs} → (wfv : wf v) → (wfvs : wf (∥_∥ {n} vs)) → wf ∥ v ∷ vs ∥
    wf-left : ∀ {d} → (wfd : wf d) → wf (left d)
    wf-right : ∀ {d} → (wfd : wf d) → wf (right d)

  wf-fun-inv : ∀ {u v} → wf (u ↦ v) → wf u × wf v
  wf-fun-inv (wf-fun wfu wfv) = ⟨ wfu , wfv ⟩

  wf-⊔-inv : ∀ {u v} → wf (u ⊔ v) → u ~ v × wf u × wf v
  wf-⊔-inv (wf-⊔ u~v wf⊔ wf⊔₁) = ⟨ u~v , ⟨ wf⊔ , wf⊔₁ ⟩ ⟩

  wf-fst-inv : ∀ {d} → wf ⦅ d ∣ → wf d
  wf-fst-inv (wf-fst wfd) = wfd

  wf-snd-inv : ∀ {d} → wf ∣ d ⦆ → wf d
  wf-snd-inv (wf-snd wfd) = wfd
  
  wf-tup-inv : ∀ {n v vs} → wf ∥ v ∷ vs ∥ → wf v × wf (∥_∥ {n} vs)
  wf-tup-inv (wf-tup wftup wftup₁) = ⟨ wftup , wftup₁ ⟩

  wf-left-inv : ∀ {d} → wf (left d) → wf d
  wf-left-inv (wf-left wfd) = wfd

  wf-right-inv : ∀ {d} → wf (right d) → wf d
  wf-right-inv (wf-right wfd) = wfd

  wf? : (v : Value) → Dec (wf v)
  wf? ω = yes wf-ω
  wf? ν = yes wf-ν
  wf? (const k) = yes (wf-const k)
  wf? (v ⊔ v₁) with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (proj₁ (proj₂ (wf-⊔-inv z))))
  ... | yes wfv with wf? v₁
  ... | no ¬wfv₁ = no (λ z → ¬wfv₁ (proj₂ (proj₂ (wf-⊔-inv z))))
  ... | yes wfv₁ with v ~? v₁
  ... | no ¬v~v₁ = no (λ z → ¬v~v₁ (proj₁ (wf-⊔-inv z)))
  ... | yes v~v₁ = yes (wf-⊔ v~v₁ wfv wfv₁) 
  wf? (v ↦ v₁) with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (proj₁ (wf-fun-inv z)))
  ... | yes wfv with wf? v₁
  ... | no ¬wfv₁ = no λ z → ¬wfv₁ (proj₂ (wf-fun-inv z))
  ... | yes wfv₁ = yes (wf-fun wfv wfv₁)
  wf? (⦅ v ∣) with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (wf-fst-inv z))
  ... | yes wfv = yes (wf-fst wfv)
  wf? (∣ v ⦆) with wf? v
  ... | no ¬wfv = no (λ z → ¬wfv (wf-snd-inv z))
  ... | yes wfv = yes (wf-snd wfv)
  wf? (∥ [] ∥) = yes wf-nil
  wf? ∥ v ∷ vs ∥ = wf-tup? (v ∷ vs)
    where
    wf-tup? : ∀ {n} (vs : Vec Value n) → Dec (wf ∥ vs ∥)
    wf-tup? [] = yes wf-nil
    wf-tup? (x ∷ vs) with wf? x
    ... | no ¬wfx = no (λ z → ¬wfx (proj₁ (wf-tup-inv z)))
    ... | yes wfx with wf-tup? vs
    ... | no ¬wfvs = no (λ z → ¬wfvs (proj₂ (wf-tup-inv z)))
    ... | yes wfvs = yes (wf-tup wfx wfvs)
  wf? (left d) with wf? d
  ... | no ¬wfd = no (λ z → ¬wfd (wf-left-inv z))
  ... | yes wfd = yes (wf-left wfd)
  wf? (right d) with wf? d
  ... | no ¬wfd = no (λ z → ¬wfd (wf-right-inv z))
  ... | yes wfd = yes (wf-right wfd)

  sc-å : ∀ v → Atomic v → sc v
  sc-å ω åv = tt
  sc-å ν åv = tt
  sc-å (const {B} k) åv with base-eq? B B
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl with base-rep-eq? k k
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl = refl
  sc-å (v ↦ v₁) åv₁ = inj₂ (sc-å v₁ åv₁)
  sc-å ⦅ d ∣ åd = sc-å d åd
  sc-å ∣ d ⦆ åd = sc-å d åd
  sc-å (∥ [] ∥) åv = tt
  sc-å ∥ x ∷ vs ∥ åv = ⟨ sc-å x (proj₁ åv) , sc-å ∥ vs ∥ (proj₂ åv) ⟩
  sc-å (left d) åd = sc-å d åd
  sc-å (right d) åd = sc-å d åd

  sc-⊔ : ∀ u v → sc u → sc v → u ~ v → sc (u ⊔ v)
  sc-⊔ u v scu scv u~v = ~-⊔-cong {u}{v}{u}{v} scu u~v (~-sym u v u~v) scv
  
  sc-↦ : ∀ u v → ((¬ (sc u)) ⊎ sc v) → sc (u ↦ v)
  sc-↦ u v (inj₁ x) = inj₁ x
  sc-↦ u v (inj₂ y) = inj₂ y

  sc-split : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → sc v₁ → sc v₂ → v₁ ~ v₂ → sc v
  sc-split (split-⊔ {v₁}{v₂}) scL scR L~R = sc-⊔ v₁ v₂ scL scR L~R
  sc-split (split-↦ split) (inj₁ x) (inj₁ x₁) L~R = inj₁ x₁
  sc-split (split-↦ split) (inj₁ x) (inj₂ y) L~R = inj₁ x
  sc-split (split-↦ split) (inj₂ y) (inj₁ x) L~R = inj₁ x
  sc-split (split-↦ split) (inj₂ y) (inj₂ y₁) (inj₁ x)  = inj₁ x
  sc-split (split-↦ split) (inj₂ y) (inj₂ y₁) (inj₂ y₂) = inj₂ (sc-split split y y₁ y₂)
  sc-split (split-fst split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂
  sc-split (split-snd split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂
  sc-split (split-tup-head split) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ ⟨ fst₂ , snd₂ ⟩ = ⟨ sc-split split fst fst₁ fst₂ , snd₂ ⟩
  sc-split (split-tup-tail x split) ⟨ fst , snd ⟩ ⟨ fst₁ , snd₁ ⟩ ⟨ fst₂ , snd₂ ⟩ = ⟨ fst₂ , sc-split split snd snd₁ snd₂ ⟩
  sc-split (split-left split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂
  sc-split (split-right split) scd₁ scd₂ d₁~d₂ = sc-split split scd₁ scd₂ d₁~d₂

  sc-split-inv : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → sc v → sc v₁ × sc v₂ × v₁ ~ v₂
  sc-split-inv (split-⊔ {v₁}{v₂}) ⟨ fst , snd ⟩ = ⟨ proj₁ (~-⊔-R-inv v₁ fst) , ⟨ proj₂ (~-⊔-R-inv v₂ snd) , proj₂ (~-⊔-R-inv v₁ fst) ⟩ ⟩
  sc-split-inv (split-↦ split) (inj₁ ¬scu) = ⟨ inj₁ ¬scu  , ⟨ inj₁ ¬scu , inj₁ ¬scu ⟩ ⟩
  sc-split-inv (split-↦ split) (inj₂ scv) with sc-split-inv split scv
  ... | ⟨ scv₁ , ⟨ scv₂ , v₁~v₂ ⟩ ⟩  = ⟨ inj₂ scv₁ , ⟨ inj₂ scv₂ , inj₂ v₁~v₂ ⟩ ⟩
  sc-split-inv (split-fst split) scd = sc-split-inv split scd
  sc-split-inv (split-snd split) scd = sc-split-inv split scd
  sc-split-inv (split-tup-head split) ⟨ fst , snd ⟩ with sc-split-inv split fst
  ... | ⟨ scv₁ , ⟨ scv₂ , v₁~v₂ ⟩ ⟩  = ⟨ ⟨ scv₁ , snd ⟩ , ⟨ ⟨ scv₂ , snd ⟩ , ⟨ v₁~v₂ , snd ⟩ ⟩ ⟩
  sc-split-inv (split-tup-tail x split) ⟨ fst , snd ⟩ with sc-split-inv split snd
  ... | ⟨ scv₁ , ⟨ scv₂ , v₁~v₂ ⟩ ⟩  = ⟨ ⟨ fst , scv₁ ⟩ , ⟨ ⟨ fst , scv₂ ⟩ , ⟨ fst , v₁~v₂ ⟩ ⟩ ⟩
  sc-split-inv (split-left split) scd = sc-split-inv split scd
  sc-split-inv (split-right split) scd = sc-split-inv split scd

  ~-refl : ∀ {v} → wf v → v ~ v
  ~-refl wf-ω = tt
  ~-refl wf-ν = tt
  ~-refl (wf-const {B} k) with base-eq? B B
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl = refl
  ~-refl (wf-fun wfv wfv₁) = inj₂ (~-refl wfv₁)
  ~-refl (wf-⊔ {u}{v} u~v wfv wfv₁) = 
    ~-⊔-cong {u}{v}{u}{v} (~-refl wfv) u~v (~-sym u v u~v) (~-refl wfv₁)
  ~-refl (wf-fst wfd) = ~-refl wfd
  ~-refl (wf-snd wfd) = ~-refl wfd
  ~-refl wf-nil = tt
  ~-refl (wf-tup wfv wfv₁) = ⟨ ~-refl wfv , ~-refl wfv₁ ⟩
  ~-refl (wf-left wfd) = ~-refl wfd
  ~-refl (wf-right wfd) = ~-refl wfd



  wf→sc : ∀ v → wf v → v ~ v
  wf→sc v wfv = ~-refl wfv

  wf-split : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → v₁ ~ v₂ → wf v₁ → wf v₂ → wf v
  wf-split split-⊔ = wf-⊔
  wf-split (split-↦ split) (inj₁ x) (wf-fun wfL wfL₁) (wf-fun wfR wfR₁) 
    = ⊥-elim (x (~-refl wfR))
  wf-split (split-↦ split) (inj₂ y) (wf-fun wfL wfL₁) (wf-fun wfR wfR₁) 
    = wf-fun wfR (wf-split split y wfL₁ wfR₁)
  wf-split (split-fst split) ~fst (wf-fst wfL) (wf-fst wfR) = wf-fst (wf-split split ~fst wfL wfR)
  wf-split (split-snd split) ~snd (wf-snd wfL) (wf-snd wfR) = wf-snd (wf-split split ~snd wfL wfR)
  wf-split (split-tup-head split) ⟨ fst , snd ⟩ (wf-tup wfL wfL₁) (wf-tup wfR wfR₁) = wf-tup (wf-split split fst wfL wfR) wfR₁
  wf-split (split-tup-tail x split) ⟨ fst , snd ⟩ (wf-tup wfL wfL₁) (wf-tup wfR wfR₁) = wf-tup wfR (wf-split split snd wfL₁ wfR₁)
  wf-split (split-left split) d₁~d₂ (wf-left wfd₁) (wf-left wfd₂) = wf-left (wf-split split  d₁~d₂ wfd₁ wfd₂)
  wf-split (split-right split) d₁~d₂ (wf-right wfd₁) (wf-right wfd₂) = wf-right (wf-split split  d₁~d₂ wfd₁ wfd₂)

  wf-split-inv : ∀ {v v₁ v₂} → v₁ ◃ v ▹ v₂ → wf v → v₁ ~ v₂ × wf v₁ × wf v₂
  wf-split-inv split-⊔ wfv = wf-⊔-inv wfv
  wf-split-inv (split-↦ split) (wf-fun wfv wfv₁) = 
    ⟨ inj₂ (proj₁ (wf-split-inv split wfv₁)) , ⟨ wf-fun wfv (proj₁ (proj₂ (wf-split-inv split wfv₁))) 
    , wf-fun wfv (proj₂ (proj₂ (wf-split-inv split wfv₁))) ⟩ ⟩
  wf-split-inv (split-fst split) (wf-fst wfv) = 
    ⟨ proj₁ (wf-split-inv split wfv) , ⟨ wf-fst (proj₁ (proj₂ (wf-split-inv split wfv))) 
    , wf-fst (proj₂ (proj₂ (wf-split-inv split wfv))) ⟩ ⟩
  wf-split-inv (split-snd split) (wf-snd wfv) = 
    ⟨ proj₁ (wf-split-inv split wfv) , ⟨ wf-snd (proj₁ (proj₂ (wf-split-inv split wfv))) 
    , wf-snd (proj₂ (proj₂ (wf-split-inv split wfv))) ⟩ ⟩
  wf-split-inv (split-tup-head split) (wf-tup wfv wfv₁) =
    ⟨ ⟨ proj₁ (wf-split-inv split wfv) , ~-refl wfv₁ ⟩ , ⟨ wf-tup (proj₁ (proj₂ (wf-split-inv split wfv))) wfv₁ 
    , wf-tup (proj₂ (proj₂ (wf-split-inv split wfv))) wfv₁ ⟩ ⟩
  wf-split-inv (split-tup-tail x split) (wf-tup wfv wfv₁) =
    ⟨ ⟨ ~-refl wfv , proj₁ (wf-split-inv split wfv₁) ⟩ , ⟨ wf-tup wfv (proj₁ (proj₂ (wf-split-inv split wfv₁))) 
    , wf-tup wfv (proj₂ (proj₂ (wf-split-inv split wfv₁))) ⟩ ⟩
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
  consistent-⊑-lemma ⊑-ν-ν ν u~v = tt
  consistent-⊑-lemma ⊑-ν-ν (v ⊔ v₁) u~v = 
    ⟨ consistent-⊑-lemma ⊑-ν-ν v (proj₁ u~v) , consistent-⊑-lemma ⊑-ν-ν v₁ (proj₂ u~v) ⟩
  consistent-⊑-lemma ⊑-ν-ν (v₁ ↦ v₂) u~v = tt
  consistent-⊑-lemma ⊑-ν-↦ ω u~v = tt
  consistent-⊑-lemma ⊑-ν-↦ ν u~v = tt
  consistent-⊑-lemma ⊑-ν-↦ (v ⊔ v₁) ⟨ fst , snd ⟩ = 
    ⟨ consistent-⊑-lemma ⊑-ν-↦ v fst , consistent-⊑-lemma ⊑-ν-↦ v₁ snd ⟩
  consistent-⊑-lemma ⊑-ν-↦ (v ↦ v₁) u~v = tt
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
  consistent-⊑-lemma ⊑-nil v u~v = u~v
  consistent-⊑-lemma (⊑-tup-å åus ⊑u ⊑u₁) ω u~v = tt
  consistent-⊑-lemma (⊑-tup-å åus ⊑u ⊑u₁) (v ⊔ v₁) ⟨ fst , snd ⟩ = 
    ⟨ consistent-⊑-lemma (⊑-tup-å åus ⊑u ⊑u₁) v fst 
    , consistent-⊑-lemma (⊑-tup-å åus ⊑u ⊑u₁) v₁ snd ⟩
  consistent-⊑-lemma (⊑-tup-å åus ⊑u ⊑u₁) ∥ x ∷ vs ∥ ⟨ fst , snd ⟩ = 
    ⟨ consistent-⊑-lemma ⊑u x fst , consistent-⊑-lemma ⊑u₁ ∥ vs ∥ snd ⟩
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) ω u~v = tt
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) ν u~v = tt
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) (v ⊔ v₁) ⟨ fst , snd ⟩ = 
    ⟨ consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) v fst
    , consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) v₁ snd ⟩
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) (v ↦ v₁) (inj₁ x) = 
    inj₁ (λ u₁~v → x (consistent-⊑-lemma ⊑u₁ v u₁~v)) 
  consistent-⊑-lemma (⊑-↦-å åu₂ ⊑u ⊑u₁) (v ↦ v₁) (inj₂ y) = 
    inj₂ (consistent-⊑-lemma ⊑u v₁ y)
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
    ; wf-fun = wf-fun
    ; wf-fun-inv = wf-fun-inv
    ; ~-refl = λ {v}{wfv} → ~-refl wfv
    ; ~-sym = λ {u}{v} → ~-sym u v
    ; ~-⊑ = consistent-⊑
    ; ~-↦-cong = λ _ → inj₂
    ; ~-↦ = λ {v}{w}{v'}{w'} → ~-↦ {v}{w}{v'}{w'}
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
