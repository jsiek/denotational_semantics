
open import Function using (_∘_)
open import Data.Nat using (ℕ; suc ; zero; _+_; _≤′_; _<′_; _<_; _≤_;
    z≤n; s≤s; ≤′-refl; ≤′-step) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ≤-step; ⊔-mono-≤;
         +-mono-≤; +-mono-≤-<; +-mono-<-≤; +-comm; +-assoc; n≤1+n;
         ≤-pred; m≤m+n; m≤n+m; ≤-reflexive; ≤′⇒≤; ≤⇒≤′; +-suc)
open Data.Nat.Properties.≤-Reasoning using (begin_; _∎; step-≤)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.List using (List; _∷_ ; []; _++_)
open import Data.Vec using (Vec; []; _∷_; length; head; tail; lookup; zipWith)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using (Pointwise; []; _∷_; head; tail; uncons)
open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
    renaming (begin_ to start_; _∎ to _□)

module Model.Filter.DomainISWIMOrdering where

  open import Model.Filter.DomainUtil
  open import Primitives
  open import Model.Filter.DomainISWIMValues


  infix 5 _⊑_

  data _⊑_ : (u v : Value) → Set where

    {- Atomic Rules :  we use å (\aa) as an abbreviation for atomic -}

    ⊑-ω : ∀ {v} → ω ⊑ v
  
    ⊑-ν-ν : ν ⊑ ν

    ⊑-ν-↦ : ∀ {v w} → ν ⊑ v ↦ w

    ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k

    ⊑-⊔-R1-å : ∀ {u v w}
       → (åu : Atomic u)     {- unnecessary, but clarifies which rule to use -}
       → u ⊑ v
         ------------------
       → u ⊑ v ⊔ w

    ⊑-⊔-R2-å : ∀ {u v w}
       → (åu : Atomic u)     {- ditto -}
       → u ⊑ w
         -----------
       → u ⊑ v ⊔ w

    ⊑-pair-å : ∀ {u₁ u₂ v₁ v₂}
       → (åfst : Atomic u₁)
       → (åsnd : Atomic u₂)
       → (⊑fst : u₁ ⊑ v₁)
       → (⊑snd : u₂ ⊑ v₂)
        ------------------
       → ⦅ u₁ , u₂ ⦆ ⊑ ⦅ v₁ , v₂ ⦆

    ⊑-nil : ∥ [] ∥ ⊑ ∥ [] ∥
  
    ⊑-tup-å : ∀ {n u v us vs}
       → (åus : Atomic-tup {suc n} (u ∷ us))
       → (u⊑v : u ⊑ v)
       → (us⊑vs : ∥ us ∥ ⊑ ∥_∥ {n} vs)
       ------------------------------
       → ∥ u ∷ us ∥ ⊑ ∥ v ∷ vs ∥

    ⊑-↦-å : ∀ {u₁ u₂ v₁ v₂}
       → (åu₂ : Atomic u₂)
       → (⊑cod : u₂ ⊑ v₂)
       → (dom⊑ : v₁ ⊑ u₁)
       ------------------
       → u₁ ↦ u₂ ⊑ v₁ ↦ v₂ 

    ⊑-left-å : ∀ {u v}
      → (åu : Atomic u)
      → (u⊑v : u ⊑ v)
      -------------------
      → left u ⊑ left v

    ⊑-right-å : ∀ {u v}
      → (åu : Atomic u)
      → (u⊑v : u ⊑ v)
      -------------------
      → right u ⊑ right v

  {- Splittable values are split until atoms can be compared -}
    ⊑-split : ∀ {u u₁ u₂ v}
       → (split : u₁ ◃ u ▹ u₂)
       → (⊑L : u₁ ⊑ v)
       → (⊑R : u₂ ⊑ v)
      -------------
       → u ⊑ v


  ⊑-⊔-R1 : ∀ {u v₁ v₂} → u ⊑ v₁ → u ⊑ v₁ ⊔ v₂
  ⊑-⊔-R1 ⊑-ω = ⊑-ω
  ⊑-⊔-R1 ⊑-ν-ν = ⊑-⊔-R1-å tt ⊑-ν-ν
  ⊑-⊔-R1 ⊑-ν-↦ = ⊑-⊔-R1-å tt ⊑-ν-↦
  ⊑-⊔-R1 ⊑-const = ⊑-⊔-R1-å tt ⊑-const
  ⊑-⊔-R1 (⊑-⊔-R1-å åu u⊑v₁) = ⊑-⊔-R1-å åu (⊑-⊔-R1 u⊑v₁)
  ⊑-⊔-R1 (⊑-⊔-R2-å åu u⊑v₁) = ⊑-⊔-R1-å åu (⊑-⊔-R2-å åu u⊑v₁)
  ⊑-⊔-R1 (⊑-pair-å åfst åsnd u⊑v₁ u⊑v₂) = ⊑-⊔-R1-å ⟨ åfst , åsnd ⟩ (⊑-pair-å åfst åsnd u⊑v₁ u⊑v₂)
  ⊑-⊔-R1 ⊑-nil = ⊑-⊔-R1-å tt ⊑-nil
  ⊑-⊔-R1 (⊑-tup-å åus u⊑v₁ us[⊑]vs) = ⊑-⊔-R1-å åus (⊑-tup-å åus u⊑v₁ us[⊑]vs)
  ⊑-⊔-R1 (⊑-↦-å åu₂ u⊑v₁ u⊑v₂) = ⊑-⊔-R1-å åu₂ (⊑-↦-å åu₂ u⊑v₁ u⊑v₂)
  ⊑-⊔-R1 (⊑-left-å åu q) = ⊑-⊔-R1-å åu (⊑-left-å åu q)
  ⊑-⊔-R1 (⊑-right-å åu q) = ⊑-⊔-R1-å åu (⊑-right-å åu q)
  ⊑-⊔-R1 (⊑-split split u⊑v₁ u⊑v₂) = ⊑-split split (⊑-⊔-R1 u⊑v₁) (⊑-⊔-R1 u⊑v₂)


  ⊑-⊔-R2 : ∀ {u v₁ v₂} → u ⊑ v₂ → u ⊑ v₁ ⊔ v₂
  ⊑-⊔-R2 ⊑-ω = ⊑-ω
  ⊑-⊔-R2 ⊑-ν-ν = ⊑-⊔-R2-å tt ⊑-ν-ν
  ⊑-⊔-R2 ⊑-ν-↦ = ⊑-⊔-R2-å tt ⊑-ν-↦
  ⊑-⊔-R2 ⊑-const = ⊑-⊔-R2-å tt ⊑-const
  ⊑-⊔-R2 (⊑-⊔-R1-å åu u⊑v₂) = ⊑-⊔-R2-å åu (⊑-⊔-R1-å åu u⊑v₂)
  ⊑-⊔-R2 (⊑-⊔-R2-å åu u⊑v₂) = ⊑-⊔-R2-å åu (⊑-⊔-R2 u⊑v₂)
  ⊑-⊔-R2 (⊑-pair-å åfst åsnd u⊑v₂ u⊑v₃) = ⊑-⊔-R2-å ⟨ åfst , åsnd ⟩ (⊑-pair-å åfst åsnd u⊑v₂ u⊑v₃)
  ⊑-⊔-R2 ⊑-nil = ⊑-⊔-R2-å tt ⊑-nil
  ⊑-⊔-R2 (⊑-tup-å åus u⊑v₂ us[⊑]vs) = ⊑-⊔-R2-å åus (⊑-tup-å åus u⊑v₂ us[⊑]vs)
  ⊑-⊔-R2 (⊑-↦-å åu₂ u⊑v₂ u⊑v₃) = ⊑-⊔-R2-å åu₂ (⊑-↦-å åu₂ u⊑v₂ u⊑v₃)
  ⊑-⊔-R2 (⊑-left-å åu q) = ⊑-⊔-R2-å åu (⊑-left-å åu q)
  ⊑-⊔-R2 (⊑-right-å åu q) = ⊑-⊔-R2-å åu (⊑-right-å åu q)
  ⊑-⊔-R2 (⊑-split split u⊑v₂ u⊑v₃) = ⊑-split split (⊑-⊔-R2 u⊑v₂) (⊑-⊔-R2 u⊑v₃)

  ⊑-⊔-L : ∀ {u₁ u₂ v} → u₁ ⊑ v → u₂ ⊑ v → u₁ ⊔ u₂ ⊑ v
  ⊑-⊔-L 1⊑ 2⊑ = ⊑-split split-⊔ 1⊑ 2⊑

  ⊑-pair : ∀ {u₁ u₂ v₁ v₂} → u₁ ⊑ v₁ → u₂ ⊑ v₂ → ⦅ u₁ , u₂ ⦆ ⊑ ⦅ v₁ , v₂ ⦆
  ⊑-pair {u₁} {u₂} {v₁} {v₂} ⊑fst ⊑snd with atomic? u₁
  ... | yes åu₁ with ⊑snd 
  ... | ⊑-ω = ⊑-pair-å åu₁ tt ⊑fst ⊑snd
  ... | ⊑-ν-ν = ⊑-pair-å åu₁ tt ⊑fst ⊑snd
  ... | ⊑-ν-↦ = ⊑-pair-å åu₁ tt ⊑fst ⊑snd
  ... | ⊑-const = ⊑-pair-å åu₁ tt ⊑fst ⊑snd
  ... | ⊑-⊔-R1-å åu q = ⊑-pair-å åu₁ åu ⊑fst ⊑snd
  ... | ⊑-⊔-R2-å åu q = ⊑-pair-å åu₁ åu ⊑fst ⊑snd
  ... | ⊑-pair-å åfst åsnd q q₁ = ⊑-pair-å åu₁ ⟨ åfst , åsnd ⟩ ⊑fst ⊑snd
  ... | ⊑-nil = ⊑-pair-å åu₁ tt ⊑fst ⊑snd
  ... | ⊑-tup-å åus q us[⊑]vs = ⊑-pair-å åu₁ åus ⊑fst ⊑snd
  ... | ⊑-↦-å åu₂ q q₁ = ⊑-pair-å åu₁ åu₂ ⊑fst ⊑snd
  ... | ⊑-left-å åu q = ⊑-pair-å åu₁ åu ⊑fst ⊑snd
  ... | ⊑-right-å åu q = ⊑-pair-å åu₁ åu ⊑fst ⊑snd
  ... | ⊑-split {u₁ = u₂1} {u₂ = u₂2} split q q₁ = 
    ⊑-split (split-pair-snd åu₁ split) (⊑-pair ⊑fst q) (⊑-pair ⊑fst q₁)
  ⊑-pair {u₁} {u₂} ⊑fst ⊑snd | no ¬åu₁ with ⊑fst
  ... | ⊑-ω = ⊥-elim (¬åu₁ tt)
  ... | ⊑-ν-ν = ⊥-elim (¬åu₁ tt)
  ... | ⊑-ν-↦ = ⊥-elim (¬åu₁ tt)
  ... | ⊑-const = ⊥-elim (¬åu₁ tt)
  ... | ⊑-⊔-R1-å åu q = ⊥-elim (¬åu₁ åu)
  ... | ⊑-⊔-R2-å åu q = ⊥-elim (¬åu₁ åu)
  ... | ⊑-pair-å åfst åsnd q q₁ = ⊥-elim (¬åu₁ ⟨ åfst , åsnd ⟩)
  ... | ⊑-nil = ⊥-elim (¬åu₁ tt)
  ... | ⊑-tup-å åus q us[⊑]vs = ⊥-elim (¬åu₁ åus)
  ... | ⊑-↦-å åu₂ q q₁ = ⊥-elim (¬åu₁ åu₂)
  ... | ⊑-left-å åu q = ⊥-elim (¬åu₁ åu)
  ... | ⊑-right-å åu q = ⊥-elim (¬åu₁ åu)
  ... | ⊑-split split q q₁ = ⊑-split (split-pair-fst split) (⊑-pair q ⊑snd) (⊑-pair q₁ ⊑snd)



  ⊑-tup : ∀ {n u v} {us vs : Vec Value n} → u ⊑ v → ∥ us ∥ ⊑ ∥ vs ∥ → ∥ u ∷ us ∥ ⊑ ∥ v ∷ vs ∥
  ⊑-tup {u = u} {us = us} u⊑v us⊑vs with atomic? u
  ... | yes åu with us⊑vs 
  ... | ⊑-nil = ⊑-tup-å ⟨ åu , tt ⟩ u⊑v ⊑-nil
  ... | ⊑-tup-å åus q us[⊑]vs = ⊑-tup-å ⟨ åu , åus ⟩ u⊑v us⊑vs
  ... | ⊑-split (split-tup-head x) q q₁ = ⊑-split (split-tup-tail åu (split-tup-head x)) (⊑-tup u⊑v q) (⊑-tup u⊑v q₁)
  ... | ⊑-split (split-tup-tail x x₁) q q₁ = ⊑-split (split-tup-tail åu (split-tup-tail x x₁)) (⊑-tup u⊑v q) (⊑-tup u⊑v q₁)
  ⊑-tup {u = u} {us = us} u⊑v us⊑vs | no ¬åu with u⊑v
  ... | ⊑-ω = ⊥-elim (¬åu tt)
  ... | ⊑-ν-ν = ⊥-elim (¬åu tt)
  ... | ⊑-ν-↦ = ⊥-elim (¬åu tt)
  ... | ⊑-const = ⊥-elim (¬åu tt)
  ... | ⊑-⊔-R1-å åu u⊑v₁ = ⊥-elim (¬åu åu)
  ... | ⊑-⊔-R2-å åu u⊑v₁ = ⊥-elim (¬åu åu)
  ... | ⊑-pair-å åfst åsnd u⊑v₁ u⊑v₂ = ⊥-elim (¬åu ⟨ åfst , åsnd ⟩)
  ... | ⊑-nil = ⊥-elim (¬åu tt)
  ... | ⊑-tup-å åus u⊑v₁ us[⊑]vs = ⊥-elim (¬åu åus)
  ... | ⊑-↦-å åu₂ u⊑v₁ u⊑v₂ = ⊥-elim (¬åu åu₂)
  ... | ⊑-left-å åu q = ⊥-elim (¬åu åu)
  ... | ⊑-right-å åu q = ⊥-elim (¬åu åu)
  ... | ⊑-split split u⊑v₁ u⊑v₂ = ⊑-split (split-tup-head split) (⊑-tup u⊑v₁ us⊑vs) (⊑-tup u⊑v₂ us⊑vs)

  ⊑-↦ : ∀ {u₁ u₂ v₁ v₂} → v₁ ⊑ u₁ →  u₂ ⊑ v₂ → u₁ ↦ u₂ ⊑ v₁ ↦ v₂
  ⊑-↦ {u₁}{u₂} dom⊑ ⊑cod with atomic? u₂
  ... | yes åu₂ = ⊑-↦-å åu₂ ⊑cod dom⊑
  ... | no ¬åu₂ with ⊑cod 
  ... | ⊑-ω = ⊥-elim (¬åu₂ tt)
  ... | ⊑-ν-ν = ⊥-elim (¬åu₂ tt)
  ... | ⊑-ν-↦ = ⊥-elim (¬åu₂ tt)
  ... | ⊑-const = ⊥-elim (¬åu₂ tt)
  ... | ⊑-⊔-R1-å åu u₂⊑v₂ = ⊥-elim (¬åu₂ åu)
  ... | ⊑-⊔-R2-å åu u₂⊑v₂ = ⊥-elim (¬åu₂ åu)
  ... | ⊑-pair-å åfst åsnd u₂⊑v₂ u₂⊑v₃ = ⊥-elim (¬åu₂ ⟨ åfst , åsnd ⟩)
  ... | ⊑-nil = ⊥-elim (¬åu₂ tt)
  ... | ⊑-tup-å åus u₂⊑v₂ us[⊑]vs = ⊥-elim (¬åu₂ åus)
  ... | ⊑-↦-å åu₂ u₂⊑v₂ u₂⊑v₃ = ⊥-elim (¬åu₂ åu₂)
  ... | ⊑-left-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-right-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-split split u₂⊑v₂ u₂⊑v₃ = ⊑-split (split-↦ split) (⊑-↦ dom⊑ u₂⊑v₂) (⊑-↦ dom⊑ u₂⊑v₃)

  ⊑-left : ∀ {u v} → u ⊑ v → left u ⊑ left v
  ⊑-left ⊑-ω = ⊑-left-å tt ⊑-ω
  ⊑-left ⊑-ν-ν = ⊑-left-å tt ⊑-ν-ν
  ⊑-left ⊑-ν-↦ = ⊑-left-å tt ⊑-ν-↦
  ⊑-left ⊑-const = ⊑-left-å tt ⊑-const
  ⊑-left (⊑-⊔-R1-å åu u⊑v) = ⊑-left-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-left (⊑-⊔-R2-å åu u⊑v) = ⊑-left-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-left (⊑-pair-å åfst åsnd u⊑v u⊑v₁) = ⊑-left-å ⟨ åfst , åsnd ⟩ (⊑-pair-å åfst åsnd u⊑v u⊑v₁)
  ⊑-left ⊑-nil = ⊑-left-å tt ⊑-nil
  ⊑-left (⊑-tup-å åus u⊑v u⊑v₁) = ⊑-left-å åus (⊑-tup-å åus u⊑v u⊑v₁)
  ⊑-left (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-left-å åu₂ (⊑-↦-å åu₂ u⊑v u⊑v₁)
  ⊑-left (⊑-left-å åu u⊑v) = ⊑-left-å åu (⊑-left u⊑v)
  ⊑-left (⊑-right-å åu u⊑v) = ⊑-left-å åu (⊑-right-å åu u⊑v)
  ⊑-left (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-left split) (⊑-left u⊑v) (⊑-left u⊑v₁)

  ⊑-right : ∀ {u v} → u ⊑ v → right u ⊑ right v
  ⊑-right ⊑-ω = ⊑-right-å tt ⊑-ω
  ⊑-right ⊑-ν-ν = ⊑-right-å tt ⊑-ν-ν
  ⊑-right ⊑-ν-↦ = ⊑-right-å tt ⊑-ν-↦
  ⊑-right ⊑-const = ⊑-right-å tt ⊑-const
  ⊑-right (⊑-⊔-R1-å åu u⊑v) = ⊑-right-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-right (⊑-⊔-R2-å åu u⊑v) = ⊑-right-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-right (⊑-pair-å åfst åsnd u⊑v u⊑v₁) = ⊑-right-å ⟨ åfst , åsnd ⟩ (⊑-pair-å åfst åsnd u⊑v u⊑v₁)
  ⊑-right ⊑-nil = ⊑-right-å tt ⊑-nil
  ⊑-right (⊑-tup-å åus u⊑v u⊑v₁) = ⊑-right-å åus (⊑-tup-å åus u⊑v u⊑v₁)
  ⊑-right (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-right-å åu₂ (⊑-↦-å åu₂ u⊑v u⊑v₁)
  ⊑-right (⊑-left-å åu u⊑v) = ⊑-right-å åu (⊑-left-å åu u⊑v)
  ⊑-right (⊑-right-å åu u⊑v) = ⊑-right-å åu (⊑-right u⊑v)
  ⊑-right (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-right split) (⊑-right u⊑v) (⊑-right u⊑v₁)

  ⊑-refl : ∀ {v} → v ⊑ v
  ⊑-refl {ω} = ⊑-ω
  ⊑-refl {ν} = ⊑-ν-ν
  ⊑-refl {const k} = ⊑-const
  ⊑-refl {⦅ v , v₁ ⦆} = ⊑-pair ⊑-refl ⊑-refl
  ⊑-refl {∥ [] ∥} = ⊑-nil
  ⊑-refl {∥ v ∷ vs ∥} = ⊑-tup ⊑-refl ⊑-refl
  ⊑-refl {v ↦ v₁} = ⊑-↦ ⊑-refl ⊑-refl
  ⊑-refl {v ⊔ v₁} = ⊑-⊔-L (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl)
  ⊑-refl {left d} = ⊑-left ⊑-refl
  ⊑-refl {right d} = ⊑-right ⊑-refl

  split-inv-↦ : ∀ {u u'} → Proper (u ↦ u') → Proper u × Proper u'
  split-inv-↦ (⊢'-↦-å P↦ P↦₁ åv₂) = ⟨ P↦₁ , P↦ ⟩
  split-inv-↦ {u} {u'} (⊢'-split (vL ↦ v₁) (vR ↦ v₂) (split-↦ split) P↦ P↦₁) = 
    ⟨ proj₁ (split-inv-↦ P↦₁) , ⊢'-split v₁ v₂ split (proj₂ (split-inv-↦ P↦)) (proj₂ (split-inv-↦ P↦₁)) ⟩

  split-inv-pair : ∀ {u u'} → Proper (⦅ u , u' ⦆) → Proper u × Proper u'
  split-inv-pair (⊢'-pair-å Ppair Ppair₁ åv₁ åv₂) = ⟨ Ppair , Ppair₁ ⟩
  split-inv-pair (⊢'-split (⦅ uL , u' ⦆) (⦅ uR , u' ⦆) (split-pair-fst split) Ppair Ppair₁) = 
    ⟨ ⊢'-split uL uR split (proj₁ (split-inv-pair Ppair)) (proj₁ (split-inv-pair Ppair₁)) , proj₂ (split-inv-pair Ppair₁) ⟩
  split-inv-pair (⊢'-split (⦅ u , u'L ⦆) (⦅ u , u'R ⦆) (split-pair-snd x split) Ppair Ppair₁) = 
    ⟨ proj₁ (split-inv-pair Ppair₁) , ⊢'-split u'L u'R split (proj₂ (split-inv-pair Ppair)) (proj₂ (split-inv-pair Ppair₁)) ⟩

  split-inv-tup : ∀ {n u us} → Proper (∥_∥ {suc n} (u ∷ us)) → Proper u × Proper (∥ us ∥)
  split-inv-tup (⊢'-tup-å Ptup Ptup₁ åv åvs) = ⟨ Ptup , Ptup₁ ⟩
  split-inv-tup (⊢'-split (∥ vL ∷ vs ∥) (∥ vR ∷ vs ∥) (split-tup-head split) Ptup Ptup₁) = 
    ⟨ ⊢'-split vL vR split (proj₁ (split-inv-tup Ptup)) (proj₁ (split-inv-tup Ptup₁)) , proj₂ (split-inv-tup Ptup₁) ⟩
  split-inv-tup (⊢'-split (∥ v ∷ vsL ∥) (∥ v ∷ vsR ∥) (split-tup-tail x split) Ptup Ptup₁) = 
    ⟨ proj₁ (split-inv-tup Ptup₁) , ⊢'-split (∥ vsL ∥) (∥ vsR ∥) split (proj₂ (split-inv-tup Ptup)) (proj₂ (split-inv-tup Ptup₁)) ⟩

  split-inv-⊔ : ∀ {u v} → Proper (u ⊔ v) → Proper u × Proper v
  split-inv-⊔ (⊢'-split vL vR split-⊔ P⊔ P⊔₁) = ⟨ P⊔ , P⊔₁ ⟩

  split-unique : ∀ {u uL uR} → uL ◃ u ▹ uR → ∀ {uL' uR'} → uL' ◃ u ▹ uR' → uL' ≡ uL × uR' ≡ uR
  split-unique split-⊔ split-⊔ = ⟨ refl , refl ⟩
  split-unique {u = u ↦ u₁} (split-↦ split) (split-↦ split') with split-unique split split'
  ... | ⟨ H₁ , H₂ ⟩ = ⟨ cong (u ↦_) H₁ , cong (u ↦_) H₂ ⟩
  split-unique {u = ⦅ u , u₁ ⦆} (split-pair-fst split) (split-pair-fst split') with split-unique split split'
  ... | ⟨ H₁ , H₂ ⟩ = ⟨ cong (λ z → ⦅ z , u₁ ⦆) H₁ , cong (λ z → ⦅ z , u₁ ⦆) H₂ ⟩
  split-unique {u = ⦅ u , u₁ ⦆} (split-pair-fst split) (split-pair-snd x split') = ⊥-elim (unsplittable u x split)
  split-unique {u = ⦅ u , u₁ ⦆} (split-pair-snd x split) (split-pair-fst split') = ⊥-elim (unsplittable u x split')
  split-unique {u = ⦅ u , u₁ ⦆} (split-pair-snd x split) (split-pair-snd x₁ split') with split-unique split split'
  ... | ⟨ H₁ , H₂ ⟩ = ⟨ cong (λ z → ⦅ u , z ⦆) H₁ , cong (λ z → ⦅ u , z ⦆) H₂ ⟩
  split-unique {u = ∥ u ∷ us ∥} (split-tup-head split) (split-tup-head split') with split-unique split split'
  ... | ⟨ H₁ , H₂ ⟩ = ⟨ cong (λ z → ∥ z ∷ us ∥) H₁ , cong (λ z → ∥ z ∷ us ∥) H₂ ⟩
  split-unique {u = ∥ u ∷ us ∥} (split-tup-head split) (split-tup-tail x split') = ⊥-elim (unsplittable u x split)
  split-unique {u = ∥ u ∷ us ∥} (split-tup-tail x split) (split-tup-head split') = ⊥-elim (unsplittable u x split')
  split-unique {u = ∥ u ∷ us ∥} (split-tup-tail x split) (split-tup-tail x₁ split') with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = left u} (split-left split) (split-left split') with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = right u} (split-right split) (split-right split') with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩


  ⊑-inversion-split-L : ∀ {u v v₁ v₂} → u ⊑ v → v₁ ◃ v ▹ v₂ → Atomic u → u ⊑ v₁ ⊎ u ⊑ v₂
  ⊑-inversion-split-L ⊑-ω split åu = inj₁ ⊑-ω
  ⊑-inversion-split-L ⊑-ν-↦ (split-↦ split) åu = inj₁ ⊑-ν-↦
  ⊑-inversion-split-L (⊑-⊔-R1-å åu₁ u⊑v) split-⊔ åu = inj₁ u⊑v
  ⊑-inversion-split-L (⊑-⊔-R2-å åu₁ u⊑v) split-⊔ åu = inj₂ u⊑v
  ⊑-inversion-split-L (⊑-pair-å åfst åsnd u⊑v u⊑v₁) (split-pair-fst split) åu 
    with ⊑-inversion-split-L u⊑v split (proj₁ åu)
  ... | inj₁ x = inj₁ (⊑-pair-å åfst åsnd x u⊑v₁)
  ... | inj₂ y = inj₂ (⊑-pair-å åfst åsnd y u⊑v₁)
  ⊑-inversion-split-L (⊑-pair-å åfst åsnd u⊑v u⊑v₁) (split-pair-snd x split) åu 
    with ⊑-inversion-split-L u⊑v₁ split (proj₂ åu)
  ... | inj₁ x = inj₁ (⊑-pair-å åfst åsnd u⊑v x)
  ... | inj₂ y = inj₂ (⊑-pair-å åfst åsnd u⊑v y)
  ⊑-inversion-split-L (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-head split) åu 
    with ⊑-inversion-split-L u⊑v split (proj₁ åu)
  ... | inj₁ x = inj₁ (⊑-tup-å åus x u⊑v₁)
  ... | inj₂ y = inj₂ (⊑-tup-å åus y u⊑v₁)
  ⊑-inversion-split-L (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-tail x split) åu 
    with ⊑-inversion-split-L u⊑v₁ split (proj₂ åu)
  ... | inj₁ x = inj₁ (⊑-tup-å åus u⊑v x)
  ... | inj₂ y = inj₂ (⊑-tup-å åus u⊑v y)
  ⊑-inversion-split-L (⊑-↦-å åu₂ u⊑v u⊑v₁) (split-↦ split) åu 
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-↦-å åu₂ x u⊑v₁)
  ... | inj₂ y = inj₂ (⊑-↦-å åu₂ y u⊑v₁)
  ⊑-inversion-split-L {.(left _)} (⊑-left-å åu₁ u⊑v) (split-left split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-left-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-left-å åu₁ y)
  ⊑-inversion-split-L {.(right _)} (⊑-right-å åu₁ u⊑v) (split-right split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-right-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-right-å åu₁ y)
  ⊑-inversion-split-L {u} (⊑-split split₁ u⊑v u⊑v₁) split åu = ⊥-elim (unsplittable u åu split₁ )



  ⊑-inversion-split-R : ∀ {u v u₁ u₂} → u ⊑ v → u₁ ◃ u ▹ u₂ → u₁ ⊑ v × u₂ ⊑ v
  ⊑-inversion-split-R (⊑-⊔-R1-å åu u⊑v) split with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-⊔-R1 IH₁ , ⊑-⊔-R1 IH₂ ⟩
  ⊑-inversion-split-R (⊑-⊔-R2-å åu u⊑v) split with ⊑-inversion-split-R u⊑v split 
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-⊔-R2 IH₁ , ⊑-⊔-R2 IH₂ ⟩
  ⊑-inversion-split-R (⊑-pair-å åfst åsnd u⊑v u⊑v₁) (split-pair-fst split) 
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-pair IH₁ u⊑v₁ , ⊑-pair IH₂ u⊑v₁ ⟩
  ⊑-inversion-split-R (⊑-pair-å åfst åsnd u⊑v u⊑v₁) (split-pair-snd x split)
    with ⊑-inversion-split-R u⊑v₁ split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-pair u⊑v IH₁ , ⊑-pair u⊑v IH₂ ⟩
  ⊑-inversion-split-R (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-head split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-tup IH₁ u⊑v₁ , ⊑-tup IH₂ u⊑v₁ ⟩
  ⊑-inversion-split-R (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-tail x split)
    with ⊑-inversion-split-R u⊑v₁ split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-tup u⊑v IH₁ , ⊑-tup u⊑v IH₂ ⟩
  ⊑-inversion-split-R (⊑-↦-å åu₂ u⊑v u⊑v₁) (split-↦ split) 
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-↦ u⊑v₁ IH₁ , ⊑-↦ u⊑v₁ IH₂ ⟩
  ⊑-inversion-split-R (⊑-left-å åu u⊑v) (split-left split) 
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-left IH₁ , ⊑-left IH₂ ⟩
  ⊑-inversion-split-R (⊑-right-å åu u⊑v) (split-right split) 
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-right IH₁ , ⊑-right IH₂ ⟩
  ⊑-inversion-split-R {u} {v} (⊑-split split₁ u⊑v u⊑v₁) split 
    with split-unique split₁ split
  ... | ⟨ q , q' ⟩ = ⟨ subst (_⊑ v) (sym q) u⊑v , subst (_⊑ v) (sym q') u⊑v₁ ⟩

  proper-split-L : ∀ {v v₁ v₂} → Proper v → v₁ ◃ v ▹ v₂ → Proper v₁
  proper-split-L .{_ ↦ _} (⊢'-↦-å {v}{v'} Pv Pv₁ åv₂) split = ⊥-elim (unsplittable (v ↦ v') åv₂ split)
  proper-split-L .{⦅ _ , _ ⦆} (⊢'-pair-å {v}{v'} Pv Pv₁ åv₁ åv₂) split = ⊥-elim (unsplittable (⦅ v , v' ⦆) ⟨ åv₁ , åv₂ ⟩ split)
  proper-split-L .{∥ _ ∷ _ ∥} (⊢'-tup-å {n}{v}{vs} Pv Pv₁ åv åvs) split = ⊥-elim (unsplittable (∥ v ∷ vs ∥) ⟨ åv , åvs ⟩ split)
  proper-split-L .{left _} (⊢'-left-å {u} Pu åu) split = ⊥-elim (unsplittable (left u) åu split)
  proper-split-L .{right _} (⊢'-right-å {u} Pu åu) split = ⊥-elim (unsplittable (right u) åu split)
  proper-split-L .{_} (⊢'-split vL vR split₁ Pv Pv₁) split = subst Proper (proj₁ (split-unique split split₁)) Pv

  proper-split-R : ∀ {v v₁ v₂} → Proper v → v₁ ◃ v ▹ v₂ → Proper v₂
  proper-split-R .{_ ↦ _} (⊢'-↦-å {v}{v'} Pv Pv₁ åv₂) split = ⊥-elim (unsplittable (v ↦ v') åv₂ split)
  proper-split-R .{⦅ _ , _ ⦆} (⊢'-pair-å {v}{v'} Pv Pv₁ åv₁ åv₂) split = ⊥-elim (unsplittable (⦅ v , v' ⦆) ⟨ åv₁ , åv₂ ⟩ split)
  proper-split-R .{∥ _ ∷ _ ∥} (⊢'-tup-å {n}{v}{vs} Pv Pv₁ åv åvs) split = ⊥-elim (unsplittable (∥ v ∷ vs ∥) ⟨ åv , åvs ⟩ split)
  proper-split-R .{left _} (⊢'-left-å {u} Pu åu) split = ⊥-elim (unsplittable (left u) åu split)
  proper-split-R .{right _} (⊢'-right-å {u} Pu åu) split = ⊥-elim (unsplittable (right u) åu split)
  proper-split-R .{_} (⊢'-split vL vR split₁ Pv Pv₁) split = subst Proper (proj₂ (split-unique split split₁)) Pv₁


  ⊑-trans-proper : ∀ v → Proper v → ∀ u w → u ⊑ v → v ⊑ w → u ⊑ w
  ⊑-trans-proper .ω ⊢'-ω .ω w ⊑-ω v⊑w = v⊑w
  ⊑-trans-proper .ω ⊢'-ω u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper ω ⊢'-ω u₁ w u⊑v v⊑w) (⊑-trans-proper ω ⊢'-ω u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .ν ⊢'-ν .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .ν ⊢'-ν .ν w ⊑-ν-ν v⊑w = v⊑w
  ⊑-trans-proper .ν ⊢'-ν u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper ν ⊢'-ν u₁ w u⊑v v⊑w) (⊑-trans-proper ν ⊢'-ν u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(const k) (⊢'-const k) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(const k) (⊢'-const k) .(const k) w ⊑-const v⊑w = v⊑w
  ⊑-trans-proper .(const k) (⊢'-const k) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (const k) (⊢'-const k) u₁ w u⊑v v⊑w) 
                  (⊑-trans-proper (const k) (⊢'-const k) u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(_ ↦ _) (⊢'-↦-å {v₁} {v₂} Pv Pv₁ åv₂) u w u⊑v v⊑w = 
      G u w u⊑v v⊑w (⊑-trans-proper v₁ Pv₁) (⊑-trans-proper v₂ Pv)
    where
    G : ∀ u w → u ⊑ v₁ ↦ v₂ → v₁ ↦ v₂ ⊑ w → (∀ u w → u ⊑ v₁ → v₁ ⊑ w → u ⊑ w) 
                              → (∀ u w → u ⊑ v₂ → v₂ ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω v⊑w IH₁ IH₂ = ⊑-ω
    G .ν .(_ ⊔ _) ⊑-ν-↦ (⊑-⊔-R1-å {_}{w₁}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R1-å tt (G ν w₁ ⊑-ν-↦ v⊑w IH₁ IH₂)
    G .ν .(_ ⊔ _) ⊑-ν-↦ (⊑-⊔-R2-å {_}{w₁}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R2-å tt (G ν w₂ ⊑-ν-↦ v⊑w IH₁ IH₂)
    G .ν .(_ ↦ _) ⊑-ν-↦ (⊑-↦-å åu₂ v⊑w v⊑w₁) IH₁ IH₂ = ⊑-ν-↦
    G .ν w ⊑-ν-↦ (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ = ⊥-elim (unsplittable (v₁ ↦ v₂) åv₂ split)
    G .(_ ↦ _) .(_ ⊔ _) (⊑-↦-å {u₁}{u₂} åu₂ u⊑v u⊑v₁) (⊑-⊔-R1-å {_}{w₁} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R1-å åu₂ (G (u₁ ↦ u₂) w₁ (⊑-↦-å åu₂ u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(_ ↦ _) .(_ ⊔ _) (⊑-↦-å {u₁}{u₂} åu₂ u⊑v u⊑v₁) (⊑-⊔-R2-å {_}{_}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R2-å åu₂ (G (u₁ ↦ u₂) w₂ (⊑-↦-å åu₂ u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(_ ↦ _) .(_ ↦ _) (⊑-↦-å {u₁}{u₂} åu₂ u⊑v u⊑v₁) (⊑-↦-å {_}{_}{w₁}{w₂} åu₃ v⊑w v⊑w₁) IH₁ IH₂ = 
      ⊑-↦-å åu₂ (IH₂ u₂ w₂ u⊑v v⊑w) (IH₁ w₁ u₁ v⊑w₁ u⊑v₁)
    G .(_ ↦ _) w (⊑-↦-å {u₁}{u₂} åu₂ u⊑v u⊑v₁) (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ = 
      ⊥-elim (unsplittable (v₁ ↦ v₂) åv₂ split)
    G u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w IH₁ IH₂ = 
      ⊑-split split (G u₁ w u⊑v v⊑w IH₁ IH₂) (G u₂ w u⊑v₁ v⊑w IH₁ IH₂)
  ⊑-trans-proper .(⦅ _ , _ ⦆) (⊢'-pair-å {v₁}{v₂} Pv Pv₁ åv₁ åv₂) u w u⊑v v⊑w = 
      G u w u⊑v v⊑w (⊑-trans-proper v₁ Pv) (⊑-trans-proper v₂ Pv₁)
    where
    G : ∀ u w → u ⊑ ⦅ v₁ , v₂ ⦆ → ⦅ v₁ , v₂ ⦆ ⊑ w → (∀ u w → u ⊑ v₁ → v₁ ⊑ w → u ⊑ w) 
                              → (∀ u w → u ⊑ v₂ → v₂ ⊑ w → u ⊑ w) → u ⊑ w
    G .ω v ⊑-ω v⊑w IH₁ IH₂ = ⊑-ω
    G .(⦅ _ , _ ⦆) .(_ ⊔ _) (⊑-pair-å {u₁}{u₂} åfst åsnd u⊑v u⊑v₁) (⊑-⊔-R1-å {_}{w₁} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R1 (G (⦅ u₁ , u₂ ⦆) w₁ (⊑-pair-å åfst åsnd u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(⦅ _ , _ ⦆) .(_ ⊔ _) (⊑-pair-å {u₁}{u₂} åfst åsnd u⊑v u⊑v₁) (⊑-⊔-R2-å {_}{_}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R2 (G (⦅ u₁ , u₂ ⦆) w₂ (⊑-pair-å åfst åsnd u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(⦅ _ , _ ⦆) .(⦅ _ , _ ⦆) (⊑-pair-å {u₁}{u₂} åfst åsnd u⊑v u⊑v₁) (⊑-pair-å {_}{_}{w₁}{w₂} åfst₁ åsnd₁ v⊑w v⊑w₁) IH₁ IH₂ = 
      ⊑-pair-å åfst åsnd (IH₁ u₁ w₁ u⊑v v⊑w) (IH₂ u₂ w₂ u⊑v₁ v⊑w₁)
    G .(⦅ _ , _ ⦆) v (⊑-pair-å åfst åsnd u⊑v u⊑v₁) (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ = 
      ⊥-elim (unsplittable (⦅ v₁ , v₂ ⦆) ⟨ åv₁ , åv₂ ⟩ split)
    G u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w IH₁ IH₂ = ⊑-split split (G u₁ w u⊑v v⊑w IH₁ IH₂) (G u₂ w u⊑v₁ v⊑w IH₁ IH₂)
  ⊑-trans-proper .(∥ [] ∥) ⊢'-nil .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(∥ [] ∥) ⊢'-nil .(∥ [] ∥) w ⊑-nil v⊑w = v⊑w
  ⊑-trans-proper .(∥ [] ∥) ⊢'-nil u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (∥ [] ∥) ⊢'-nil u₁ w u⊑v v⊑w) (⊑-trans-proper (∥ [] ∥) ⊢'-nil u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(∥ _ ∷ _ ∥) (⊢'-tup-å {n}{v}{vs} Pv Pv₁ åv åvs) u w u⊑v v⊑w = 
      G u w u⊑v v⊑w (⊑-trans-proper v Pv) (⊑-trans-proper (∥ vs ∥) Pv₁)
    where
    G : ∀ u w → u ⊑ ∥ v ∷ vs ∥ → ∥ v ∷ vs ∥ ⊑ w → (∀ u w → u ⊑ v → v ⊑ w → u ⊑ w) 
                              → (∀ u w → u ⊑ (∥ vs ∥) → (∥ vs ∥) ⊑ w → u ⊑ w) → u ⊑ w
    G .ω v ⊑-ω v⊑w IH₁ IH₂ = ⊑-ω
    G .(∥ u ∷ _ ∥) .(_ ⊔ _) (⊑-tup-å {n} {u} {_} {us} åus u⊑v u⊑v₁) (⊑-⊔-R1-å {_}{w₁} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R1 (G (∥ u ∷ us ∥) w₁ (⊑-tup-å åus u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(∥ u ∷ _ ∥) .(_ ⊔ _) (⊑-tup-å {n} {u} {_} {us} åus u⊑v u⊑v₁) (⊑-⊔-R2-å {_}{_}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R2 (G (∥ u ∷ us ∥) w₂ (⊑-tup-å åus u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(∥ u ∷ _ ∥) .(∥ _ ∷ _ ∥) (⊑-tup-å {n} {u} {_} {us} åus u⊑v u⊑v₁) (⊑-tup-å {_}{_}{w}{_}{ws} åus₁ v⊑w v⊑w₁) IH₁ IH₂ = 
      ⊑-tup-å åus (IH₁ u w u⊑v v⊑w) (IH₂ (∥ us ∥) (∥ ws ∥) u⊑v₁ v⊑w₁)
    G .(∥ _ ∷ _ ∥) w (⊑-tup-å åus u⊑v u⊑v₁) (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ = 
      ⊥-elim (unsplittable (∥ v ∷ vs ∥) ⟨ åv , åvs ⟩ split)
    G u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w IH₁ IH₂ = ⊑-split split (G u₁ w u⊑v v⊑w IH₁ IH₂) (G u₂ w u⊑v₁ v⊑w IH₁ IH₂)
  ⊑-trans-proper v (⊢'-split vL vR split PvL PvR) u w u⊑v v⊑w = 
    split-trans u (proper u) u⊑v (⊑-trans-proper vL PvL) (⊑-trans-proper vR PvR)
    where 
    split-trans : ∀ u → Proper u → u ⊑ v
      → (∀ u w → u ⊑ vL → vL ⊑ w → u ⊑ w)
      → (∀ u w → u ⊑ vR → vR ⊑ w → u ⊑ w) → u ⊑ w
    split-trans .ω ⊢'-ω u⊑v IH₁ IH₂ with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split tt
    ... | inj₁ x = IH₁ ω w x vL⊑w
    ... | inj₂ y = IH₂ ω w y vR⊑w
    split-trans .ν ⊢'-ν u⊑v IH₁ IH₂ with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split tt
    ... | inj₁ x = IH₁ ν w x vL⊑w
    ... | inj₂ y = IH₂ ν w y vR⊑w
    split-trans .(const k) (⊢'-const k) u⊑v IH₁ IH₂ with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split tt
    ... | inj₁ x = IH₁ (const k) w x vL⊑w
    ... | inj₂ y = IH₂ (const k) w y vR⊑w
    split-trans .(_ ↦ _) (⊢'-↦-å {v₁} {v₂} Pu Pu₁ åv₂) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split åv₂
    ... | inj₁ x = IH₁ (v₁ ↦ v₂) w x vL⊑w
    ... | inj₂ y = IH₂ (v₁ ↦ v₂) w y vR⊑w
    split-trans .(⦅ _ , _ ⦆) (⊢'-pair-å {v₁} {v₂} Pu Pu₁ åv₁ åv₂) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split ⟨ åv₁ , åv₂ ⟩
    ... | inj₁ x = IH₁ (⦅ v₁ , v₂ ⦆) w x vL⊑w
    ... | inj₂ y = IH₂ (⦅ v₁ , v₂ ⦆) w y vR⊑w
    split-trans .(∥ [] ∥) ⊢'-nil u⊑v IH₁ IH₂ with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split tt
    ... | inj₁ x = IH₁ (∥ [] ∥) w x vL⊑w
    ... | inj₂ y = IH₂ (∥ [] ∥) w y vR⊑w
    split-trans .(∥ _ ∷ _ ∥) (⊢'-tup-å {n}{v}{vs} Pu Pu₁ åv åvs) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split ⟨ åv , åvs ⟩
    ... | inj₁ x = IH₁ (∥ v ∷ vs ∥) w x vL⊑w
    ... | inj₂ y = IH₂ (∥ v ∷ vs ∥) w y vR⊑w
    split-trans .(left _) (⊢'-left-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split åu
    ... | inj₁ x = IH₁ (left u) w x vL⊑w
    ... | inj₂ y = IH₂ (left u) w y vR⊑w
    split-trans .(right _) (⊢'-right-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split åu
    ... | inj₁ x = IH₁ (right u) w x vL⊑w
    ... | inj₂ y = IH₂ (right u) w y vR⊑w
    split-trans u (⊢'-split uL uR split' Pu Pu₁) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R u⊑v split'
    ... | ⟨ uL⊑v , uR⊑v ⟩ = 
      ⊑-split split' (split-trans uL Pu uL⊑v IH₁ IH₂) (split-trans uR Pu₁ uR⊑v IH₁ IH₂)
  ⊑-trans-proper .(left _) (⊢'-left-å Pv åv) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(left _) (⊢'-left-å {v} Pv åv) .(left _) w (⊑-left-å {u} åu u⊑v) v⊑w 
    = G (left u) w (⊑-left-å åu u⊑v) v⊑w (⊑-trans-proper v Pv)
    where
    G : ∀ u w → u ⊑ left v → left v ⊑ w → (∀ u w → u ⊑ v → v ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω Lv⊑w IH = ⊑-ω
    G .(left _) .(_ ⊔ _) (⊑-left-å {u₁} {v₁} åu u⊑Lv) (⊑-⊔-R1-å {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-⊔-R1-å åu (G (left u₁) w₁ (⊑-left-å åu u⊑Lv) Lv⊑w IH)
    G .(left _) .(_ ⊔ _) (⊑-left-å {u₁} {v₁} åu u⊑Lv) (⊑-⊔-R2-å {_} {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-⊔-R2-å åu (G (left u₁) w₁ (⊑-left-å åu u⊑Lv) Lv⊑w IH)
    G .(left _) .(left _) (⊑-left-å {u₁} {v₁} åu u⊑Lv) (⊑-left-å {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-left-å åu (IH u₁ w₁ u⊑Lv Lv⊑w)
    G .(left _) w (⊑-left-å åu u⊑Lv) (⊑-split split Lv⊑w Lv⊑w₁) IH = 
      ⊥-elim (unsplittable (left v) åv split)
    G u w (⊑-split {u} {u₁} {u₂} split u⊑Lv u⊑Lv₁) Lv⊑w IH = 
      ⊑-split split (G u₁ w u⊑Lv Lv⊑w IH) (G u₂ w u⊑Lv₁ Lv⊑w IH)
  ⊑-trans-proper .(left _) (⊢'-left-å {v} Pv åv) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (left v) (⊢'-left-å Pv åv) u₁ w u⊑v v⊑w)
                  (⊑-trans-proper (left v) (⊢'-left-å Pv åv) u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(right _) (⊢'-right-å Pv åv) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(right _) (⊢'-right-å {v} Pv åv) .(right _) w (⊑-right-å {u} åu u⊑v) v⊑w 
    = G (right u) w (⊑-right-å åu u⊑v) v⊑w (⊑-trans-proper v Pv)
    where
    G : ∀ u w → u ⊑ right v → right v ⊑ w → (∀ u w → u ⊑ v → v ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω Rv⊑w IH = ⊑-ω
    G .(right _) .(_ ⊔ _) (⊑-right-å {u₁}{v₁} åu u⊑Rv) (⊑-⊔-R1-å {_}{w₁} åu₁ Rv⊑w) IH = 
      ⊑-⊔-R1-å åu (G (right u₁) w₁ (⊑-right-å åu u⊑Rv) Rv⊑w IH)
    G .(right _) .(_ ⊔ _) (⊑-right-å {u₁}{v₁} åu u⊑Rv) (⊑-⊔-R2-å {_}{_}{w₁} åu₁ Rv⊑w) IH = 
      ⊑-⊔-R2-å åu (G (right u₁) w₁ (⊑-right-å {u₁}{v₁} åu u⊑Rv) Rv⊑w IH)
    G .(right _) .(right _) (⊑-right-å {u₁}{v₁} åu u⊑Rv) (⊑-right-å {_}{w₁} åu₁ Rv⊑w) IH = 
      ⊑-right-å åu (IH u₁ w₁ u⊑Rv Rv⊑w)
    G .(right _) w (⊑-right-å åu u⊑Rv) (⊑-split split Rv⊑w Rv⊑w₁) IH = 
      ⊥-elim (unsplittable (right v) åv split)
    G u w (⊑-split {_}{u₁}{u₂} split u⊑Rv u⊑Rv₁) Rv⊑w IH = 
      ⊑-split split (G u₁ w u⊑Rv Rv⊑w IH) (G u₂ w u⊑Rv₁ Rv⊑w IH)
  ⊑-trans-proper .(right _) (⊢'-right-å {v} Pv åv) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (right v) (⊢'-right-å Pv åv) u₁ w u⊑v v⊑w)
                  (⊑-trans-proper (right v) (⊢'-right-å Pv åv) u₂ w u⊑v₁ v⊑w)


  ⊑-trans : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
  ⊑-trans {u}{v}{w} u⊑v v⊑w = ⊑-trans-proper v (proper v) u w u⊑v v⊑w

  tup-cons : Value → Value → Value
  tup-cons u ω = ω
  tup-cons u ν = ω
  tup-cons u (const k) = ω
  tup-cons u (v ⊔ v₁) = ω
  tup-cons u (v ↦ v₁) = ω
  tup-cons u (⦅ v , v₁ ⦆) = ω
  tup-cons u (left v) = ω
  tup-cons u (right v) = ω
  tup-cons u (∥ vs ∥) = ∥ u ∷ vs ∥


 {- This is the distributivity rule for each splitting -}
  ⊑-dist-⊔ : ∀ {v vL vR}
       → vL ◃ v ▹ vR
       ----------------------
       → v ⊑ vL ⊔ vR
  ⊑-dist-⊔ split = ⊑-split split (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl)


 {- for example, the usual distributivity rule for functions -}
  ⊑-dist-fun : ∀ {v wL wR}
     →  v ↦ (wL ⊔ wR) ⊑ (v ↦ wL) ⊔ (v ↦ wR)
  ⊑-dist-fun {v}{wL}{wR} = ⊑-split (split-↦ split-⊔) (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl)
  

  ordering : ValueOrdering value_struct
  ordering = record
   { _⊑_ = _⊑_
   ; ⊑-⊥ = ⊑-ω
   ; ⊑-conj-L = ⊑-⊔-L
   ; ⊑-conj-R1 = ⊑-⊔-R1
   ; ⊑-conj-R2 = ⊑-⊔-R2
   ; ⊑-trans = ⊑-trans
   ; ⊑-fun = ⊑-↦
   ; ⊑-refl = ⊑-refl
   ; ⊑-dist = ⊑-dist-fun
   }



{-  

{-
  And distributivity for pairs
-}

⊑-pair-dist : ∀ {u u' v v'}
       → pair (u ⊔ u') (v ⊔ v') ⊑ ⦅ u , v ⦆ ⊔ pair u' v'
⊑-pair-dist =
  ⊑-pair (λ z → z) (pair-⊔ pair-pair pair-pair) ⊑-refl ⊑-refl

-}



{-

{-



⊔-⊑L : ∀{B C A}
    → B ⊔ C ⊑ A
    → B ⊑ A
⊔-⊑L (⊑-conj-L B⊔C⊑A B⊔C⊑A₁) = B⊔C⊑A
⊔-⊑L (⊑-conj-R1 B⊔C⊑A) = ⊑-conj-R1 (⊔-⊑L B⊔C⊑A)
⊔-⊑L (⊑-conj-R2 B⊔C⊑A) = ⊑-conj-R2 (⊔-⊑L B⊔C⊑A)

⊔-⊑R : ∀{B C A}
    → B ⊔ C ⊑ A
    → C ⊑ A
⊔-⊑R (⊑-conj-L B⊔C⊑A B⊔C⊑A₁) = B⊔C⊑A₁
⊔-⊑R (⊑-conj-R1 B⊔C⊑A) = ⊑-conj-R1 (⊔-⊑R B⊔C⊑A)
⊔-⊑R (⊑-conj-R2 B⊔C⊑A) = ⊑-conj-R2 (⊔-⊑R B⊔C⊑A)

⊑-fun-inv : ∀{u₁ u₂ v w}
      → u₁ ⊑ u₂
      → v ↦ w ∈ u₁
      → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
⊑-fun-inv {.ν} {u₂} {v} {w} (⊑-ν neu₂) ()
⊑-fun-inv {.(const _)} {.(const _)} {v} {w} ⊑-const ()
⊑-fun-inv {.(⦅ _ , _ ⦆)} {u₂} {v} {w} (⊑-⦅ _ , _ ⦆ _ _) ()
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
⊑-fun-inv {u11 ↦ u21} {u₂} {v} {w} (⊑-fun{u' = u′} u′⊆u₂ afu′ du′⊑u11 u21⊑cu′)
    refl =
      ⟨ u′ , ⟨ afu′ , ⟨ u′⊆u₂ , ⟨ du′⊑u11 , u21⊑cu′ ⟩ ⟩ ⟩ ⟩

⊑-pair-inv : ∀ {u₁ u₂ v}
           → (⦅ u₁ , u₂ ⦆) ⊑ v
           → Σ[ v' ∈ Value ] pair-factor v v' u₁ u₂    {- Σ[ pairv' ∈ Pair v' ]
                 v' ⊆ v × u₁ ⊑ pair-fst pairv' × u₂ ⊑ pair-snd pairv' -}
⊑-pair-inv (⊑-conj-R1 u₁⊑v) with ⊑-pair-inv u₁⊑v
... | ⟨ v' , ⟨ pairv' , ⟨ v'⊆v , approx ⟩ ⟩ ⟩ =
   ⟨ v' , ⟨ pairv' , ⟨ inj₁ ∘ v'⊆v , approx ⟩ ⟩ ⟩
⊑-pair-inv (⊑-conj-R2 u₂⊑v) with ⊑-pair-inv u₂⊑v
... | ⟨ v' , ⟨ pairv' , ⟨ v'⊆v , approx ⟩ ⟩ ⟩ =
   ⟨ v' , ⟨ pairv' , ⟨ inj₂ ∘ v'⊆v , approx ⟩ ⟩ ⟩
⊑-pair-inv (⊑-pair {v' = v'} v'⊆v pairv' u₁⊑v₁ u₂⊑v₂) =
   ⟨ v' , ⟨ pairv' , ⟨ v'⊆v , ⟨ u₁⊑v₁ , u₂⊑v₂ ⟩ ⟩ ⟩ ⟩

⊑-tup-inv : ∀ {n} {us vs : Vec Value n} → ∥ us ∥ ⊑ ∥ vs ∥ → us [⊑] vs
⊑-tup-inv {zero} {[]} ⊑-nil = []
⊑-tup-inv {zero} {[]} (⊑-split (split-tup ()) q q')
⊑-tup-inv {suc n} {u ∷ us} (⊑-tup-å åus us⊑vs us[⊑]vs) = us⊑vs ∷ us[⊑]vs
⊑-tup-inv {suc n} {u ∷ us} {v ∷ vs} (⊑-split (split-tup (split-tup-head x)) us⊑vs us⊑vs') with ⊑-tup-inv us⊑vs | ⊑-tup-inv us⊑vs'
... | u⊑v₁ ∷ us⊑vs₁ | u⊑v₂ ∷ us⊑vs₂ = ⊑-split x u⊑v₁ u⊑v₂ ∷ us⊑vs₂
⊑-tup-inv {suc n} {u ∷ us} {v ∷ vs} (⊑-split (split-tup (split-tup-tail split)) us⊑vs us⊑vs') with ⊑-tup-inv us⊑vs | ⊑-tup-inv us⊑vs'
... | u⊑v₁ ∷ us⊑vs₁ | u⊑v₂ ∷ us⊑vs₂ = u⊑v₂ ∷ ⊑-tup-inv (⊑-split (split-∥ split ∥) {!   !} {!   !} )  


⊑-tup-inv : ∀ {n vs v}
           → (∥_∥ {n} vs) ⊑ v
           → Σ[ v' ∈ Value ] tup-factor v v' vs    {- Σ[ pairv' ∈ Pair v' ]
                 v' ⊆ v × u₁ ⊑ pair-fst pairv' × u₂ ⊑ pair-snd pairv' -}
⊑-tup-inv (⊑-conj-R1 u₁⊑v) with ⊑-tup-inv u₁⊑v
... | ⟨ v' , ⟨ tupv' , ⟨ v'⊆v , approx ⟩ ⟩ ⟩ =
   ⟨ v' , ⟨ tupv' , ⟨ inj₁ ∘ v'⊆v , approx ⟩ ⟩ ⟩
⊑-tup-inv (⊑-conj-R2 u₂⊑v) with ⊑-tup-inv u₂⊑v
... | ⟨ v' , ⟨ tupv' , ⟨ v'⊆v , approx ⟩ ⟩ ⟩ =
   ⟨ v' , ⟨ tupv' , ⟨ inj₂ ∘ v'⊆v , approx ⟩ ⟩ ⟩
⊑-tup-inv (⊑-tup {v' = v'} v'⊆v tupv' vs⊑v') =
   ⟨ v' , ⟨ tupv' , ⟨ v'⊆v , vs⊑v' ⟩ ⟩ ⟩



{-
  The traditional function subtyping rule is admissible.
 -}


{-
  And distributivity for pairles
-}

⊑-pair-dist : ∀ {u u' v v'}
       → pair (u ⊔ u') (v ⊔ v') ⊑ ⦅ u , v ⦆ ⊔ pair u' v'
⊑-pair-dist =
  ⊑-pair (λ z → z) (pair-⊔ pair-pair pair-pair) ⊑-refl ⊑-refl

{-
  The usual inversion rule for function subtyping.
 -}


⊑-fun-inv′ : ∀{v w v′ w′}
  → v ↦ w ⊑ v′ ↦ w′
   -----------------
  → v′ ⊑ v × w ⊑ w′
⊑-fun-inv′ {v}{w}{v′}{w′} lt
  with ⊑-fun-inv lt refl
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
  with NonEmptyFun∈ f
... | ⟨ u , ⟨ u′ , u↦u′∈Γ ⟩ ⟩
  with Γ⊆v34 u↦u′∈Γ
... | refl =
  let codΓ⊆w′ = ⊆↦→cod⊆ Γ⊆v34 in
  let u⊆domΓ = ↦∈→⊆dom{Γ}{neu = f} u↦u′∈Γ in
    ⟨ ⊑-trans (⊆→⊑ u⊆domΓ) lt1 , ⊑-trans lt2 (⊆→⊑ codΓ⊆w′) ⟩


⊑-tup-inv' : ∀ {n} {vs₁} {vs₂} → ∥_∥ {n} vs₁ ⊑ ∥_∥ {n} vs₂ → Pointwise (_⊑_) vs₁ vs₂
⊑-tup-inv' {n} {vs₁} {vs₂} (⊑-tup {v' = v'} v'⊆vs₂ tup-∥ vs ∥₁⊑v') with v'⊆vs₂ {v'} refl
... | eq = subst (Pointwise _⊑_ vs₁) (tup-injective eq) vs₁⊑v'
⊑-tup-inv' (⊑-tup v'⊆vs₂ (tup-⊔ tupv' tupv'') vs₁⊑v') = {!   !}

⊑-tup' : ∀ {n v₁ vs₁ v₂ vs₂} → v₁ ⊑ v₂ → ∥_∥ {n} vs₁ ⊑ ∥_∥ {n} vs₂ → tup (v₁ ∷ vs₁) ⊑ tup (v₂ ∷ vs₂)
⊑-tup' {n} {v₁} {vs₁} {v₂} {vs₂} v₁⊑v₂ vs₁⊑vs₂ = ⊑-tup {suc n} {v₁ ∷ vs₁} {tup (v₂ ∷ vs₂)}  (λ x → x) tup-tup {!   !}

{- The pointwise rules for pairles -}



⊑-pair' : ∀ {u₁ u₂ v₁ v₂} → u₁ ⊑ v₁ → u₂ ⊑ v₂
         → ⦅ u₁ , u₂ ⦆ ⊑ ⦅ v₁ , v₂ ⦆
⊑-pair' ⊑₁ ⊑₂ = ⊑-pair (λ z → z) pair-pair ⊑₁ ⊑₂

⊑-pair-inv' : ∀ {u₁ u₂ v₁ v₂} → ⦅ u₁ , u₂ ⦆ ⊑ ⦅ v₁ , v₂ ⦆
             → u₁ ⊑ v₁ × u₂ ⊑ v₂
⊑-pair-inv' u⊑v with ⊑-pair-inv u⊑v
... | ⟨ v' , ⟨ pairv' , ⟨ v'⊆v , ⟨  u₁⊑fstv' , u₂⊑sndv' ⟩ ⟩ ⟩ ⟩
  with pair→pair∈ pairv'
... | ⟨ v'₁ , ⟨ v'₂ , v'₁,v'₂∈v' ⟩ ⟩ with v'⊆v v'₁,v'₂∈v'
... | refl = ⟨ u⊑v⊆w→u⊑w u₁⊑fstv' (fst-⊆ pairv' pair-pair v'⊆v)
             , u⊑v⊆w→u⊑w u₂⊑sndv' (snd-⊆ pairv' pair-pair v'⊆v) ⟩




-}

-}
