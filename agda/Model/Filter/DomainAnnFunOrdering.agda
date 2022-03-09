
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

module Model.Filter.DomainAnnFunOrdering where

  open import Model.Filter.DomainUtil
  open import Primitives
  open import Model.Filter.DomainAnnFunValues


  infix 5 _⊑_

  data _⊑_ : (u v : Value) → Set where

    {- Atomic Rules :  we use å (\aa) as an abbreviation for atomic -}

    ⊑-ω : ∀ {v} → ω ⊑ v
  
    ⊑-ν-ν-å : ∀ {FV FV'} 
      → (åFV : Atomic FV)
      → (FV⊑ : FV ⊑ FV')
        ------------------
      → (FV ⊢ν) ⊑ (FV' ⊢ν)

    ⊑-ν-↦-å : ∀ {FV FV' v w}
      → (åFV : Atomic FV)
      → (FV⊑ : FV ⊑ FV')
        ----------------------
      → (FV ⊢ν) ⊑ FV' ⊢ v ↦ w

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

    ⊑-fst-å : ∀ {u v}
       → (åu : Atomic u)
       → (u⊑v : u ⊑ v)
        ------------------
       → ⦅ u ∣ ⊑ ⦅ v ∣

    ⊑-snd-å : ∀ {u v}
       → (åu : Atomic u)
       → (u⊑v : u ⊑ v)
        ------------------
       → ∣ u ⦆ ⊑ ∣ v ⦆

    ⊑-nil : ∥ [] ∥ ⊑ ∥ [] ∥
  
    ⊑-tup-å : ∀ {n u v us vs}
       → (åus : Atomic-tup {suc n} (u ∷ us))
       → (u⊑v : u ⊑ v)
       → (us⊑vs : ∥ us ∥ ⊑ ∥_∥ {n} vs)
       ------------------------------
       → ∥ u ∷ us ∥ ⊑ ∥ v ∷ vs ∥

    ⊑-↦-å : ∀ {FV FV' u₁ u₂ v₁ v₂}
       → (åu₂ : Atomic u₂)
       → (åFV : Atomic FV)
       → (⊑FV : FV ⊑ FV')
       → (⊑cod : u₂ ⊑ v₂)
       → (dom⊑ : v₁ ⊑ u₁)
       ------------------
       → FV ⊢ u₁ ↦ u₂ ⊑ FV' ⊢ v₁ ↦ v₂ 

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
  ⊑-⊔-R1 (⊑-ν-ν-å åFV u⊑v) = ⊑-⊔-R1-å åFV (⊑-ν-ν-å åFV u⊑v)
  ⊑-⊔-R1 (⊑-ν-↦-å åFV u⊑v) = ⊑-⊔-R1-å åFV (⊑-ν-↦-å åFV u⊑v)
  ⊑-⊔-R1 ⊑-const = ⊑-⊔-R1-å tt ⊑-const
  ⊑-⊔-R1 (⊑-⊔-R1-å åu u⊑v₁) = ⊑-⊔-R1-å åu (⊑-⊔-R1 u⊑v₁)
  ⊑-⊔-R1 (⊑-⊔-R2-å åu u⊑v₁) = ⊑-⊔-R1-å åu (⊑-⊔-R2-å åu u⊑v₁)
  ⊑-⊔-R1 (⊑-fst-å åu u⊑v) = ⊑-⊔-R1-å åu (⊑-fst-å åu u⊑v)
  ⊑-⊔-R1 (⊑-snd-å åu u⊑v) = ⊑-⊔-R1-å åu (⊑-snd-å åu u⊑v)
  ⊑-⊔-R1 ⊑-nil = ⊑-⊔-R1-å tt ⊑-nil
  ⊑-⊔-R1 (⊑-tup-å åus u⊑v₁ us[⊑]vs) = ⊑-⊔-R1-å åus (⊑-tup-å åus u⊑v₁ us[⊑]vs)
  ⊑-⊔-R1 (⊑-↦-å åu₂ åFV FV⊑ u⊑v₁ u⊑v₂) = ⊑-⊔-R1-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV FV⊑ u⊑v₁ u⊑v₂)
  ⊑-⊔-R1 (⊑-left-å åu q) = ⊑-⊔-R1-å åu (⊑-left-å åu q)
  ⊑-⊔-R1 (⊑-right-å åu q) = ⊑-⊔-R1-å åu (⊑-right-å åu q)
  ⊑-⊔-R1 (⊑-split split u⊑v₁ u⊑v₂) = ⊑-split split (⊑-⊔-R1 u⊑v₁) (⊑-⊔-R1 u⊑v₂)

  ⊑-⊔-R2 : ∀ {u v₁ v₂} → u ⊑ v₂ → u ⊑ v₁ ⊔ v₂
  ⊑-⊔-R2 ⊑-ω = ⊑-ω
  ⊑-⊔-R2 (⊑-ν-ν-å åFV u⊑v) = ⊑-⊔-R2-å åFV (⊑-ν-ν-å åFV u⊑v)
  ⊑-⊔-R2 (⊑-ν-↦-å åFV u⊏v) = ⊑-⊔-R2-å åFV (⊑-ν-↦-å åFV u⊏v)
  ⊑-⊔-R2 ⊑-const = ⊑-⊔-R2-å tt ⊑-const
  ⊑-⊔-R2 (⊑-⊔-R1-å åu u⊑v₂) = ⊑-⊔-R2-å åu (⊑-⊔-R1-å åu u⊑v₂)
  ⊑-⊔-R2 (⊑-⊔-R2-å åu u⊑v₂) = ⊑-⊔-R2-å åu (⊑-⊔-R2 u⊑v₂)
  ⊑-⊔-R2 (⊑-fst-å åu u⊑v) = ⊑-⊔-R2-å åu (⊑-fst-å åu u⊑v)
  ⊑-⊔-R2 (⊑-snd-å åu u⊑v) = ⊑-⊔-R2-å åu (⊑-snd-å åu u⊑v)
  ⊑-⊔-R2 ⊑-nil = ⊑-⊔-R2-å tt ⊑-nil
  ⊑-⊔-R2 (⊑-tup-å åus u⊑v₂ us[⊑]vs) = ⊑-⊔-R2-å åus (⊑-tup-å åus u⊑v₂ us[⊑]vs)
  ⊑-⊔-R2 (⊑-↦-å åu₂ åFV FV⊑ u⊑v₂ u⊑v₃) = ⊑-⊔-R2-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV FV⊑ u⊑v₂ u⊑v₃)
  ⊑-⊔-R2 (⊑-left-å åu q) = ⊑-⊔-R2-å åu (⊑-left-å åu q)
  ⊑-⊔-R2 (⊑-right-å åu q) = ⊑-⊔-R2-å åu (⊑-right-å åu q)
  ⊑-⊔-R2 (⊑-split split u⊑v₂ u⊑v₃) = ⊑-split split (⊑-⊔-R2 u⊑v₂) (⊑-⊔-R2 u⊑v₃)

  ⊑-⊔-L : ∀ {u₁ u₂ v} → u₁ ⊑ v → u₂ ⊑ v → u₁ ⊔ u₂ ⊑ v
  ⊑-⊔-L 1⊑ 2⊑ = ⊑-split split-⊔ 1⊑ 2⊑

  ⊑-fst : ∀ {u v} → u ⊑ v → ⦅ u ∣ ⊑ ⦅ v ∣
  ⊑-fst ⊑-ω = ⊑-fst-å tt ⊑-ω
  ⊑-fst (⊑-ν-ν-å åFV u⊑v) = ⊑-fst-å åFV (⊑-ν-ν-å åFV u⊑v)
  ⊑-fst (⊑-ν-↦-å åFV u⊑v) = ⊑-fst-å åFV (⊑-ν-↦-å åFV u⊑v)
  ⊑-fst ⊑-const = ⊑-fst-å tt ⊑-const
  ⊑-fst (⊑-⊔-R1-å åu u⊑v) = ⊑-fst-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-fst (⊑-⊔-R2-å åu u⊑v) = ⊑-fst-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-fst (⊑-fst-å åu u⊑v) = ⊑-fst-å åu (⊑-fst u⊑v)
  ⊑-fst (⊑-snd-å åu u⊑v) = ⊑-fst-å åu (⊑-snd-å åu u⊑v)
  ⊑-fst ⊑-nil = ⊑-fst-å tt ⊑-nil
  ⊑-fst (⊑-tup-å åus u⊑v u⊑v₁) = ⊑-fst-å åus (⊑-tup-å åus u⊑v u⊑v₁)
  ⊑-fst (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) = ⊑-fst-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂)
  ⊑-fst (⊑-left-å åu u⊑v) = ⊑-fst-å åu (⊑-left-å åu u⊑v)
  ⊑-fst (⊑-right-å åu u⊑v) = ⊑-fst-å åu (⊑-right-å åu u⊑v)
  ⊑-fst (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-fst split) (⊑-fst u⊑v) (⊑-fst u⊑v₁)

  ⊑-snd : ∀ {u v} → u ⊑ v → ∣ u ⦆ ⊑ ∣ v ⦆
  ⊑-snd ⊑-ω = ⊑-snd-å tt ⊑-ω
  ⊑-snd (⊑-ν-ν-å åFV u⊑v) = ⊑-snd-å åFV (⊑-ν-ν-å åFV u⊑v)
  ⊑-snd (⊑-ν-↦-å åFV u⊑v) = ⊑-snd-å åFV (⊑-ν-↦-å åFV u⊑v)
  ⊑-snd ⊑-const = ⊑-snd-å tt ⊑-const
  ⊑-snd (⊑-⊔-R1-å åu u⊑v) = ⊑-snd-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-snd (⊑-⊔-R2-å åu u⊑v) = ⊑-snd-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-snd (⊑-fst-å åu u⊑v) = ⊑-snd-å åu (⊑-fst-å åu u⊑v)
  ⊑-snd (⊑-snd-å åu u⊑v) = ⊑-snd-å åu (⊑-snd u⊑v)
  ⊑-snd ⊑-nil = ⊑-snd-å tt ⊑-nil
  ⊑-snd (⊑-tup-å åus u⊑v u⊑v₁) = ⊑-snd-å åus (⊑-tup-å åus u⊑v u⊑v₁)
  ⊑-snd (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) = ⊑-snd-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂)
  ⊑-snd (⊑-left-å åu u⊑v) = ⊑-snd-å åu (⊑-left-å åu u⊑v)
  ⊑-snd (⊑-right-å åu u⊑v) = ⊑-snd-å åu (⊑-right-å åu u⊑v)
  ⊑-snd (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-snd split) (⊑-snd u⊑v) (⊑-snd u⊑v₁)

  ⊑-tup : ∀ {n u v} {us vs : Vec Value n} → u ⊑ v → ∥ us ∥ ⊑ ∥ vs ∥ → ∥ u ∷ us ∥ ⊑ ∥ v ∷ vs ∥
  ⊑-tup {u = u} {us = us} u⊑v us⊑vs with atomic? u
  ... | yes åu with us⊑vs 
  ... | ⊑-nil = ⊑-tup-å ⟨ åu , tt ⟩ u⊑v ⊑-nil
  ... | ⊑-tup-å åus q us[⊑]vs = ⊑-tup-å ⟨ åu , åus ⟩ u⊑v us⊑vs
  ... | ⊑-split (split-tup-head x) q q₁ = ⊑-split (split-tup-tail åu (split-tup-head x)) (⊑-tup u⊑v q) (⊑-tup u⊑v q₁)
  ... | ⊑-split (split-tup-tail x x₁) q q₁ = ⊑-split (split-tup-tail åu (split-tup-tail x x₁)) (⊑-tup u⊑v q) (⊑-tup u⊑v q₁)
  ⊑-tup {u = u} {us = us} u⊑v us⊑vs | no ¬åu with u⊑v
  ... | ⊑-ω = ⊥-elim (¬åu tt)
  ... | ⊑-ν-ν-å åu u⊑v' = ⊥-elim (¬åu åu)
  ... | ⊑-ν-↦-å åu u⊑v' = ⊥-elim (¬åu åu)
  ... | ⊑-const = ⊥-elim (¬åu tt)
  ... | ⊑-⊔-R1-å åu u⊑v₁ = ⊥-elim (¬åu åu)
  ... | ⊑-⊔-R2-å åu u⊑v₁ = ⊥-elim (¬åu åu)
  ... | ⊑-fst-å åu q = ⊥-elim (¬åu åu)
  ... | ⊑-snd-å åu q = ⊥-elim (¬åu åu)
  ... | ⊑-nil = ⊥-elim (¬åu tt)
  ... | ⊑-tup-å åus u⊑v₁ us[⊑]vs = ⊥-elim (¬åu åus)
  ... | ⊑-↦-å åu₂ åu' u⊑v' u⊑v₁ u⊑v₂ = ⊥-elim (¬åu ⟨ åu₂ , åu' ⟩)
  ... | ⊑-left-å åu q = ⊥-elim (¬åu åu)
  ... | ⊑-right-å åu q = ⊥-elim (¬åu åu)
  ... | ⊑-split split u⊑v₁ u⊑v₂ = ⊑-split (split-tup-head split) (⊑-tup u⊑v₁ us⊑vs) (⊑-tup u⊑v₂ us⊑vs)

  ⊑-↦ : ∀ {FV FV' u₁ u₂ v₁ v₂} → FV ⊑ FV' → v₁ ⊑ u₁ →  u₂ ⊑ v₂ → FV ⊢ u₁ ↦ u₂ ⊑ FV' ⊢ v₁ ↦ v₂
  ⊑-↦ {FV}{FV'}{u₁}{u₂} ⊑FV dom⊑ ⊑cod with atomic? u₂
  ... | yes åu₂ with atomic? FV
  ... | yes åFV = ⊑-↦-å åu₂ åFV ⊑FV ⊑cod dom⊑
  ... | no ¬åFV with ⊑FV
  ... | ⊑-ω = ⊥-elim (¬åFV tt)
  ... | ⊑-ν-ν-å åFV ⊑FV₁ = ⊥-elim (¬åFV åFV)
  ... | ⊑-ν-↦-å åFV ⊑FV₁ = ⊥-elim (¬åFV åFV)
  ... | ⊑-const = ⊥-elim (¬åFV tt)
  ... | ⊑-⊔-R1-å åu ⊑FV₁ = ⊥-elim (¬åFV åu)
  ... | ⊑-⊔-R2-å åu ⊑FV₁ = ⊥-elim (¬åFV åu)
  ... | ⊑-fst-å åu ⊑FV₁ = ⊥-elim (¬åFV åu)
  ... | ⊑-snd-å åu ⊑FV₁ = ⊥-elim (¬åFV åu)
  ... | ⊑-nil = ⊥-elim (¬åFV tt)
  ... | ⊑-tup-å åus ⊑FV₁ ⊑FV₂ = ⊥-elim (¬åFV åus)
  ... | ⊑-↦-å åu₃ åFV ⊑FV₁ ⊑FV₂ ⊑FV₃ = ⊥-elim (¬åFV ⟨ åu₃ , åFV ⟩)
  ... | ⊑-left-å åu ⊑FV₁ = ⊥-elim (¬åFV åu)
  ... | ⊑-right-å åu ⊑FV₁ = ⊥-elim (¬åFV åu)
  ... | ⊑-split split ⊑FV₁ ⊑FV₂ = 
    ⊑-split (split-↦-ann åu₂ split) (⊑-↦ ⊑FV₁ dom⊑ ⊑cod) (⊑-↦ ⊑FV₂ dom⊑ ⊑cod)
  ⊑-↦ {FV}{FV'}{u₁}{u₂} ⊑FV dom⊑ ⊑cod | no ¬åu₂ with ⊑cod 
  ... | ⊑-ω = ⊥-elim (¬åu₂ tt)
  ... | ⊑-ν-ν-å åu u⊑v' = ⊥-elim (¬åu₂ åu)
  ... | ⊑-ν-↦-å åu u⊑v' = ⊥-elim (¬åu₂ åu)
  ... | ⊑-const = ⊥-elim (¬åu₂ tt)
  ... | ⊑-⊔-R1-å åu u₂⊑v₂ = ⊥-elim (¬åu₂ åu)
  ... | ⊑-⊔-R2-å åu u₂⊑v₂ = ⊥-elim (¬åu₂ åu)
  ... | ⊑-fst-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-snd-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-nil = ⊥-elim (¬åu₂ tt)
  ... | ⊑-tup-å åus u₂⊑v₂ us[⊑]vs = ⊥-elim (¬åu₂ åus)
  ... | ⊑-↦-å åu₂ åu' u⊑v' u₂⊑v₂ u₂⊑v₃ = ⊥-elim (¬åu₂ ⟨ åu₂ , åu' ⟩)
  ... | ⊑-left-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-right-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-split split u₂⊑v₂ u₂⊑v₃ = ⊑-split (split-↦ split) (⊑-↦ ⊑FV dom⊑ u₂⊑v₂) (⊑-↦ ⊑FV dom⊑ u₂⊑v₃)
  

  ⊑-left : ∀ {u v} → u ⊑ v → left u ⊑ left v
  ⊑-left ⊑-ω = ⊑-left-å tt ⊑-ω
  ⊑-left (⊑-ν-ν-å åFV u⊑v) = ⊑-left-å åFV (⊑-ν-ν-å åFV u⊑v)
  ⊑-left (⊑-ν-↦-å åFV u⊑v) = ⊑-left-å åFV (⊑-ν-↦-å åFV u⊑v)
  ⊑-left ⊑-const = ⊑-left-å tt ⊑-const
  ⊑-left (⊑-⊔-R1-å åu u⊑v) = ⊑-left-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-left (⊑-⊔-R2-å åu u⊑v) = ⊑-left-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-left (⊑-fst-å åu u⊑v) = ⊑-left-å åu (⊑-fst-å åu u⊑v)
  ⊑-left (⊑-snd-å åu u⊑v) = ⊑-left-å åu (⊑-snd-å åu u⊑v)
  ⊑-left ⊑-nil = ⊑-left-å tt ⊑-nil
  ⊑-left (⊑-tup-å åus u⊑v u⊑v₁) = ⊑-left-å åus (⊑-tup-å åus u⊑v u⊑v₁)
  ⊑-left (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) = ⊑-left-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂)
  ⊑-left (⊑-left-å åu u⊑v) = ⊑-left-å åu (⊑-left u⊑v)
  ⊑-left (⊑-right-å åu u⊑v) = ⊑-left-å åu (⊑-right-å åu u⊑v)
  ⊑-left (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-left split) (⊑-left u⊑v) (⊑-left u⊑v₁)

  ⊑-right : ∀ {u v} → u ⊑ v → right u ⊑ right v
  ⊑-right ⊑-ω = ⊑-right-å tt ⊑-ω
  ⊑-right (⊑-ν-ν-å åFV u⊑v) = ⊑-right-å åFV (⊑-ν-ν-å åFV u⊑v)
  ⊑-right (⊑-ν-↦-å åFV u⊑v) = ⊑-right-å åFV (⊑-ν-↦-å åFV u⊑v)
  ⊑-right ⊑-const = ⊑-right-å tt ⊑-const
  ⊑-right (⊑-⊔-R1-å åu u⊑v) = ⊑-right-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-right (⊑-⊔-R2-å åu u⊑v) = ⊑-right-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-right (⊑-fst-å åu u⊑v) = ⊑-right-å åu (⊑-fst-å åu u⊑v)
  ⊑-right (⊑-snd-å åu u⊑v) = ⊑-right-å åu (⊑-snd-å åu u⊑v)
  ⊑-right ⊑-nil = ⊑-right-å tt ⊑-nil
  ⊑-right (⊑-tup-å åus u⊑v u⊑v₁) = ⊑-right-å åus (⊑-tup-å åus u⊑v u⊑v₁)
  ⊑-right (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) = ⊑-right-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂)
  ⊑-right (⊑-left-å åu u⊑v) = ⊑-right-å åu (⊑-left-å åu u⊑v)
  ⊑-right (⊑-right-å åu u⊑v) = ⊑-right-å åu (⊑-right u⊑v)
  ⊑-right (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-right split) (⊑-right u⊑v) (⊑-right u⊑v₁)

  ⊑-ν-ν : ∀ {FV FV'} → FV ⊑ FV' → FV ⊢ν ⊑ FV' ⊢ν
  ⊑-ν-ν ⊑-ω = ⊑-ν-ν-å tt ⊑-ω
  ⊑-ν-ν (⊑-ν-ν-å åFV FV⊑) = ⊑-ν-ν-å åFV (⊑-ν-ν FV⊑)
  ⊑-ν-ν (⊑-ν-↦-å åFV FV⊑) = ⊑-ν-ν-å åFV (⊑-ν-↦-å åFV FV⊑)
  ⊑-ν-ν ⊑-const = ⊑-ν-ν-å tt ⊑-const
  ⊑-ν-ν (⊑-⊔-R1-å åu FV⊑) = ⊑-ν-ν-å åu (⊑-⊔-R1-å åu FV⊑)
  ⊑-ν-ν (⊑-⊔-R2-å åu FV⊑) = ⊑-ν-ν-å åu (⊑-⊔-R2-å åu FV⊑)
  ⊑-ν-ν (⊑-fst-å åu FV⊑) = ⊑-ν-ν-å åu (⊑-fst-å åu FV⊑)
  ⊑-ν-ν (⊑-snd-å åu FV⊑) = ⊑-ν-ν-å åu (⊑-snd-å åu FV⊑)
  ⊑-ν-ν ⊑-nil = ⊑-ν-ν-å tt ⊑-nil
  ⊑-ν-ν (⊑-tup-å åus FV⊑ FV⊑₁) = ⊑-ν-ν-å åus (⊑-tup-å åus FV⊑ FV⊑₁)
  ⊑-ν-ν (⊑-↦-å åu₂ åFV FV⊑ FV⊑₁ FV⊑₂) = ⊑-ν-ν-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV FV⊑ FV⊑₁ FV⊑₂)
  ⊑-ν-ν (⊑-left-å åu FV⊑) = ⊑-ν-ν-å åu (⊑-left-å åu FV⊑)
  ⊑-ν-ν (⊑-right-å åu FV⊑) = ⊑-ν-ν-å åu (⊑-right-å åu FV⊑)
  ⊑-ν-ν (⊑-split split FV⊑ FV⊑₁) = ⊑-split (split-ν split) (⊑-ν-ν FV⊑) (⊑-ν-ν FV⊑₁)

  ⊑-ν-↦ : ∀ {FV FV' u v} → FV ⊑ FV' → FV ⊢ν ⊑ FV' ⊢ u ↦ v
  ⊑-ν-↦ ⊑-ω = ⊑-ν-↦-å tt ⊑-ω
  ⊑-ν-↦ (⊑-ν-ν-å åFV FV⊑) = ⊑-ν-↦-å åFV (⊑-ν-ν-å åFV FV⊑)
  ⊑-ν-↦ (⊑-ν-↦-å åFV FV⊑) = ⊑-ν-↦-å åFV (⊑-ν-↦ FV⊑)
  ⊑-ν-↦ ⊑-const = ⊑-ν-↦-å tt ⊑-const
  ⊑-ν-↦ (⊑-⊔-R1-å åu FV⊑) = ⊑-ν-↦-å åu (⊑-⊔-R1-å åu FV⊑)
  ⊑-ν-↦ (⊑-⊔-R2-å åu FV⊑) = ⊑-ν-↦-å åu (⊑-⊔-R2-å åu FV⊑)
  ⊑-ν-↦ (⊑-fst-å åu FV⊑) = ⊑-ν-↦-å åu (⊑-fst-å åu FV⊑)
  ⊑-ν-↦ (⊑-snd-å åu FV⊑) = ⊑-ν-↦-å åu (⊑-snd-å åu FV⊑)
  ⊑-ν-↦ ⊑-nil = ⊑-ν-↦-å tt ⊑-nil
  ⊑-ν-↦ (⊑-tup-å åus FV⊑ FV⊑₁) = ⊑-ν-↦-å åus (⊑-tup-å åus FV⊑ FV⊑₁)
  ⊑-ν-↦ (⊑-↦-å åu₂ åFV FV⊑ FV⊑₁ FV⊑₂) = ⊑-ν-↦-å ⟨ åu₂ , åFV ⟩ (⊑-↦-å åu₂ åFV FV⊑ FV⊑₁ FV⊑₂)
  ⊑-ν-↦ (⊑-left-å åu FV⊑) = ⊑-ν-↦-å åu (⊑-left-å åu FV⊑)
  ⊑-ν-↦ (⊑-right-å åu FV⊑) = ⊑-ν-↦-å åu (⊑-right-å åu FV⊑)
  ⊑-ν-↦ (⊑-split split FV⊑ FV⊑₁) = ⊑-split (split-ν split) (⊑-ν-↦ FV⊑) (⊑-ν-↦ FV⊑₁)

  ⊑-refl : ∀ {v} → v ⊑ v
  ⊑-refl {ω} = ⊑-ω
  ⊑-refl {FV ⊢ν} = ⊑-ν-ν ⊑-refl
  ⊑-refl {const k} = ⊑-const
  ⊑-refl {⦅ u ∣} = ⊑-fst ⊑-refl
  ⊑-refl {∣ v ⦆} = ⊑-snd ⊑-refl
  ⊑-refl {∥ [] ∥} = ⊑-nil
  ⊑-refl {∥ v ∷ vs ∥} = ⊑-tup ⊑-refl ⊑-refl
  ⊑-refl {FV ⊢ v ↦ v₁} = ⊑-↦ ⊑-refl ⊑-refl ⊑-refl
  ⊑-refl {v ⊔ v₁} = ⊑-⊔-L (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl)
  ⊑-refl {left d} = ⊑-left ⊑-refl
  ⊑-refl {right d} = ⊑-right ⊑-refl


  proper-↦-inv : ∀ {FV u v} → Proper (FV ⊢ u ↦ v) → Proper FV × Proper u × Proper v
  proper-↦-inv (⊢'-↦-å Pd Pd₁ Pd₂ åw åFV) = ⟨ Pd , ⟨ Pd₁ , Pd₂ ⟩ ⟩
  proper-↦-inv {FV}{u}{v} (⊢'-split (FV ⊢ u ↦ v₁) (FV ⊢ u ↦ v₂) (split-↦ split) Pd Pd₁) 
    with proper-↦-inv Pd | proper-↦-inv Pd₁
  ... | ⟨ PFV , ⟨ Pu , Pv ⟩ ⟩  | ⟨ PFV' , ⟨ Pu' , Pv' ⟩ ⟩ = 
    ⟨ PFV' , ⟨ Pu' , ⊢'-split v₁ v₂ split Pv Pv' ⟩ ⟩
  proper-↦-inv {FV}{u}{v} (⊢'-split (FVL ⊢ u ↦ v) (FVR ⊢ u ↦ v) (split-↦-ann åw split) Pd Pd₁) 
    with proper-↦-inv Pd | proper-↦-inv Pd₁
  ... | ⟨ PFV , ⟨ Pu , Pv ⟩ ⟩  | ⟨ PFV' , ⟨ Pu' , Pv' ⟩ ⟩ = 
    ⟨ ⊢'-split FVL FVR split PFV PFV' , ⟨ Pu' , Pv' ⟩ ⟩


  proper-tup-inv : ∀ {n u us} → Proper (∥_∥ {suc n} (u ∷ us)) → Proper u × Proper (∥ us ∥)
  proper-tup-inv (⊢'-tup-å Ptup Ptup₁ åv åvs) = ⟨ Ptup , Ptup₁ ⟩
  proper-tup-inv (⊢'-split (∥ vL ∷ vs ∥) (∥ vR ∷ vs ∥) (split-tup-head split) Ptup Ptup₁) = 
    ⟨ ⊢'-split vL vR split (proj₁ (proper-tup-inv Ptup)) (proj₁ (proper-tup-inv Ptup₁)) , proj₂ (proper-tup-inv Ptup₁) ⟩
  proper-tup-inv (⊢'-split (∥ v ∷ vsL ∥) (∥ v ∷ vsR ∥) (split-tup-tail x split) Ptup Ptup₁) = 
    ⟨ proj₁ (proper-tup-inv Ptup₁) , ⊢'-split (∥ vsL ∥) (∥ vsR ∥) split (proj₂ (proper-tup-inv Ptup)) (proj₂ (proper-tup-inv Ptup₁)) ⟩

  proper-⊔-inv : ∀ {u v} → Proper (u ⊔ v) → Proper u × Proper v
  proper-⊔-inv (⊢'-split vL vR split-⊔ P⊔ P⊔₁) = ⟨ P⊔ , P⊔₁ ⟩


  split-unique : ∀ {u uL uR} → uL ◃ u ▹ uR → ∀ {uL' uR'} → uL' ◃ u ▹ uR' → uL' ≡ uL × uR' ≡ uR
  split-unique {u = .(_ ⊔ _)} split-⊔ split-⊔ = ⟨ refl , refl ⟩
  split-unique {u = .(_ ⊢ν)} (split-ν split) (split-ν split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = .(_ ⊢ _ ↦ _)} (split-↦ split) (split-↦ split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = (FV ⊢ u ↦ v)} (split-↦ split) (split-↦-ann åw split') 
    = ⊥-elim (unsplittable v åw split)
  split-unique {u = (FV ⊢ u ↦ v)} (split-↦-ann åw split) (split-↦ split') 
    = ⊥-elim (unsplittable v åw split')
  split-unique {u = .(_ ⊢ _ ↦ _)} (split-↦-ann åw split) (split-↦-ann åw₁ split') 
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = .(⦅ _ ∣)} (split-fst split) (split-fst split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = .(∣ _ ⦆)} (split-snd split) (split-snd split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = .(∥ _ ∷ _ ∥)} (split-tup-head split) (split-tup-head split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = (∥ u ∷ us ∥)} (split-tup-head split) (split-tup-tail x split') 
    = ⊥-elim (unsplittable u x split)
  split-unique {u = (∥ u ∷ us ∥)} (split-tup-tail x split) (split-tup-head split') 
    = ⊥-elim (unsplittable u x split')
  split-unique {u = .(∥ _ ∷ _ ∥)} (split-tup-tail x split) (split-tup-tail x₁ split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = .(left _)} (split-left split) (split-left split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩
  split-unique {u = .(right _)} (split-right split) (split-right split')
     with split-unique split split'
  ... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩

  ⊑-inversion-split-L : ∀ {u v v₁ v₂} → u ⊑ v → v₁ ◃ v ▹ v₂ → Atomic u → u ⊑ v₁ ⊎ u ⊑ v₂
  ⊑-inversion-split-L ⊑-ω split åu = inj₁ ⊑-ω
  ⊑-inversion-split-L (⊑-ν-ν-å åFV u⊑v) (split-ν split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-ν-ν-å åFV x)
  ... | inj₂ y = inj₂ (⊑-ν-ν-å åFV y)
  ⊑-inversion-split-L (⊑-ν-↦-å åFV u⊑v) (split-↦ split) åu = inj₁ (⊑-ν-↦-å åu u⊑v)
  ⊑-inversion-split-L (⊑-ν-↦-å åFV u⊑v) (split-↦-ann åw split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-ν-↦-å åFV x)
  ... | inj₂ y = inj₂ (⊑-ν-↦-å åFV y)
  ⊑-inversion-split-L (⊑-⊔-R1-å åu₁ u⊑v) split-⊔ åu = inj₁ u⊑v
  ⊑-inversion-split-L (⊑-⊔-R2-å åu₁ u⊑v) split-⊔ åu = inj₂ u⊑v
  ⊑-inversion-split-L (⊑-fst-å åu₁ u⊑v) (split-fst split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-fst-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-fst-å åu₁ y)
  ⊑-inversion-split-L (⊑-snd-å åu₁ u⊑v) (split-snd split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-snd-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-snd-å åu₁ y)
  ⊑-inversion-split-L (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-head split) åu 
    with ⊑-inversion-split-L u⊑v split (proj₁ åu)
  ... | inj₁ x = inj₁ (⊑-tup-å åu x u⊑v₁)
  ... | inj₂ y = inj₂ (⊑-tup-å åu y u⊑v₁)
  ⊑-inversion-split-L (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-tail x split) åu
    with ⊑-inversion-split-L u⊑v₁ split (proj₂ åu)
  ... | inj₁ x = inj₁ (⊑-tup-å åu u⊑v x)
  ... | inj₂ y = inj₂ (⊑-tup-å åu u⊑v y)
  ⊑-inversion-split-L (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) (split-↦ split) åu
    with ⊑-inversion-split-L u⊑v₁ split (proj₁ åu)
  ... | inj₁ x = inj₁ (⊑-↦-å (proj₁ åu) (proj₂ åu) u⊑v x u⊑v₂)
  ... | inj₂ y = inj₂ (⊑-↦-å (proj₁ åu) (proj₂ åu) u⊑v y u⊑v₂)
  ⊑-inversion-split-L (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) (split-↦-ann åw split) åu
    with ⊑-inversion-split-L u⊑v split (proj₂ åu)
  ... | inj₁ x = inj₁ (⊑-↦-å (proj₁ åu) (proj₂ åu) x u⊑v₁ u⊑v₂)
  ... | inj₂ y = inj₂ (⊑-↦-å (proj₁ åu) (proj₂ åu) y u⊑v₁ u⊑v₂)
  ⊑-inversion-split-L (⊑-left-å åu₁ u⊑v) (split-left split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-left-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-left-å åu₁ y)
  ⊑-inversion-split-L (⊑-right-å åu₁ u⊑v) (split-right split) åu
    with ⊑-inversion-split-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-right-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-right-å åu₁ y)
  ⊑-inversion-split-L {u} (⊑-split split₁ u⊑v u⊑v₁) split åu 
    = ⊥-elim (unsplittable u åu split₁)


  ⊑-inversion-split-R : ∀ {u v u₁ u₂} → u ⊑ v → u₁ ◃ u ▹ u₂ → u₁ ⊑ v × u₂ ⊑ v
  ⊑-inversion-split-R (⊑-ν-ν-å åFV u⊑v) (split-ν split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-ν-ν IH₁ , ⊑-ν-ν IH₂ ⟩
  ⊑-inversion-split-R (⊑-ν-↦-å åFV u⊑v) (split-ν split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-ν-↦ IH₁ , ⊑-ν-↦ IH₂ ⟩
  ⊑-inversion-split-R (⊑-⊔-R1-å åu u⊑v) split with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-⊔-R1 IH₁ , ⊑-⊔-R1 IH₂ ⟩
  ⊑-inversion-split-R (⊑-⊔-R2-å åu u⊑v) split with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-⊔-R2 IH₁ , ⊑-⊔-R2 IH₂ ⟩
  ⊑-inversion-split-R (⊑-fst-å åu u⊑v) (split-fst split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-fst IH₁ , ⊑-fst IH₂ ⟩
  ⊑-inversion-split-R (⊑-snd-å åu u⊑v) (split-snd split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-snd IH₁ , ⊑-snd IH₂ ⟩
  ⊑-inversion-split-R (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-head split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-tup IH₁ u⊑v₁ , ⊑-tup IH₂ u⊑v₁ ⟩
  ⊑-inversion-split-R (⊑-tup-å åus u⊑v u⊑v₁) (split-tup-tail x split)
    with ⊑-inversion-split-R u⊑v₁ split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-tup u⊑v IH₁ , ⊑-tup u⊑v IH₂ ⟩
  ⊑-inversion-split-R (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) (split-↦ split)
    with ⊑-inversion-split-R u⊑v₁ split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-↦ u⊑v u⊑v₂ IH₁ , ⊑-↦ u⊑v u⊑v₂ IH₂ ⟩
  ⊑-inversion-split-R (⊑-↦-å åu₂ åFV u⊑v u⊑v₁ u⊑v₂) (split-↦-ann åw split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-↦ IH₁ u⊑v₂ u⊑v₁ , ⊑-↦ IH₂ u⊑v₂ u⊑v₁ ⟩
  ⊑-inversion-split-R (⊑-left-å åu u⊑v) (split-left split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-left IH₁ , ⊑-left IH₂ ⟩
  ⊑-inversion-split-R (⊑-right-å åu u⊑v) (split-right split)
    with ⊑-inversion-split-R u⊑v split
  ... | ⟨ IH₁ , IH₂ ⟩ = ⟨ ⊑-right IH₁ , ⊑-right IH₂ ⟩
  ⊑-inversion-split-R {u}{v} (⊑-split split₁ u⊑v u⊑v₁) split with split-unique split₁ split
  ... | ⟨ refl , refl ⟩ = ⟨ u⊑v , u⊑v₁ ⟩


{-
  proper-split-L : ∀ {v v₁ v₂} → Proper v → v₁ ◃ v ▹ v₂ → Proper v₁
  proper-split-L .{_ ⊢ _ ↦ _} (⊢'-↦-å {FV}{v}{v'} Pv Pv₁ åv₂) split = ⊥-elim (unsplittable (FV ⊢ v ↦ v') åv₂ split)
  proper-split-L .{⦅ _ ∣} (⊢'-fst-å {v} Pv åv) split = ⊥-elim (unsplittable ⦅ v ∣ åv split)
  proper-split-L .{∣ _ ⦆} (⊢'-snd-å {v} Pv åv) split = ⊥-elim (unsplittable ∣ v ⦆ åv split) 
  proper-split-L .{∥ _ ∷ _ ∥} (⊢'-tup-å {n}{v}{vs} Pv Pv₁ åv åvs) split = ⊥-elim (unsplittable (∥ v ∷ vs ∥) ⟨ åv , åvs ⟩ split)
  proper-split-L .{left _} (⊢'-left-å {u} Pu åu) split = ⊥-elim (unsplittable (left u) åu split)
  proper-split-L .{right _} (⊢'-right-å {u} Pu åu) split = ⊥-elim (unsplittable (right u) åu split)
  proper-split-L .{_} (⊢'-split vL vR split₁ Pv Pv₁) split = subst Proper (proj₁ (split-unique split split₁)) Pv

  proper-split-R : ∀ {v v₁ v₂} → Proper v → v₁ ◃ v ▹ v₂ → Proper v₂
  proper-split-R .{_ ⊢ _ ↦ _} (⊢'-↦-å {FV}{v}{v'} Pv Pv₁ åv₂) split = ⊥-elim (unsplittable (FV ⊢ v ↦ v') åv₂ split)
  proper-split-R .{⦅ _ ∣} (⊢'-fst-å {v} Pv åv) split = ⊥-elim (unsplittable ⦅ v ∣ åv split)
  proper-split-R .{∣ _ ⦆} (⊢'-snd-å {v} Pv åv) split = ⊥-elim (unsplittable ∣ v ⦆ åv split) 
  proper-split-R .{∥ _ ∷ _ ∥} (⊢'-tup-å {n}{v}{vs} Pv Pv₁ åv åvs) split = ⊥-elim (unsplittable (∥ v ∷ vs ∥) ⟨ åv , åvs ⟩ split)
  proper-split-R .{left _} (⊢'-left-å {u} Pu åu) split = ⊥-elim (unsplittable (left u) åu split)
  proper-split-R .{right _} (⊢'-right-å {u} Pu åu) split = ⊥-elim (unsplittable (right u) åu split)
  proper-split-R .{_} (⊢'-split vL vR split₁ Pv Pv₁) split = subst Proper (proj₂ (split-unique split split₁)) Pv₁
-}

  ⊑-trans-proper : ∀ v → Proper v → ∀ u w → u ⊑ v → v ⊑ w → u ⊑ w
  ⊑-trans-proper .ω ⊢'-ω .ω w ⊑-ω v⊑w = v⊑w
  ⊑-trans-proper .ω ⊢'-ω u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper ω ⊢'-ω u₁ w u⊑v v⊑w) (⊑-trans-proper ω ⊢'-ω u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(_ ⊢ν) (⊢'-ν PFV åFV) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(_ ⊢ν) (⊢'-ν {FV} PFV åFV) .(_ ⊢ν) w (⊑-ν-ν-å {FV₁} åFV₁ FV⊑) v⊑w
    = G (FV₁ ⊢ν) w (⊑-ν-ν-å åFV₁ FV⊑) v⊑w (⊑-trans-proper FV PFV)
    where
    G : ∀ u w → u ⊑ FV ⊢ν → FV ⊢ν ⊑ w → (∀ u w → u ⊑ FV → FV ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω v⊑w IH = ⊑-ω
    G .(_ ⊢ν) .(_ ⊢ν) (⊑-ν-ν-å {FV'}{FV₁'} åFV' u⊑v) (⊑-ν-ν-å {FV''}{FV₁''} åFV'' v⊑w) IH 
      = ⊑-ν-ν-å åFV' (IH FV' FV₁'' u⊑v v⊑w)
    G .(_ ⊢ν) .(_ ⊢ _ ↦ _) (⊑-ν-ν-å {FV'}{FV₁'} åFV' u⊑v) (⊑-ν-↦-å {FV''}{FV₁''} åFV'' v⊑w) IH 
      = ⊑-ν-↦-å åFV' (IH FV' FV₁'' u⊑v v⊑w)
    G .(_ ⊢ν) .(_ ⊔ _) (⊑-ν-ν-å {FV'}{FV₁'} åFV' u⊑v) (⊑-⊔-R1-å {u'}{v'}{w'} åu v⊑w) IH 
      = ⊑-⊔-R1-å åFV' (G (FV' ⊢ν) v' (⊑-ν-ν-å åFV' u⊑v) v⊑w IH)
    G .(_ ⊢ν) .(_ ⊔ _) (⊑-ν-ν-å {FV'}{FV₁'} åFV' u⊑v) (⊑-⊔-R2-å {u'}{v'}{w'} åu v⊑w) IH 
      = ⊑-⊔-R2-å åFV' (G (FV' ⊢ν) w' (⊑-ν-ν-å åFV' u⊑v) v⊑w IH)
    G .(_ ⊢ν) w (⊑-ν-ν-å åFV' u⊑v) (⊑-split split v⊑w v⊑w₁) IH 
      = ⊥-elim (unsplittable (FV ⊢ν) åFV split)
    G u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w IH = 
      ⊑-split split (G u₁ w u⊑v v⊑w IH) (G u₂ w u⊑v₁ v⊑w IH)
  ⊑-trans-proper (FV ⊢ν) (⊢'-ν PFV åFV) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (FV ⊢ν) (⊢'-ν PFV åFV) u₁ w u⊑v v⊑w) (⊑-trans-proper (FV ⊢ν) (⊢'-ν PFV åFV) u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(const k) (⊢'-const k) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(const k) (⊢'-const k) .(const k) w ⊑-const v⊑w = v⊑w
  ⊑-trans-proper .(const k) (⊢'-const k) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (const k) (⊢'-const k) u₁ w u⊑v v⊑w) 
                  (⊑-trans-proper (const k) (⊢'-const k) u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(_ ⊢ _ ↦ _) (⊢'-↦-å {FV}{v₁}{v₂} PFV Pv Pv₁ åv₂ åFV) u w u⊑v v⊑w = 
      G u w u⊑v v⊑w (⊑-trans-proper FV PFV) (⊑-trans-proper v₁ Pv) (⊑-trans-proper v₂ Pv₁)
    where
    G : ∀ u w → u ⊑ FV ⊢ v₁ ↦ v₂ → FV ⊢ v₁ ↦ v₂ ⊑ w 
                              → (∀ u w → u ⊑ FV → FV ⊑ w → u ⊑ w)
                              → (∀ u w → u ⊑ v₁ → v₁ ⊑ w → u ⊑ w) 
                              → (∀ u w → u ⊑ v₂ → v₂ ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω v⊑w IH₁ IH₂ IH₃ = ⊑-ω
    G (FV' ⊢ν) .(_ ⊔ _) (⊑-ν-↦-å PFV' åFV') (⊑-⊔-R1-å {_}{w₁}{w₂} åu v⊑w) IH₁ IH₂ IH₃ = 
      ⊑-⊔-R1-å PFV' (G (FV' ⊢ν) w₁ (⊑-ν-↦-å PFV' åFV') v⊑w IH₁ IH₂ IH₃)
    G (FV' ⊢ν) .(_ ⊔ _) (⊑-ν-↦-å PFV' åFV') (⊑-⊔-R2-å {_}{w₁}{w₂} åu v⊑w) IH₁ IH₂ IH₃ = 
      ⊑-⊔-R2-å PFV' (G (FV' ⊢ν) w₂ (⊑-ν-↦-å PFV' åFV') v⊑w IH₁ IH₂ IH₃)
    G (FV' ⊢ν) (FV'' ⊢ _ ↦ _) (⊑-ν-↦-å PFV' åFV')  (⊑-↦-å åu₂ åFV FV⊑ v⊑w v⊑w₁) IH₁ IH₂ IH₃ 
      = ⊑-ν-↦ (IH₁ FV' FV'' åFV' FV⊑)
    G (FV' ⊢ν) w (⊑-ν-↦-å PFV' åFV') (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ IH₃ = ⊥-elim (unsplittable (FV ⊢ v₁ ↦ v₂) ⟨ åv₂ , åFV ⟩ split)
    G .(_ ⊢ _ ↦ _) .(_ ⊔ _) (⊑-↦-å {FV₁}{FV₂}{u₁}{u₂} åu₂ åFV FV⊑ u⊑v u⊑v₁) (⊑-⊔-R1-å {_}{w₁} åu v⊑w) IH₁ IH₂ IH₃ = 
      ⊑-⊔-R1-å ⟨ åu₂ , åFV ⟩ (G (FV₁ ⊢ u₁ ↦ u₂) w₁ (⊑-↦-å åu₂ åFV FV⊑ u⊑v u⊑v₁) v⊑w IH₁ IH₂ IH₃)
    G .(_ ⊢ _ ↦ _) .(_ ⊔ _) (⊑-↦-å {FV₁}{FV₂}{u₁}{u₂} åu₂ åFV FV⊑ u⊑v u⊑v₁) (⊑-⊔-R2-å {_}{_}{w₂} åu v⊑w) IH₁ IH₂ IH₃ = 
      ⊑-⊔-R2-å ⟨ åu₂ , åFV ⟩ (G (FV₁ ⊢ u₁ ↦ u₂) w₂ (⊑-↦-å åu₂ åFV FV⊑ u⊑v u⊑v₁) v⊑w IH₁ IH₂ IH₃)
    G .(_ ⊢ _ ↦ _) .(_ ⊢ _ ↦ _) (⊑-↦-å {FV₁}{FV₂}{u₁}{u₂} åu₂ åFV FV⊑ u⊑v u⊑v₁) 
                                 (⊑-↦-å {FV'}{FV''}{u'}{u''}{w₁}{w₂} åu₃ åFV' FV'⊑ v⊑w v⊑w₁) IH₁ IH₂ IH₃ = 
        ⊑-↦-å åu₂ åFV (IH₁ FV₁ FV'' FV⊑ FV'⊑) (IH₃ u₂ w₂ u⊑v v⊑w) (IH₂ w₁ u₁ v⊑w₁ u⊑v₁)
    G .(_ ⊢ _ ↦ _) w (⊑-↦-å {FV₁}{FV₂}{u₁}{u₂} åu₂ åFV' FV⊑ u⊑v u⊑v₁) (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ IH₃ = 
      ⊥-elim (unsplittable (FV₂ ⊢ v₁ ↦ v₂) ⟨ åv₂ , åFV ⟩  split)
    G u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w IH₁ IH₂ IH₃ = 
      ⊑-split split (G u₁ w u⊑v v⊑w IH₁ IH₂ IH₃) (G u₂ w u⊑v₁ v⊑w IH₁ IH₂ IH₃)
  ⊑-trans-proper .(⦅ _ ∣) (⊢'-fst-å Pv åv₁) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(⦅ _ ∣) (⊢'-fst-å {v} Pv åv) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper ⦅ v ∣ (⊢'-fst-å Pv åv) u₁ w u⊑v v⊑w)
                  (⊑-trans-proper ⦅ v ∣ (⊢'-fst-å Pv åv) u₂ w u⊑v₁ v⊑w)  
  ⊑-trans-proper .(⦅ _ ∣) (⊢'-fst-å {v} Pv åv) .(⦅ _ ∣) w (⊑-fst-å {u} åu u⊑v) v⊑w
    = G (⦅ u ∣) w (⊑-fst-å åu u⊑v) v⊑w (⊑-trans-proper v Pv)
    where
    G : ∀ u w → u ⊑ ⦅ v ∣ → ⦅ v ∣ ⊑ w → (∀ u w → u ⊑ v → v ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω Lv⊑w IH = ⊑-ω
    G .(⦅ _ ∣) .(_ ⊔ _) (⊑-fst-å {u₁} {v₁} åu u⊑Lv) (⊑-⊔-R1-å {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-⊔-R1-å åu (G (⦅ u₁ ∣) w₁ (⊑-fst-å åu u⊑Lv) Lv⊑w IH)
    G .(⦅ _ ∣) .(_ ⊔ _) (⊑-fst-å {u₁} {v₁} åu u⊑Lv) (⊑-⊔-R2-å {_} {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-⊔-R2-å åu (G (⦅ u₁ ∣) w₁ (⊑-fst-å åu u⊑Lv) Lv⊑w IH)
    G .(⦅ _ ∣) .(⦅ _ ∣) (⊑-fst-å {u₁} {v₁} åu u⊑Lv) (⊑-fst-å {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-fst-å åu (IH u₁ w₁ u⊑Lv Lv⊑w)
    G .(⦅ _ ∣) w (⊑-fst-å åu u⊑Lv) (⊑-split split Lv⊑w Lv⊑w₁) IH = 
      ⊥-elim (unsplittable (⦅ v ∣) åv split)
    G u w (⊑-split {u} {u₁} {u₂} split u⊑Lv u⊑Lv₁) Lv⊑w IH = 
      ⊑-split split (G u₁ w u⊑Lv Lv⊑w IH) (G u₂ w u⊑Lv₁ Lv⊑w IH)
  ⊑-trans-proper .(∣ _ ⦆) (⊢'-snd-å Pv åv₂) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(∣ _ ⦆) (⊢'-snd-å {v} Pv åv) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper ∣ v ⦆ (⊢'-snd-å Pv åv) u₁ w u⊑v v⊑w)
                  (⊑-trans-proper ∣ v ⦆ (⊢'-snd-å Pv åv) u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(∣ _ ⦆) (⊢'-snd-å {v} Pv åv) .(∣ _ ⦆) w (⊑-snd-å {u} åu u⊑v) v⊑w 
    = G (∣ u ⦆) w (⊑-snd-å åu u⊑v) v⊑w (⊑-trans-proper v Pv)
    where
    G : ∀ u w → u ⊑ ∣ v ⦆ → ∣ v ⦆ ⊑ w → (∀ u w → u ⊑ v → v ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω Lv⊑w IH = ⊑-ω
    G .(∣ _ ⦆) .(_ ⊔ _) (⊑-snd-å {u₁} {v₁} åu u⊑Lv) (⊑-⊔-R1-å {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-⊔-R1-å åu (G (∣ u₁ ⦆) w₁ (⊑-snd-å åu u⊑Lv) Lv⊑w IH)
    G .(∣ _ ⦆) .(_ ⊔ _) (⊑-snd-å {u₁} {v₁} åu u⊑Lv) (⊑-⊔-R2-å {_} {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-⊔-R2-å åu (G (∣ u₁ ⦆) w₁ (⊑-snd-å åu u⊑Lv) Lv⊑w IH)
    G .(∣ _ ⦆) .(∣ _ ⦆) (⊑-snd-å {u₁} {v₁} åu u⊑Lv) (⊑-snd-å {_} {w₁} åu₁ Lv⊑w) IH = 
      ⊑-snd-å åu (IH u₁ w₁ u⊑Lv Lv⊑w)
    G .(∣ _ ⦆) w (⊑-snd-å åu u⊑Lv) (⊑-split split Lv⊑w Lv⊑w₁) IH = 
      ⊥-elim (unsplittable (∣ v ⦆) åv split)
    G u w (⊑-split {u} {u₁} {u₂} split u⊑Lv u⊑Lv₁) Lv⊑w IH = 
      ⊑-split split (G u₁ w u⊑Lv Lv⊑w IH) (G u₂ w u⊑Lv₁ Lv⊑w IH)
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
    split-trans (FV ⊢ν) (⊢'-ν PFV åFV) u⊑v IH₁ IH₂ with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split åFV
    ... | inj₁ x = IH₁ (FV ⊢ν) w x vL⊑w
    ... | inj₂ y = IH₂ (FV ⊢ν) w y vR⊑w
    split-trans .(const k) (⊢'-const k) u⊑v IH₁ IH₂ with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split tt
    ... | inj₁ x = IH₁ (const k) w x vL⊑w
    ... | inj₂ y = IH₂ (const k) w y vR⊑w
    split-trans .(_ ⊢ _ ↦ _) (⊢'-↦-å {FV}{v₁}{v₂} Pu Pu₁ PFV åFV åv₂) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split ⟨ åFV , åv₂ ⟩
    ... | inj₁ x = IH₁ (FV ⊢ v₁ ↦ v₂) w x vL⊑w
    ... | inj₂ y = IH₂ (FV ⊢ v₁ ↦ v₂) w y vR⊑w
    split-trans .(⦅ _ ∣) (⊢'-fst-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split åu
    ... | inj₁ x = IH₁ ⦅ u ∣ w x vL⊑w
    ... | inj₂ y = IH₂ ⦅ u ∣ w y vR⊑w
    split-trans .(∣ _ ⦆) (⊢'-snd-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-inversion-split-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-inversion-split-L u⊑v split åu
    ... | inj₁ x = IH₁ (∣ u ⦆) w x vL⊑w
    ... | inj₂ y = IH₂ (∣ u ⦆) w y vR⊑w
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
  
  ⊑-trans : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
  ⊑-trans {u}{v}{w} u⊑v v⊑w = ⊑-trans-proper v (proper v) u w u⊑v v⊑w

  {-
  tup-cons : Value → Value → Value
  tup-cons u ω = ω
  tup-cons u (FV ⊢ν) = ω
  tup-cons u (const k) = ω
  tup-cons u (v ⊔ v₁) = ω
  tup-cons u (FV ⊢ v ↦ v₁) = ω
  tup-cons u (⦅ v ∣) = ω
  tup-cons u (∣ v ⦆) = ω
  tup-cons u (left v) = ω
  tup-cons u (right v) = ω
  tup-cons u (∥ vs ∥) = ∥ u ∷ vs ∥
-}

 {- This is the distributivity rule for each splitting -}
  ⊑-dist-⊔ : ∀ {v vL vR}
       → vL ◃ v ▹ vR
       ----------------------
       → v ⊑ vL ⊔ vR
  ⊑-dist-⊔ split = ⊑-split split (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl)


 {- for example, the usual distributivity rule for functions -}
  ⊑-dist-fun : ∀ {FV v wL wR}
     →  FV ⊢ v ↦ (wL ⊔ wR) ⊑ (FV ⊢ v ↦ wL) ⊔ (FV ⊢ v ↦ wR)
  ⊑-dist-fun {v}{wL}{wR} = ⊑-split (split-↦ split-⊔) (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl)
  

  ⊔⊑⊔ : ∀ {uL uR vL vR} → uL ⊑ vL → uR ⊑ vR → uL ⊔ uR ⊑ vL ⊔ vR
  ⊔⊑⊔ ⊑L ⊑R = ⊑-⊔-L (⊑-⊔-R1 ⊑L) (⊑-⊔-R2 ⊑R)

  pattern ⦅_,_⦆' u v = ⦅ u ∣ ⊔ ∣ v ⦆

  ⊑-dist-pair-example : ∀ {uL uR vL vR}
    → ⦅ uL ⊔ uR , vL ⊔ vR ⦆' ⊑ ⦅ uL , vL ⦆' ⊔ ⦅ uR , vR ⦆'
  ⊑-dist-pair-example {uL}{uR}{vL}{vR} = 
    ⊑-split split-⊔ (⊑-split (split-fst split-⊔) 
                              (⊑-⊔-R1 (⊑-⊔-R1 ⊑-refl)) 
                              (⊑-⊔-R2 (⊑-⊔-R1 ⊑-refl))) 
                    (⊑-split (split-snd split-⊔)
                              (⊑-⊔-R1 (⊑-⊔-R2 ⊑-refl))
                              (⊑-⊔-R2 (⊑-⊔-R2 ⊑-refl)))


  ordering : ValueOrdering value_struct
  ordering = record
   { _⊑_ = _⊑_
   ; ⊑-⊥ = ⊑-ω
   ; ⊑-conj-L = ⊑-⊔-L
   ; ⊑-conj-R1 = ⊑-⊔-R1
   ; ⊑-conj-R2 = ⊑-⊔-R2
   ; ⊑-trans = ⊑-trans
   ; ⊑-fun = ⊑-↦ ⊑-ω
   ; ⊑-refl = ⊑-refl
   ; ⊑-dist = ⊑-dist-fun
   }

  ⊔-closed : (Value → Set) → Set
  ⊔-closed D = ∀ u v → D u → D v 
          → Σ[ u⊔v' ∈ Value ] D u⊔v' × (u ⊔ v) ⊑ u⊔v'

  ⊑-closed : (Value → Set) → Set
  ⊑-closed D = ∀ u v → D v → u ⊑ v → D u

  ⊑-closure : Value → (Value → Set)
  ⊑-closure V d = d ⊑ V

  ⊑-closure-closed : ∀ V → ⊑-closed (⊑-closure V)
  ⊑-closure-closed V u v v⊑V u⊑v = ⊑-trans u⊑v v⊑V

  ⊑-closure-⊔-closed : ∀ V → ⊔-closed (⊑-closure V)
  ⊑-closure-⊔-closed V u v u⊑V v⊑V = 
    ⟨ V , ⟨ ⊑-refl , ⊑-split split-⊔ u⊑V v⊑V ⟩ ⟩

  singleton-⊔-closed : ∀ V → ⊔-closed (λ v → v ≡ V)
  singleton-⊔-closed V u .u refl refl = 
    ⟨ u , ⟨ refl , ⊑-⊔-L ⊑-refl ⊑-refl ⟩ ⟩



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
      → FV ⊢ v ↦ w ∈ u₁
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
  → FV ⊢ v ↦ w ⊑ v′ ↦ w′
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
