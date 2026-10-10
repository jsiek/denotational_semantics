
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

module Compiler.Model.Filter.Domain.AnnFun.Ordering where

  open import Compiler.Model.Filter.Domain.Util
  open import Primitives
  open import Compiler.Model.Filter.Domain.AnnFun.Values


  infix 5 _⊑_
  
  _≅_ : (u v : Value) → Set
  data _⊑_ : (u v : Value) → Set
  
  u ≅ v = u ⊑ v × v ⊑ u
  
  data _⊑_ where

    {- Atomic Rules :  we use å (\aa) as an abbreviation for atomic -}

    ⊑-ω : ∀ {v} → ω ⊑ v
  
    ⊑-ν-ν : ∀ {FV} → (FV ⊢ν) ⊑ (FV ⊢ν)

    ⊑-ν-↦ : ∀ {FV v w} → (FV ⊢ν) ⊑ FV ⊢ v ↦ w

    ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k

    ⊑-⊔-R1-å : ∀ {u v w}
       → (åu : Atomic u)     {- unnecessary, but clarifies which rule to use -}
       → u ⊑ v
     --------------------
       → u ⊑ v ⊔ w

    ⊑-⊔-R2-å : ∀ {u v w}
       → (åu : Atomic u)     {- ditto -}
       → u ⊑ w
      ------------------
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
  
    ⊑-tup-å : ∀ {n} {i : Fin n} {d d'}
       → (åu : Atomic d)
       → (u⊑v : d ⊑ d')
      --------------------------------
       → tup[ i ] d ⊑ tup[ i ] d'

    ⊑-↦-å : ∀ {FV u₁ u₂ v₁ v₂}
       → (åu₂ : Atomic u₂)
       → (dom⊑ : v₁ ⊑ u₁)
       → (⊑cod : u₂ ⊑ v₂)
       --------------------------------
       → FV ⊢ u₁ ↦ u₂ ⊑ FV ⊢ v₁ ↦ v₂ 

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

  ⊑-split-inv-R : ∀ {u v u₁ u₂} → u ⊑ v → u₁ ◃ u ▹ u₂ → u₁ ⊑ v × u₂ ⊑ v
  ⊑-split-inv-R (⊑-ν-ν {FV}) split = ⊥-elim (unsplittable (FV ⊢ν) tt split)
  ⊑-split-inv-R (⊑-ν-↦ {FV}) split = ⊥-elim (unsplittable (FV ⊢ν) tt split)
  ⊑-split-inv-R (⊑-⊔-R1-å {u} åu u⊑v) split = ⊥-elim (unsplittable u åu split)
  ⊑-split-inv-R (⊑-⊔-R2-å {u} åu u⊑v) split = ⊥-elim (unsplittable u åu split)
  ⊑-split-inv-R (⊑-fst-å {u} åu u⊑v) split = ⊥-elim (unsplittable ⦅ u ∣ åu split)
  ⊑-split-inv-R (⊑-snd-å {u} åu u⊑v) split = ⊥-elim (unsplittable ∣ u ⦆ åu split)
  ⊑-split-inv-R (⊑-tup-å {n}{i}{d} åd u⊑v) split = ⊥-elim (unsplittable (tup[ i ] d) åd split)
  ⊑-split-inv-R (⊑-↦-å {FV}{u₁}{u₂} åu₂ u⊑v u⊑v₁) split = ⊥-elim (unsplittable (FV ⊢ u₁ ↦ u₂) åu₂ split)
  ⊑-split-inv-R (⊑-left-å {u} åu u⊑v) split = ⊥-elim (unsplittable (left u) åu split)
  ⊑-split-inv-R (⊑-right-å {u} åu u⊑v) split = ⊥-elim (unsplittable (right u) åu split)
  ⊑-split-inv-R (⊑-split split₁ u⊑v u⊑v₁) split with split-unique split split₁
  ... | ⟨ refl , refl ⟩ = ⟨ u⊑v , u⊑v₁ ⟩


  ⊑-↦ : ∀ {FV u₁ u₂ v₁ v₂} → v₁ ⊑ u₁ →  u₂ ⊑ v₂ → FV ⊢ u₁ ↦ u₂ ⊑ FV ⊢ v₁ ↦ v₂
  ⊑-↦ {FV}{u₁}{u₂} dom⊑ ⊑cod with atomic? u₂
  ... | yes åu₂ = ⊑-↦-å åu₂ dom⊑ ⊑cod
  ... | no ¬åu₂ with ⊑cod 
  ... | ⊑-ω = ⊥-elim (¬åu₂ tt)
  ... | ⊑-ν-ν = ⊥-elim (¬åu₂ tt)
  ... | ⊑-ν-↦ = ⊥-elim (¬åu₂ tt)
  ... | ⊑-const = ⊥-elim (¬åu₂ tt)
  ... | ⊑-⊔-R1-å åu u₂⊑v₂ = ⊥-elim (¬åu₂ åu)
  ... | ⊑-⊔-R2-å åu u₂⊑v₂ = ⊥-elim (¬åu₂ åu)
  ... | ⊑-fst-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-snd-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-tup-å åu u₂⊑v₂ = ⊥-elim (¬åu₂ åu)
  ... | ⊑-↦-å åu₂ u₂⊑v₂ u₂⊑v₃ = ⊥-elim (¬åu₂ åu₂)
  ... | ⊑-left-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-right-å åu q = ⊥-elim (¬åu₂ åu)
  ... | ⊑-split split u₂⊑v₂ u₂⊑v₃ = ⊑-split (split-↦ split) (⊑-↦ dom⊑ u₂⊑v₂) (⊑-↦ dom⊑ u₂⊑v₃)



  ⊑-split-inv-L : ∀ {u v v₁ v₂} → u ⊑ v → v₁ ◃ v ▹ v₂ → Atomic u → u ⊑ v₁ ⊎ u ⊑ v₂
  ⊑-split-inv-L ⊑-ω split åu = inj₁ ⊑-ω
  ⊑-split-inv-L ⊑-ν-↦ (split-↦ split) åu = inj₁ ⊑-ν-↦
  ⊑-split-inv-L (⊑-⊔-R1-å åu₁ u⊑v) split-⊔ åu = inj₁ u⊑v
  ⊑-split-inv-L (⊑-⊔-R2-å åu₁ u⊑v) split-⊔ åu = inj₂ u⊑v
  ⊑-split-inv-L (⊑-fst-å åu₁ u⊑v) (split-fst split) åu
    with ⊑-split-inv-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-fst-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-fst-å åu₁ y)
  ⊑-split-inv-L (⊑-snd-å åu₁ u⊑v) (split-snd split) åu
    with ⊑-split-inv-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-snd-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-snd-å åu₁ y)
  ⊑-split-inv-L (⊑-tup-å åu₁ u⊑v) (split-tup split) åu 
    with ⊑-split-inv-L u⊑v split åu₁
  ... | inj₁ x = inj₁ (⊑-tup-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-tup-å åu₁ y)
  ⊑-split-inv-L (⊑-↦-å åu₂ u⊑v₁ u⊑v₂) (split-↦ split) åu
    with ⊑-split-inv-L u⊑v₂ split åu
  ... | inj₁ x = inj₁ (⊑-↦-å åu u⊑v₁ x)
  ... | inj₂ y = inj₂ (⊑-↦-å åu u⊑v₁ y)
  ⊑-split-inv-L (⊑-left-å åu₁ u⊑v) (split-left split) åu
    with ⊑-split-inv-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-left-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-left-å åu₁ y)
  ⊑-split-inv-L (⊑-right-å åu₁ u⊑v) (split-right split) åu
    with ⊑-split-inv-L u⊑v split åu
  ... | inj₁ x = inj₁ (⊑-right-å åu₁ x)
  ... | inj₂ y = inj₂ (⊑-right-å åu₁ y)
  ⊑-split-inv-L {u} (⊑-split split₁ u⊑v u⊑v₁) split åu 
    = ⊥-elim (unsplittable u åu split₁)


  ⊑-⊔-R1 : ∀ {u v₁ v₂} → u ⊑ v₁ → u ⊑ v₁ ⊔ v₂
  ⊑-⊔-R1 ⊑-ω = ⊑-ω
  ⊑-⊔-R1 ⊑-ν-ν = ⊑-⊔-R1-å tt ⊑-ν-ν
  ⊑-⊔-R1 ⊑-ν-↦ = ⊑-⊔-R1-å tt ⊑-ν-↦
  ⊑-⊔-R1 ⊑-const = ⊑-⊔-R1-å tt ⊑-const
  ⊑-⊔-R1 (⊑-⊔-R1-å åu u⊑v₁) = ⊑-⊔-R1-å åu (⊑-⊔-R1 u⊑v₁)
  ⊑-⊔-R1 (⊑-⊔-R2-å åu u⊑v₁) = ⊑-⊔-R1-å åu (⊑-⊔-R2-å åu u⊑v₁)
  ⊑-⊔-R1 (⊑-fst-å åu u⊑v) = ⊑-⊔-R1-å åu (⊑-fst-å åu u⊑v)
  ⊑-⊔-R1 (⊑-snd-å åu u⊑v) = ⊑-⊔-R1-å åu (⊑-snd-å åu u⊑v)
  ⊑-⊔-R1 (⊑-tup-å åu u⊑v₁) = ⊑-⊔-R1-å åu (⊑-tup-å åu u⊑v₁)
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
  ⊑-⊔-R2 (⊑-fst-å åu u⊑v) = ⊑-⊔-R2-å åu (⊑-fst-å åu u⊑v)
  ⊑-⊔-R2 (⊑-snd-å åu u⊑v) = ⊑-⊔-R2-å åu (⊑-snd-å åu u⊑v)
  ⊑-⊔-R2 (⊑-tup-å åu u⊑v₂) = ⊑-⊔-R2-å åu (⊑-tup-å åu u⊑v₂)
  ⊑-⊔-R2 (⊑-↦-å åu₂ u⊑v₂ u⊑v₃) = ⊑-⊔-R2-å åu₂ (⊑-↦-å åu₂ u⊑v₂ u⊑v₃)
  ⊑-⊔-R2 (⊑-left-å åu q) = ⊑-⊔-R2-å åu (⊑-left-å åu q)
  ⊑-⊔-R2 (⊑-right-å åu q) = ⊑-⊔-R2-å åu (⊑-right-å åu q)
  ⊑-⊔-R2 (⊑-split split u⊑v₂ u⊑v₃) = ⊑-split split (⊑-⊔-R2 u⊑v₂) (⊑-⊔-R2 u⊑v₃)

  ⊑-⊔-L : ∀ {u₁ u₂ v} → u₁ ⊑ v → u₂ ⊑ v → u₁ ⊔ u₂ ⊑ v
  ⊑-⊔-L 1⊑ 2⊑ = ⊑-split split-⊔ 1⊑ 2⊑

  ⊑-fst : ∀ {u v} → u ⊑ v → ⦅ u ∣ ⊑ ⦅ v ∣
  ⊑-fst ⊑-ω = ⊑-fst-å tt ⊑-ω
  ⊑-fst ⊑-ν-ν = ⊑-fst-å tt ⊑-ν-ν
  ⊑-fst ⊑-ν-↦ = ⊑-fst-å tt ⊑-ν-↦
  ⊑-fst ⊑-const = ⊑-fst-å tt ⊑-const
  ⊑-fst (⊑-⊔-R1-å åu u⊑v) = ⊑-fst-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-fst (⊑-⊔-R2-å åu u⊑v) = ⊑-fst-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-fst (⊑-fst-å åu u⊑v) = ⊑-fst-å åu (⊑-fst u⊑v)
  ⊑-fst (⊑-snd-å åu u⊑v) = ⊑-fst-å åu (⊑-snd-å åu u⊑v)
  ⊑-fst (⊑-tup-å åu u⊑v) = ⊑-fst-å åu (⊑-tup-å åu u⊑v)
  ⊑-fst (⊑-↦-å åu₂ u⊑v₁ u⊑v₂) = ⊑-fst-å åu₂ (⊑-↦-å åu₂ u⊑v₁ u⊑v₂)
  ⊑-fst (⊑-left-å åu u⊑v) = ⊑-fst-å åu (⊑-left-å åu u⊑v)
  ⊑-fst (⊑-right-å åu u⊑v) = ⊑-fst-å åu (⊑-right-å åu u⊑v)
  ⊑-fst (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-fst split) (⊑-fst u⊑v) (⊑-fst u⊑v₁)

  ⊑-snd : ∀ {u v} → u ⊑ v → ∣ u ⦆ ⊑ ∣ v ⦆
  ⊑-snd ⊑-ω = ⊑-snd-å tt ⊑-ω
  ⊑-snd ⊑-ν-ν = ⊑-snd-å tt ⊑-ν-ν
  ⊑-snd ⊑-ν-↦ = ⊑-snd-å tt ⊑-ν-↦
  ⊑-snd ⊑-const = ⊑-snd-å tt ⊑-const
  ⊑-snd (⊑-⊔-R1-å åu u⊑v) = ⊑-snd-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-snd (⊑-⊔-R2-å åu u⊑v) = ⊑-snd-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-snd (⊑-fst-å åu u⊑v) = ⊑-snd-å åu (⊑-fst-å åu u⊑v)
  ⊑-snd (⊑-snd-å åu u⊑v) = ⊑-snd-å åu (⊑-snd u⊑v)
  ⊑-snd (⊑-tup-å åu u⊑v) = ⊑-snd-å åu (⊑-tup-å åu u⊑v)
  ⊑-snd (⊑-↦-å åu₂ u⊑v₁ u⊑v₂) = ⊑-snd-å åu₂ (⊑-↦-å åu₂ u⊑v₁ u⊑v₂)
  ⊑-snd (⊑-left-å åu u⊑v) = ⊑-snd-å åu (⊑-left-å åu u⊑v)
  ⊑-snd (⊑-right-å åu u⊑v) = ⊑-snd-å åu (⊑-right-å åu u⊑v)
  ⊑-snd (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-snd split) (⊑-snd u⊑v) (⊑-snd u⊑v₁)

  ⊑-tup : ∀ {n}{i : Fin n}{u v} → u ⊑ v → tup[ i ] u ⊑ tup[ i ] v
  ⊑-tup {n} {i} ⊑-ω = ⊑-tup-å tt ⊑-ω
  ⊑-tup {n} {i} ⊑-ν-ν = ⊑-tup-å tt ⊑-ν-ν
  ⊑-tup {n} {i} ⊑-ν-↦ = ⊑-tup-å tt ⊑-ν-↦
  ⊑-tup {n} {i} ⊑-const = ⊑-tup-å tt ⊑-const
  ⊑-tup {n} {i} (⊑-⊔-R1-å åu u⊑v) = ⊑-tup-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-tup {n} {i} (⊑-⊔-R2-å åu u⊑v) = ⊑-tup-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-tup {n} {i} (⊑-fst-å åu u⊑v) = ⊑-tup-å åu (⊑-fst-å åu u⊑v)
  ⊑-tup {n} {i} (⊑-snd-å åu u⊑v) = ⊑-tup-å åu (⊑-snd-å åu u⊑v)
  ⊑-tup {n} {i} (⊑-tup-å åu u⊑v) = ⊑-tup-å åu (⊑-tup u⊑v)
  ⊑-tup {n} {i} (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-tup-å åu₂ (⊑-↦-å åu₂ u⊑v u⊑v₁)
  ⊑-tup {n} {i} (⊑-left-å åu u⊑v) = ⊑-tup-å åu (⊑-left-å åu u⊑v)
  ⊑-tup {n} {i} (⊑-right-å åu u⊑v) = ⊑-tup-å åu (⊑-right-å åu u⊑v)
  ⊑-tup {n} {i} (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-tup split) (⊑-tup u⊑v) (⊑-tup u⊑v₁)

  ⊑-left : ∀ {u v} → u ⊑ v → left u ⊑ left v
  ⊑-left ⊑-ω = ⊑-left-å tt ⊑-ω
  ⊑-left ⊑-ν-ν = ⊑-left-å tt ⊑-ν-ν
  ⊑-left ⊑-ν-↦ = ⊑-left-å tt ⊑-ν-↦
  ⊑-left ⊑-const = ⊑-left-å tt ⊑-const
  ⊑-left (⊑-⊔-R1-å åu u⊑v) = ⊑-left-å åu (⊑-⊔-R1-å åu u⊑v)
  ⊑-left (⊑-⊔-R2-å åu u⊑v) = ⊑-left-å åu (⊑-⊔-R2-å åu u⊑v)
  ⊑-left (⊑-fst-å åu u⊑v) = ⊑-left-å åu (⊑-fst-å åu u⊑v)
  ⊑-left (⊑-snd-å åu u⊑v) = ⊑-left-å åu (⊑-snd-å åu u⊑v)
  ⊑-left (⊑-tup-å åu u⊑v) = ⊑-left-å åu (⊑-tup-å åu u⊑v)
  ⊑-left (⊑-↦-å åu₂ u⊑v₁ u⊑v₂) = ⊑-left-å åu₂ (⊑-↦-å åu₂ u⊑v₁ u⊑v₂)
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
  ⊑-right (⊑-fst-å åu u⊑v) = ⊑-right-å åu (⊑-fst-å åu u⊑v)
  ⊑-right (⊑-snd-å åu u⊑v) = ⊑-right-å åu (⊑-snd-å åu u⊑v)
  ⊑-right (⊑-tup-å åu u⊑v) = ⊑-right-å åu (⊑-tup-å åu u⊑v)
  ⊑-right (⊑-↦-å åu₂ u⊑v₁ u⊑v₂) = ⊑-right-å åu₂ (⊑-↦-å åu₂ u⊑v₁ u⊑v₂)
  ⊑-right (⊑-left-å åu u⊑v) = ⊑-right-å åu (⊑-left-å åu u⊑v)
  ⊑-right (⊑-right-å åu u⊑v) = ⊑-right-å åu (⊑-right u⊑v)
  ⊑-right (⊑-split split u⊑v u⊑v₁) = ⊑-split (split-right split) (⊑-right u⊑v) (⊑-right u⊑v₁)



  ⊑-refl : ∀ {v} → v ⊑ v
  ⊑-refl {ω} = ⊑-ω
  ⊑-refl {FV ⊢ν} = ⊑-ν-ν
  ⊑-refl {const k} = ⊑-const
  ⊑-refl {⦅ u ∣} = ⊑-fst ⊑-refl
  ⊑-refl {∣ v ⦆} = ⊑-snd ⊑-refl
  ⊑-refl {(tup[ i ] d)} = ⊑-tup ⊑-refl
  ⊑-refl {FV ⊢ v ↦ v₁} = ⊑-↦ ⊑-refl ⊑-refl
  ⊑-refl {v ⊔ v₁} = ⊑-⊔-L (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl)
  ⊑-refl {left d} = ⊑-left ⊑-refl
  ⊑-refl {right d} = ⊑-right ⊑-refl

  {-
  proper-↦-inv : ∀ {FV u v} → Proper (FV ⊢ u ↦ v) → Proper u × Proper v
  proper-↦-inv (⊢'-↦-å Pd₁ Pd₂ åw) = ⟨ Pd₁ , Pd₂ ⟩
  proper-↦-inv {FV}{u}{v} (⊢'-split (FV ⊢ u ↦ v₁) (FV ⊢ u ↦ v₂) (split-↦ split) Pd Pd₁) 
    with proper-↦-inv Pd | proper-↦-inv Pd₁
  ... | ⟨ Pu , Pv ⟩  | ⟨ Pu' , Pv' ⟩ = 
    ⟨ Pu' , ⊢'-split v₁ v₂ split Pv Pv' ⟩


  proper-tup-inv : ∀ {n}{i : Fin n}{d} → Proper (tup[ i ] d) → Proper d
  proper-tup-inv (⊢'-tup-å Ptup åv) = Ptup
  proper-tup-inv (⊢'-split (tup[ i ] dL) (tup[ i ] dR) (split-tup split) Ptup Ptup') = 
    HOLE
  proper-⊔-inv : ∀ {u v} → Proper (u ⊔ v) → Proper u × Proper v
  proper-⊔-inv (⊢'-split vL vR split-⊔ P⊔ P⊔₁) = ⟨ P⊔ , P⊔₁ ⟩
-}



{-
  proper-split-L : ∀ {v v₁ v₂} → Proper v → v₁ ◃ v ▹ v₂ → Proper v₁
  proper-split-L .{_ ⊢ _ ↦ _} (⊢'-↦-å {FV}{v}{v'} Pv Pv₁ åv₂) split = ⊥-elim (unsplittable (FV ⊢ v ↦ v') åv₂ split)
  proper-split-L .{⦅ _ ∣} (⊢'-fst-å {v} Pv åv) split = ⊥-elim (unsplittable ⦅ v ∣ åv split)
  proper-split-L .{∣ _ ⦆} (⊢'-snd-å {v} Pv åv) split = ⊥-elim (unsplittable ∣ v ⦆ åv split) 
  proper-split-L .{∥ _ ∷ _ ∥} (⊢'-tup-å {n}{v}{vs} Pv Pv₁ åv åvs) split = ⊥-elim (unsplittable ((tup[ i ] d)) ⟨ åv , åvs ⟩ split)
  proper-split-L .{left _} (⊢'-left-å {u} Pu åu) split = ⊥-elim (unsplittable (left u) åu split)
  proper-split-L .{right _} (⊢'-right-å {u} Pu åu) split = ⊥-elim (unsplittable (right u) åu split)
  proper-split-L .{_} (⊢'-split vL vR split₁ Pv Pv₁) split = subst Proper (proj₁ (split-unique split split₁)) Pv

  proper-split-R : ∀ {v v₁ v₂} → Proper v → v₁ ◃ v ▹ v₂ → Proper v₂
  proper-split-R .{_ ⊢ _ ↦ _} (⊢'-↦-å {FV}{v}{v'} Pv Pv₁ åv₂) split = ⊥-elim (unsplittable (FV ⊢ v ↦ v') åv₂ split)
  proper-split-R .{⦅ _ ∣} (⊢'-fst-å {v} Pv åv) split = ⊥-elim (unsplittable ⦅ v ∣ åv split)
  proper-split-R .{∣ _ ⦆} (⊢'-snd-å {v} Pv åv) split = ⊥-elim (unsplittable ∣ v ⦆ åv split) 
  proper-split-R .{∥ _ ∷ _ ∥} (⊢'-tup-å {n}{v}{vs} Pv Pv₁ åv åvs) split = ⊥-elim (unsplittable ((tup[ i ] d)) ⟨ åv , åvs ⟩ split)
  proper-split-R .{left _} (⊢'-left-å {u} Pu åu) split = ⊥-elim (unsplittable (left u) åu split)
  proper-split-R .{right _} (⊢'-right-å {u} Pu åu) split = ⊥-elim (unsplittable (right u) åu split)
  proper-split-R .{_} (⊢'-split vL vR split₁ Pv Pv₁) split = subst Proper (proj₂ (split-unique split split₁)) Pv₁
-}

  ⊑-trans-proper : ∀ v → Proper v → ∀ u w → u ⊑ v → v ⊑ w → u ⊑ w
  ⊑-trans-proper .ω ⊢'-ω .ω w ⊑-ω v⊑w = v⊑w
  ⊑-trans-proper .ω ⊢'-ω u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper ω ⊢'-ω u₁ w u⊑v v⊑w) (⊑-trans-proper ω ⊢'-ω u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(_ ⊢ν) ⊢'-ν .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(_ ⊢ν) (⊢'-ν {FV}) .(_ ⊢ν) w (⊑-ν-ν {FV₁}) v⊑w = v⊑w
  ⊑-trans-proper (FV ⊢ν) ⊢'-ν u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (FV ⊢ν) ⊢'-ν u₁ w u⊑v v⊑w) (⊑-trans-proper (FV ⊢ν) ⊢'-ν u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(const k) (⊢'-const k) .ω w ⊑-ω v⊑w = ⊑-ω
  ⊑-trans-proper .(const k) (⊢'-const k) .(const k) w ⊑-const v⊑w = v⊑w
  ⊑-trans-proper .(const k) (⊢'-const k) u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w = 
    ⊑-split split (⊑-trans-proper (const k) (⊢'-const k) u₁ w u⊑v v⊑w) 
                  (⊑-trans-proper (const k) (⊢'-const k) u₂ w u⊑v₁ v⊑w)
  ⊑-trans-proper .(_ ⊢ _ ↦ _) (⊢'-↦-å {FV}{v₁}{v₂} Pv Pv₁ åv₂) u w u⊑v v⊑w = 
      G u w u⊑v v⊑w (⊑-trans-proper v₁ Pv) (⊑-trans-proper v₂ Pv₁)
    where
    G : ∀ u w → u ⊑ FV ⊢ v₁ ↦ v₂ → FV ⊢ v₁ ↦ v₂ ⊑ w
                              → (∀ u w → u ⊑ v₁ → v₁ ⊑ w → u ⊑ w) 
                              → (∀ u w → u ⊑ v₂ → v₂ ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω v⊑w IH₁ IH₂ = ⊑-ω
    G (FV' ⊢ν) .(_ ⊔ _) ⊑-ν-↦ (⊑-⊔-R1-å {_}{w₁}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R1-å tt (G (FV' ⊢ν) w₁ ⊑-ν-↦ v⊑w IH₁ IH₂)
    G (FV' ⊢ν) .(_ ⊔ _) ⊑-ν-↦ (⊑-⊔-R2-å {_}{w₁}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R2-å tt (G (FV' ⊢ν) w₂ ⊑-ν-↦ v⊑w IH₁ IH₂)
    G (FV' ⊢ν) (FV'' ⊢ _ ↦ _) ⊑-ν-↦  (⊑-↦-å åu₂ v⊑w v⊑w₁) IH₁ IH₂ 
      = ⊑-ν-↦
    G (FV' ⊢ν) w ⊑-ν-↦ (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ = ⊥-elim (unsplittable (FV ⊢ v₁ ↦ v₂) åv₂ split)
    G .(_ ⊢ _ ↦ _) .(_ ⊔ _) (⊑-↦-å {FV₁}{u₁}{u₂} åu₂ u⊑v u⊑v₁) (⊑-⊔-R1-å {_}{w₁} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R1-å åu₂ (G (FV₁ ⊢ u₁ ↦ u₂) w₁ (⊑-↦-å åu₂ u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(_ ⊢ _ ↦ _) .(_ ⊔ _) (⊑-↦-å {FV₁}{u₁}{u₂} åu₂ u⊑v u⊑v₁) (⊑-⊔-R2-å {_}{_}{w₂} åu v⊑w) IH₁ IH₂ = 
      ⊑-⊔-R2-å åu₂ (G (FV₁ ⊢ u₁ ↦ u₂) w₂ (⊑-↦-å åu₂ u⊑v u⊑v₁) v⊑w IH₁ IH₂)
    G .(_ ⊢ _ ↦ _) .(_ ⊢ _ ↦ _) (⊑-↦-å {FV₁}{u₁}{u₂} åu₂ u⊑v u⊑v₁) 
                                 (⊑-↦-å {FV'}{u'}{u''}{w₁}{w₂} åu₃ v⊑w v⊑w₁) IH₁ IH₂ = 
        ⊑-↦-å åu₂ (IH₁ w₁ u₁ v⊑w u⊑v) (IH₂ u₂ w₂ u⊑v₁ v⊑w₁)
    G .(_ ⊢ _ ↦ _) w (⊑-↦-å {FV₁}{u₁}{u₂} åu₂ u⊑v u⊑v₁) (⊑-split split v⊑w v⊑w₁) IH₁ IH₂ = 
      ⊥-elim (unsplittable (FV₁ ⊢ v₁ ↦ v₂) åv₂  split)
    G u w (⊑-split {_}{u₁}{u₂} split u⊑v u⊑v₁) v⊑w IH₁ IH₂ = 
      ⊑-split split (G u₁ w u⊑v v⊑w IH₁ IH₂) (G u₂ w u⊑v₁ v⊑w IH₁ IH₂)
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
  ⊑-trans-proper (tup[ i ] v) (⊢'-tup-å {n}{i}{v} Pv åv) u w u⊑v v⊑w = 
      G u w u⊑v v⊑w (⊑-trans-proper v Pv)
    where
    G : ∀ u w → u ⊑ tup[ i ] v → tup[ i ] v ⊑ w → (∀ u w → u ⊑ v → v ⊑ w → u ⊑ w) → u ⊑ w
    G .ω w ⊑-ω tupv⊑w IH = ⊑-ω
    G .(tup[ i ] _) .(_ ⊔ _) (⊑-tup-å {n}{i}{u₁} åu u⊑tupv) (⊑-⊔-R1-å {_}{v₁} åu₁ tupv⊑w) IH = 
      ⊑-⊔-R1-å åu (G (tup[ i ] u₁) v₁ (⊑-tup-å åu u⊑tupv) tupv⊑w IH)
    G .(tup[ i ] _) .(_ ⊔ _) (⊑-tup-å {n}{i}{u₁} åu u⊑tupv) (⊑-⊔-R2-å {_}{_}{w₁} åu₁ tupv⊑w) IH = 
      ⊑-⊔-R2-å åu (G (tup[ i ] u₁) w₁ (⊑-tup-å åu u⊑tupv) tupv⊑w IH)
    G .(tup[ i ] _) .(tup[ i ] _) (⊑-tup-å {n}{i}{u₁} åu u⊑tupv) (⊑-tup-å {n}{i}{_}{v₁} åu₁ tupv⊑w) IH = 
      ⊑-tup-å åu (IH u₁ v₁ u⊑tupv tupv⊑w)
    G .(tup[ i ] _) w (⊑-tup-å åu u⊑tupv) (⊑-split split tupv⊑w tupv⊑w₁) IH = 
      ⊥-elim (unsplittable (tup[ i ] v) åv split)
    G u w (⊑-split {u} {u₁} {u₂} split u⊑tupv u⊑tupv₁) tupv⊑w IH = 
      ⊑-split split (G u₁ w u⊑tupv tupv⊑w IH) (G u₂ w u⊑tupv₁ tupv⊑w IH)
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
    split-trans .ω ⊢'-ω u⊑v IH₁ IH₂ with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split tt
    ... | inj₁ x = IH₁ ω w x vL⊑w
    ... | inj₂ y = IH₂ ω w y vR⊑w
    split-trans (FV ⊢ν) ⊢'-ν u⊑v IH₁ IH₂ with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split tt
    ... | inj₁ x = IH₁ (FV ⊢ν) w x vL⊑w
    ... | inj₂ y = IH₂ (FV ⊢ν) w y vR⊑w
    split-trans .(const k) (⊢'-const k) u⊑v IH₁ IH₂ with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split tt
    ... | inj₁ x = IH₁ (const k) w x vL⊑w
    ... | inj₂ y = IH₂ (const k) w y vR⊑w
    split-trans .(_ ⊢ _ ↦ _) (⊢'-↦-å {FV}{v₁}{v₂} Pu Pu₁ åv₂) u⊑v IH₁ IH₂ 
      with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split åv₂
    ... | inj₁ x = IH₁ (FV ⊢ v₁ ↦ v₂) w x vL⊑w
    ... | inj₂ y = IH₂ (FV ⊢ v₁ ↦ v₂) w y vR⊑w
    split-trans .(⦅ _ ∣) (⊢'-fst-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split åu
    ... | inj₁ x = IH₁ ⦅ u ∣ w x vL⊑w
    ... | inj₂ y = IH₂ ⦅ u ∣ w y vR⊑w
    split-trans .(∣ _ ⦆) (⊢'-snd-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split åu
    ... | inj₁ x = IH₁ (∣ u ⦆) w x vL⊑w
    ... | inj₂ y = IH₂ (∣ u ⦆) w y vR⊑w
    split-trans .(tup[ _ ] _) (⊢'-tup-å {n}{i}{d} Pd åd) u⊑v IH₁ IH₂ 
      with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split åd
    ... | inj₁ x = IH₁ (tup[ i ] d) w x vL⊑w
    ... | inj₂ y = IH₂ (tup[ i ] d) w y vR⊑w
    split-trans .(left _) (⊢'-left-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split åu
    ... | inj₁ x = IH₁ (left u) w x vL⊑w
    ... | inj₂ y = IH₂ (left u) w y vR⊑w
    split-trans .(right _) (⊢'-right-å {u} Pu åu) u⊑v IH₁ IH₂ 
      with ⊑-split-inv-R v⊑w split
    ... | ⟨ vL⊑w , vR⊑w ⟩ with ⊑-split-inv-L u⊑v split åu
    ... | inj₁ x = IH₁ (right u) w x vL⊑w
    ... | inj₂ y = IH₂ (right u) w y vR⊑w
    split-trans u (⊢'-split uL uR split' Pu Pu₁) u⊑v IH₁ IH₂ 
      with ⊑-split-inv-R u⊑v split'
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
  
{-
  ⊑-dist-fst : ∀ {uL uR} → ⦅ uL ⊔ uR ∣ ⊑ ⦅ uL ∣ ⊔ ⦅ uR ∣
  ⊑-dist-fst = HOLE

  ⊑-dist-snd : ∀ {uL uR} → ∣ uL ⊔ uR ⦆ ⊑ ∣ uL ⦆ ⊔ ∣ uR ⦆
  ⊑-dist-snd = HOLE
    
  ⊑-dist-left : ∀ {uL uR} → left (uL ⊔ uR) ⊑ left uL ⊔ left uR
  ⊑-dist-left = HOLE
    
  ⊑-dist-right : ∀ {uL uR} → right (uL ⊔ uR) ⊑ right uL ⊔ right uR
  ⊑-dist-right = HOLE
    
  ⊑-dist-tup : ∀ {vL vR vs} → ∥ vL ⊔ vR ∷ vs ∥ ⊑ ∥ vL ∷ vs ∥ ⊔ ∥ vR ∷ vs ∥
  ⊑-dist-tup = HOLE

-}

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
   ; ⊑-fun = ⊑-↦
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

