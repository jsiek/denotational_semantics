open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)

open import Variables
open import Primitives
open import ValueBCDConst


module BelowBCDConst where

Below⊥-⊑ : ∀{v w : Value} → Below⊥ v → w ⊑ v → Below⊥ w
Below⊥-⊑ bv ⊑-⊥ = tt
Below⊥-⊑ bv ⊑-const = bv
Below⊥-⊑ bv (⊑-conj-L w⊑v w⊑v₁) = ⟨ Below⊥-⊑ bv w⊑v , Below⊥-⊑ bv w⊑v₁ ⟩
Below⊥-⊑ bv (⊑-conj-R1 w⊑v) = Below⊥-⊑ (proj₁ bv) w⊑v
Below⊥-⊑ bv (⊑-conj-R2 w⊑v) = Below⊥-⊑ (proj₂ bv) w⊑v
Below⊥-⊑ bv (⊑-trans w⊑v w⊑v₁) = Below⊥-⊑ (Below⊥-⊑ bv w⊑v₁) w⊑v
Below⊥-⊑ bv (⊑-fun w⊑v w⊑v₁) = bv
Below⊥-⊑ bv ⊑-dist = proj₁ bv

v⊑⊥→Below⊥ : ∀{v : Value} → v ⊑ ⊥ → Below⊥ v
v⊑⊥→Below⊥ ⊑-⊥ = tt
v⊑⊥→Below⊥ (⊑-conj-L v⊑⊥ v⊑⊥₁) = ⟨ v⊑⊥→Below⊥ v⊑⊥ , v⊑⊥→Below⊥ v⊑⊥₁ ⟩
v⊑⊥→Below⊥ (⊑-trans v⊑⊥ v⊑⊥₁) = Below⊥-⊑ (v⊑⊥→Below⊥ v⊑⊥₁) v⊑⊥


Below⊥→BelowConst : ∀{B : Base}{k : base-rep B}{v : Value}
   → Below⊥ v
   → BelowConst k v
Below⊥→BelowConst {v = ⊥} b⊥v = tt
Below⊥→BelowConst {B}{k}{const {B′} k′} b⊥v
    with base-eq? B B′ 
... | yes eq rewrite eq = ⊥-elim b⊥v
... | no neq = b⊥v
Below⊥→BelowConst {v = v ↦ w} b⊥v = b⊥v
Below⊥→BelowConst {v = v₁ ⊔ v₂} ⟨ fst , snd ⟩ =
  ⟨ Below⊥→BelowConst fst , Below⊥→BelowConst snd ⟩

BelowConst-⊥ : ∀{B : Base}{k : base-rep B}{v : Value}
   → v ⊑ ⊥
   → BelowConst k v
BelowConst-⊥ v⊑⊥ = Below⊥→BelowConst (v⊑⊥→Below⊥ v⊑⊥)

BelowConst-⊑ : ∀{B : Base}{k : base-rep B}{v w : Value}
   → BelowConst k v
   → w ⊑ v
   → BelowConst k w
BelowConst-⊑ bkv ⊑-⊥ = tt
BelowConst-⊑ {B} bkv (⊑-const{B′})
    with base-eq? B B′
... | yes eq rewrite eq = bkv
... | no neq = bkv
BelowConst-⊑ bkv (⊑-conj-L w⊑v w⊑v₁) =
  ⟨ BelowConst-⊑ bkv w⊑v , BelowConst-⊑ bkv w⊑v₁ ⟩
BelowConst-⊑ bkv (⊑-conj-R1 w⊑v) = BelowConst-⊑ (proj₁ bkv) w⊑v
BelowConst-⊑ bkv (⊑-conj-R2 w⊑v) = BelowConst-⊑ (proj₂ bkv) w⊑v
BelowConst-⊑ bkv (⊑-trans w⊑v w⊑v₁) = BelowConst-⊑ (BelowConst-⊑ bkv w⊑v₁) w⊑v
BelowConst-⊑ bkv (⊑-fun w⊑v w⊑v₁) = bkv
BelowConst-⊑ bkv ⊑-dist = proj₁ bkv

⊑k→BelowConstk : ∀{B : Base}{k : base-rep B}{v : Value}
   → v ⊑ const {B} k
   → BelowConst k v
⊑k→BelowConstk ⊑-⊥ = tt
⊑k→BelowConstk {B} (⊑-const{B′})
    with base-eq? B B′
... | yes eq rewrite eq = refl
... | no neq = neq refl
⊑k→BelowConstk (⊑-conj-L v⊑k v⊑k₁) =
   ⟨ ⊑k→BelowConstk v⊑k , ⊑k→BelowConstk v⊑k₁ ⟩
⊑k→BelowConstk (⊑-trans v⊑k v⊑k₁) =
  let ih = ⊑k→BelowConstk v⊑k₁ in
  BelowConst-⊑ ih v⊑k

BelowConstk→⊑k : ∀{B : Base}{k : base-rep B}{v : Value}
   → BelowConst k v
   → v ⊑ const {B} k
BelowConstk→⊑k {v = ⊥} bkv = ⊑-⊥
BelowConstk→⊑k {B}{k}{v = const {B′} k′} bkv
     with base-eq? B B′
... | yes eq rewrite eq | bkv = ⊑-const
... | no neq = ⊥-elim bkv
BelowConstk→⊑k {v = v ↦ v₁} ()
BelowConstk→⊑k {v = v₁ ⊔ v₂} ⟨ fst , snd ⟩ =
  ⊑-conj-L (BelowConstk→⊑k fst) (BelowConstk→⊑k snd)

