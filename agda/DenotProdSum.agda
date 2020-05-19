module DenotProdSum where

open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import ModelISWIM
open import ConsistentAux value_struct ordering consistent
open import Primitives

{------------------------------------------------------------------------------

  An encoding of products and sums using functions, 0s, and 1s.

 -----------------------------------------------------------------------------}

⟬_,_⟭ : Denotation → Denotation → Denotation
⟬_,_⟭ D₁ D₂ γ ⊥ = ⊤
⟬_,_⟭ D₁ D₂ γ (const k) = Bot
⟬_,_⟭ D₁ D₂ γ (v ↦ w) = const 0 ⊑ v × D₁ γ w
                      ⊎ const 1 ⊑ v × D₂ γ w
⟬_,_⟭ D₁ D₂ γ (v₁ ⊔ v₂) = ⟬ D₁ , D₂ ⟭ γ v₁ × ⟬ D₁ , D₂ ⟭ γ v₂

𝟘 : Denotation
𝟘 γ v = const 0 ⊑ v

𝟙 : Denotation
𝟙 γ v = const 1 ⊑ v

π₁ : Denotation → Denotation
π₁ D = D ● 𝟘

π₂ : Denotation → Denotation
π₂ D = D ● 𝟙

inj1 : Denotation → Denotation
inj1 D = ⟬ 𝟘 , D ⟭

inj2 : Denotation → Denotation
inj2 D = ⟬ 𝟙 , D ⟭

case⊎ : Denotation → Denotation → Denotation → Denotation
case⊎ D⊎ D₁ D₂ γ v =
   ((π₁ D⊎) γ (const 0)
    × (Σ[ v₁ ∈ Value ] wf v₁ × ((π₂ D⊎) γ v₁) × D₁ (γ `, v₁) v))
   ⊎ ((π₁ D⊎) γ (const 1)
    × (Σ[ v₂ ∈ Value ] wf v₂ × ((π₂ D⊎) γ v₂) × D₂ (γ `, v₂) v))

π₁-≃ : ∀{D}{E} → π₁ ⟬ D , E ⟭ ≃ D
π₁-≃ {D}{E} γ v wfγ wfv = ⟨ G , H ⟩
  where
  G : π₁ ⟬ D , E ⟭ γ v → D γ v
  G ⟨ w , ⟨ wfw , ⟨ inj₁ ⟨ _ , Dv ⟩ , 0⊑w ⟩ ⟩ ⟩ = Dv
  G ⟨ w , ⟨ wfw , ⟨ inj₂ ⟨ 1⊑w , Ev ⟩ , 0⊑w ⟩ ⟩ ⟩
      with k⊑v→k′⊑v→k′≡k wfw 0⊑w 1⊑w
  ... | ()

  H : D γ v → π₁ ⟬ D , E ⟭ γ v
  H Dv = ⟨ const 0 , ⟨ wf-const , ⟨ inj₁ ⟨ ⊑-const , Dv ⟩ , ⊑-const ⟩ ⟩ ⟩

π₂-≃ : ∀{D}{E} → π₂ ⟬ D , E ⟭ ≃ E
π₂-≃ {D}{E} γ v wfγ wfv = ⟨ G , H ⟩
  where
  G : π₂ ⟬ D , E ⟭ γ v → E γ v
  G ⟨ w , ⟨ wfw , ⟨ inj₁ ⟨ 0⊑w , _ ⟩ , 1⊑w ⟩ ⟩ ⟩
      with k⊑v→k′⊑v→k′≡k wfw 0⊑w 1⊑w
  ... | ()
  G ⟨ w , ⟨ wfw , ⟨ inj₂ ⟨ _ , Ev ⟩ , 1⊑w ⟩ ⟩ ⟩ = Ev

  H : E γ v → π₂ ⟬ D , E ⟭ γ v
  H Ev = ⟨ const 1 , ⟨ wf-const , ⟨ inj₂ ⟨ ⊑-const , Ev ⟩ , ⊑-const ⟩ ⟩ ⟩


℘kv→k⊑v : ∀{B}{k}{v}
   → ℘ {base B} k v
   → const k ⊑ v ⊎ v ⊑ ⊥
℘kv→k⊑v {B} {k} {⊥} ℘kv = inj₂ ⊑-⊥
℘kv→k⊑v {B} {k} {const {b = b} k'} ℘kv
    with base-eq? B b
... | yes refl with ℘kv
... | refl = inj₁ ⊑-refl
℘kv→k⊑v {B} {k} {const {b = b} k'} ℘kv
    | no neq with ℘kv
... | ()
℘kv→k⊑v {B} {k} {v ⊔ w} ⟨ pkv , pkw ⟩
    with ℘kv→k⊑v {B}{k}{v} pkv | ℘kv→k⊑v {B}{k}{w} pkw
... | inj₁ kv | inj₁ kw = inj₁ (⊑-conj-R1 kv)    
... | inj₁ kv | inj₂ w⊥ = inj₁ (⊑-conj-R1 kv)    
... | inj₂ v⊥ | inj₁ kw = inj₁ (⊑-conj-R2 kw)    
... | inj₂ v⊥ | inj₂ w⊥ = inj₂ (⊑-conj-L v⊥ w⊥)    

{-

show a contradiction

have:

  wf v'
  ℘ 0 v'
  ℘ 1 v'

want:
  const 0 ⊑ v'
  const 1 ⊑ v'

PrimConst.agda

   ℘k→BelowConstk : ∀{B : Base}{k : base-rep B}{v : Value}
       → ℘ {base B} k v
       → BelowConst k v

   BelowConstk→⊑k : ∀{B : Base}{k : base-rep B}{v : Value}
      → BelowConst k v
      → v ⊑ const {B} k

   A⊑k→A⊆k⊔⊥ : ∀{A}{B}{k : base-rep B}
             → A ⊑ const k
             → A ⊆ (const k ⊔ ⊥)
   A⊑k→A⊆k⊔⊥ A⊑k = BelowConstk→⊆k⊔⊥ (⊑k→BelowConstk A⊑k)

   k⊔⊥⊆v→k~v : ∀{v : Value}{B : Base}{k : base-rep B}
           → v ⊆ (const k ⊔ ⊥)
           → const k ~ v

   

Consistency.agda

   k⊑v→k′⊑v→k′≡k : ∀{b : Base}{k k′ : base-rep b}{v : Value}
                 → wf v 
                 → const {b} k ⊑ v → const {b} k′ ⊑ v
                 → k ≡ k′



-}
