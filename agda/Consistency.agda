open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero; _+_; _<_; _≤_) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; ≤-step; ⊔-mono-≤;
         +-mono-≤-<; +-mono-<-≤; +-comm; n≤1+n;
         ≤-pred)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)

open import Variables
open import Primitives
open import Structures
open import ValueBCDConst
open import FunInverseBCDConst
open OrderingAux domain ordering
open import BelowBCDConst

module Consistency where

v~⊥ : ∀{v : Value} → v ~ ⊥
v~⊥ {⊥} = tt
v~⊥ {const x} = tt
v~⊥ {v ↦ w} = tt
v~⊥ {v₁ ⊔ v₂} = ⟨ v~⊥ {v₁} , v~⊥ {v₂} ⟩

~⊔R : ∀{v u₁ u₂} → v ~ u₁ → v ~ u₂ 
    → v ~ u₁ ⊔ u₂
~⊔R {⊥} v~u₁ v~u₂ = tt
~⊔R {const k} v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
~⊔R {v ↦ w} v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
~⊔R {v₁ ⊔ v₂} v~u₁ v~u₂ =
    ⟨ (~⊔R {v = v₁} (proj₁ v~u₁) (proj₁ v~u₂)) ,
      (~⊔R {v = v₂} (proj₂ v~u₁) (proj₂ v~u₂)) ⟩



~-sym : ∀{u v} → u ~ v → v ~ u
~-sym {⊥} {⊥} u~v = tt
~-sym {⊥} {const k} u~v = tt
~-sym {⊥} {v ↦ w} u~v = tt
~-sym {⊥} {v₁ ⊔ v₂} u~v = ⟨ ~-sym {v = v₁} tt , ~-sym {v = v₂} tt ⟩
~-sym {const k} {⊥} u~v = tt
~-sym {const {B} k} {const {B′} k′} u~v
    with base-eq? B B′
... | no neq = ⊥-elim u~v
... | yes eq
    rewrite eq
    with base-eq? B′ B′
... | no neq = neq refl
... | yes refl = sym u~v
~-sym {const k} {v ↦ w} ()
~-sym {const k} {u ⊔ v} ⟨ k~u , k~v ⟩ =
  ⟨ (~-sym{v = u} k~u) , (~-sym{v = v} k~v) ⟩
~-sym {v ↦ w} {⊥} u~v = tt
~-sym {v ↦ w} {const k} ()
~-sym {v ↦ w} {v′ ↦ w′} (inj₁ ⟨ fst , snd ⟩) =
   inj₁ ⟨ (~-sym{v = v′} fst) , (~-sym{v = w′} snd) ⟩
~-sym {v ↦ w} {v′ ↦ w′} (inj₂ ¬v~v′) =
   inj₂ λ x → ⊥-elim (contradiction (~-sym{u = v′} x) ¬v~v′)
~-sym {v ↦ w} {u₁ ⊔ u₂} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{v = u₁} fst , ~-sym{v = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {⊥} ⟨ fst , snd ⟩ = tt
~-sym {u₁ ⊔ u₂} {const k} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{u = u₁} fst , ~-sym{u = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {v ↦ v₁} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{u = u₁} fst , ~-sym{u = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {v₁ ⊔ v₂} ⟨ fst , snd ⟩ 
    with ~-sym {u₁} {v₁ ⊔ v₂} fst
       | ~-sym {u₂} {v₁ ⊔ v₂} snd
... | ⟨ v₁~u₁ , v₂~u₁ ⟩ | ⟨ v₁~u₂ , v₂~u₂ ⟩ =
      ⟨ ~⊔R{v = v₁} v₁~u₁ v₁~u₂ , ~⊔R{v = v₂} v₂~u₁ v₂~u₂ ⟩

~-refl : ∀{v} → wf v → v ~ v
~-refl {.⊥} wf-bot = tt
~-refl {const {B} k} wf-const
    with base-eq? B B
... | yes eq rewrite eq = refl
... | no neq = neq refl
~-refl {.(_ ↦ _)} (wf-fun wfv wfv₁) = inj₁ ⟨ ~-refl wfv , ~-refl wfv₁ ⟩
~-refl {v₁ ⊔ v₂} (wf-⊔ v₁~v₂ wfv₁ wfv₂) =
    ⟨ ~⊔R{v₁} (~-refl{v₁} wfv₁) v₁~v₂ ,
      ~⊔R{v₂} (~-sym{v₁} v₁~v₂) (~-refl wfv₂) ⟩


consistent→atoms : ∀ {u v u′ v′} → u ~ v → u′ ∈ u → v′ ∈ v → u′ ~ v′
consistent→atoms {⊥} {v} {u′} {v′} u~v u′∈u v′∈v rewrite u′∈u = tt
consistent→atoms {const {B} k} {⊥} {u′} {v′} u~v u′∈u v′∈v
    rewrite u′∈u | v′∈v = tt
consistent→atoms {const {B} k} {const {B′} k′} {u′} {v′} u~v u′∈u v′∈v
    rewrite u′∈u | v′∈v
    with base-eq? B B′
... | yes refl = u~v
... | no neq = u~v
consistent→atoms {const {B} k} {v ↦ w} {u′} {v′} () u′∈u v′∈v
consistent→atoms {const {B} k} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u
    (inj₁ v′∈v₁) rewrite u′∈u = consistent→atoms{const {B} k} fst refl v′∈v₁
consistent→atoms {const {B} k} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u
    (inj₂ v′∈v₂) rewrite u′∈u =  consistent→atoms{const {B} k} snd refl v′∈v₂
consistent→atoms {u ↦ w} {⊥} {u′} {v′} u~v u′∈u v′∈v rewrite u′∈u | v′∈v = tt
consistent→atoms {u ↦ w} {const x} {u′} {v′} () u′∈u v′∈v
consistent→atoms {u ↦ w} {v₁ ↦ v₂} {u′} {v′} (inj₁ ⟨ fst , snd ⟩) u′∈u v′∈v
    rewrite u′∈u | v′∈v = inj₁ ⟨ fst , snd ⟩
consistent→atoms {u ↦ w} {v₁ ↦ v₂} {u′} {v′} (inj₂ y) u′∈u v′∈v
    rewrite u′∈u | v′∈v = inj₂ y
consistent→atoms {u ↦ w} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u (inj₁ x)
    rewrite u′∈u = consistent→atoms {u ↦ w}{v₁} fst refl x
consistent→atoms {u ↦ w} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u (inj₂ y)
    rewrite u′∈u = consistent→atoms {u ↦ w}{v₂} snd refl y
consistent→atoms {u₁ ⊔ u₂} {v} {u′} {v′} ⟨ u₁~v , u₂~v ⟩ (inj₁ u′∈u₁) v′∈v =
    consistent→atoms u₁~v u′∈u₁ v′∈v
consistent→atoms {u₁ ⊔ u₂} {v} {u′} {v′} ⟨ u₁~v , u₂~v ⟩ (inj₂ u′∈u₂) v′∈v =
    consistent→atoms u₂~v u′∈u₂ v′∈v

atoms→consistent : ∀{u v}
                 → (∀{u′ v′} → u′ ∈ u → v′ ∈ v → u′ ~ v′)
                 → u ~ v
atoms→consistent {⊥} {v} atoms = tt
atoms→consistent {const k} {⊥} atoms = tt
atoms→consistent {const k} {const k′} atoms =
    atoms {const k} {const k′} refl refl
atoms→consistent {const k} {v ↦ w} atoms =
    ⊥-elim (atoms {const k} {v ↦ w} refl refl)
atoms→consistent {const k} {v₁ ⊔ v₂} atoms =
    ⟨ atoms→consistent{const k}{v₁} (λ {u′} {v′} z z₁ → atoms z (inj₁ z₁)) ,
      atoms→consistent{const k}{v₂} (λ {u′} {v′} z z₁ → atoms z (inj₂ z₁)) ⟩
atoms→consistent {u ↦ w} {⊥} atoms = tt
atoms→consistent {u ↦ w} {const k} atoms =
    ⊥-elim (atoms {u ↦ w}{const k} refl refl)
atoms→consistent {u ↦ w} {v₁ ↦ v₂} atoms =
    atoms {u ↦ w} {v₁ ↦ v₂ } refl refl
atoms→consistent {u ↦ w} {v₁ ⊔ v₂} atoms =
    ⟨ atoms→consistent{u ↦ w}{v₁}(λ {u′}{v′} z z₁ → atoms z (inj₁ z₁)) ,
      atoms→consistent{u ↦ w}{v₂} (λ {u′} {v′} z z₁ → atoms z (inj₂ z₁)) ⟩
atoms→consistent {u₁ ⊔ u₂} {v} atoms =
    ⟨ atoms→consistent (λ {u′} {v′} z → atoms (inj₁ z)) ,
      atoms→consistent (λ {u′} {v′} z → atoms (inj₂ z)) ⟩


BelowFun : Value → Set
BelowFun ⊥ = ⊤
BelowFun (const {B} k) = Bot
BelowFun (v ↦ w) = ⊤
BelowFun (u ⊔ v) = BelowFun u × BelowFun v

Below⊥→BelowFun : ∀{v : Value}
   → Below⊥ v
   → BelowFun v
Below⊥→BelowFun {⊥} b⊥v = tt
Below⊥→BelowFun {const {B′} k′} ()
Below⊥→BelowFun {v ↦ w} ()
Below⊥→BelowFun {v₁ ⊔ v₂} ⟨ fst , snd ⟩ =
  ⟨ Below⊥→BelowFun fst , Below⊥→BelowFun snd ⟩


BelowFun-⊑ : ∀{u v} → BelowFun v → u ⊑ v → BelowFun u
BelowFun-⊑ {.⊥} {v} bv ⊑-⊥ = tt
BelowFun-⊑ {.(const _)} {.(const _)} () ⊑-const
BelowFun-⊑ {.(_ ⊔ _)} {v} bv (⊑-conj-L u⊑v u⊑v₁) =
    ⟨ BelowFun-⊑ bv u⊑v , BelowFun-⊑ bv u⊑v₁ ⟩
BelowFun-⊑ {u} {.(_ ⊔ _)} bv (⊑-conj-R1 u⊑v) =
    BelowFun-⊑ (proj₁ bv) u⊑v
BelowFun-⊑ {u} {.(_ ⊔ _)} bv (⊑-conj-R2 u⊑v) =
    BelowFun-⊑ (proj₂ bv) u⊑v
BelowFun-⊑ {u} {v} bv (⊑-trans u⊑v u⊑v₁) =
    BelowFun-⊑ (BelowFun-⊑ bv u⊑v₁) u⊑v
BelowFun-⊑ {.(_ ↦ _)} {.(_ ↦ _)} bv (⊑-fun u⊑v u⊑v₁) = tt
BelowFun-⊑ {.(_ ↦ (_ ⊔ _))} {.(_ ↦ _ ⊔ _ ↦ _)} bv ⊑-dist = tt

⊑↦→BelowFun : ∀{u v w} → u ⊑ v ↦ w → BelowFun u
⊑↦→BelowFun {.⊥} {v} {w} ⊑-⊥ = tt
⊑↦→BelowFun {.(_ ⊔ _)} {v} {w} (⊑-conj-L u⊑v↦w u⊑v↦w₁) =
    ⟨ ⊑↦→BelowFun u⊑v↦w , ⊑↦→BelowFun u⊑v↦w₁ ⟩
⊑↦→BelowFun {u} {v} {w} (⊑-trans u⊑v↦w u⊑v↦w₁) =
  let ih = ⊑↦→BelowFun u⊑v↦w₁ in
  BelowFun-⊑ ih u⊑v↦w
⊑↦→BelowFun {.(_ ↦ _)} {v} {w} (⊑-fun u⊑v↦w u⊑v↦w₁) = tt


AboveConst : Value → Set
AboveConst u = Σ[ B ∈ Base ] Σ[ k ∈ base-rep B ] const {B} k ⊑ u

AboveConst-⊑ : ∀{u v}
   → AboveConst u → u ⊑ v
   → AboveConst v
AboveConst-⊑ ⟨ B , ⟨ k , snd ⟩ ⟩ uv = ⟨ B , ⟨ k , ⊑-trans snd uv ⟩ ⟩

const-sub-inv : ∀{u₁ u₂ : Value}
        → u₁ ⊑ u₂
        → ∀{B}{k : base-rep B} → const {B} k ∈ u₁
          -------------------------------------
        → const {B} k ∈ u₂
const-sub-inv {.⊥} {u₂} ⊑-⊥ ()
const-sub-inv {.(const _)} {.(const _)} ⊑-const f = f
const-sub-inv {.(_ ⊔ _)} {u₂} (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₁ x) =
    const-sub-inv u₁⊑u₂ x
const-sub-inv {.(_ ⊔ _)} {u₂} (⊑-conj-L u₁⊑u₂ u₁⊑u₃) (inj₂ y) =
    const-sub-inv u₁⊑u₃ y
const-sub-inv {u₁} {.(_ ⊔ _)} (⊑-conj-R1 u₁⊑u₂) f = inj₁ (const-sub-inv u₁⊑u₂ f)
const-sub-inv {u₁} {.(_ ⊔ _)} (⊑-conj-R2 u₁⊑u₂) f = inj₂ (const-sub-inv u₁⊑u₂ f)
const-sub-inv {u₁} {u₂} (⊑-trans u₁⊑u₂ u₁⊑u₃) f =
    const-sub-inv u₁⊑u₃ (const-sub-inv u₁⊑u₂ f)
const-sub-inv {.(_ ↦ _)} {.(_ ↦ _)} (⊑-fun u₁⊑u₂ u₁⊑u₃) ()
const-sub-inv {.(_ ↦ (_ ⊔ _))} {.(_ ↦ _ ⊔ _ ↦ _)} ⊑-dist ()

{-
AboveConst⊥ : ¬ AboveConst ⊥
AboveConst⊥ ⟨ v , ⟨ w , lt ⟩ ⟩ = {!!}
-}

⊔⊑R : ∀{B₁ B₂ A}
    → B₁ ⊔ B₂ ⊑ A
    → B₁ ⊑ A
⊔⊑R (⊑-conj-L B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = B₁⊔B₂⊑A
⊔⊑R (⊑-conj-R1 B₁⊔B₂⊑A) = ⊑-conj-R1 (⊔⊑R B₁⊔B₂⊑A)
⊔⊑R (⊑-conj-R2 B₁⊔B₂⊑A) = ⊑-conj-R2 (⊔⊑R B₁⊔B₂⊑A)
⊔⊑R (⊑-trans B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = ⊑-trans (⊔⊑R B₁⊔B₂⊑A) B₁⊔B₂⊑A₁

⊔⊑L : ∀{B₁ B₂ A}
    → B₁ ⊔ B₂ ⊑ A
    → B₂ ⊑ A
⊔⊑L (⊑-conj-L B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = B₁⊔B₂⊑A₁
⊔⊑L (⊑-conj-R1 B₁⊔B₂⊑A) = ⊑-conj-R1 (⊔⊑L B₁⊔B₂⊑A)
⊔⊑L (⊑-conj-R2 B₁⊔B₂⊑A) = ⊑-conj-R2 (⊔⊑L B₁⊔B₂⊑A)
⊔⊑L (⊑-trans B₁⊔B₂⊑A B₁⊔B₂⊑A₁) = ⊑-trans (⊔⊑L B₁⊔B₂⊑A) B₁⊔B₂⊑A₁

{- Atomic Subtyping 1 -}

∈⊑⊑ : ∀{B A C} → C ∈ B → B ⊑ A → C ⊑ A
∈⊑⊑ {⊥} C∈B B⊑A  rewrite C∈B = B⊑A
∈⊑⊑ {const k} C∈B B⊑A rewrite C∈B = B⊑A
∈⊑⊑ {B₁ ↦ B₂} C∈B B⊑A rewrite C∈B = B⊑A
∈⊑⊑ {B₁ ⊔ B₂}{A}{C} (inj₁ C∈B₁) B⊑A = ∈⊑⊑ {B₁}{A}{C} C∈B₁ (⊔⊑R B⊑A)
∈⊑⊑ {B₁ ⊔ B₂}{A}{C} (inj₂ C∈B₂) B⊑A = ∈⊑⊑ {B₂}{A}{C} C∈B₂ (⊔⊑L B⊑A)

{- Atomic Subtyping 2 -}

k⊑A→k∈A : ∀{B}{k : base-rep B}{A : Value}
        → const k ⊑ A
        → const k ∈ A
k⊑A→k∈A {B} {k} {A} k⊑A = const-sub-inv k⊑A refl

{- Atomic Subtyping 3 -}

BelowConstk→⊆k⊔⊥ : ∀{A}{B}{k : base-rep B}
          → BelowConst k A
          → A ⊆ (const k ⊔ ⊥)
BelowConstk→⊆k⊔⊥ {⊥} {B} {k} bkA u≡⊥ = inj₂ u≡⊥
BelowConstk→⊆k⊔⊥ {const {b} k′} {B} {k} bkA u≡k′
    with base-eq? B b
... | yes eq rewrite eq | bkA = inj₁ u≡k′
... | no neq = ⊥-elim bkA
BelowConstk→⊆k⊔⊥ {A₁ ↦ A₂} {B} {k} () u≡A₁→A₂
BelowConstk→⊆k⊔⊥ {A₁ ⊔ A₂} {B} {k} ⟨ fst , snd ⟩ (inj₁ x) =
    BelowConstk→⊆k⊔⊥ fst x
BelowConstk→⊆k⊔⊥ {A₁ ⊔ A₂} {B} {k} ⟨ fst , snd ⟩ (inj₂ y) =
    BelowConstk→⊆k⊔⊥ snd y

A⊑k→A⊆k⊔⊥ : ∀{A}{B}{k : base-rep B}
          → A ⊑ const k
          → A ⊆ (const k ⊔ ⊥)
A⊑k→A⊆k⊔⊥ A⊑k = BelowConstk→⊆k⊔⊥ (⊑k→BelowConstk A⊑k)

⊆k⊔⊥→BelowConstk : ∀{A}{B}{k : base-rep B}
          → A ⊆ (const k ⊔ ⊥)
          → BelowConst k A
⊆k⊔⊥→BelowConstk {⊥} {B} {k} A⊆k⊔⊥ = tt
⊆k⊔⊥→BelowConstk {const {b} k′} {B} {k} A⊆k⊔⊥
    with base-eq? B b
... | no neq
    with A⊆k⊔⊥ {const k′} refl
... | inj₁ refl = neq refl
... | inj₂ ()
⊆k⊔⊥→BelowConstk {const {b} k′} {B} {k} A⊆k⊔⊥ | yes eq rewrite eq
    with A⊆k⊔⊥ {const k′} refl
... | inj₁ refl = refl
... | inj₂ ()
⊆k⊔⊥→BelowConstk {A₁ ↦ A₂} {B} {k} A⊆k⊔⊥
    with A⊆k⊔⊥ {A₁ ↦ A₂} refl
... | inj₁ ()
... | inj₂ ()
⊆k⊔⊥→BelowConstk {A₁ ⊔ A₂} {B} {k} A⊆k⊔⊥ =
    ⟨ ⊆k⊔⊥→BelowConstk (λ {u} z → A⊆k⊔⊥ (inj₁ z)) ,
      ⊆k⊔⊥→BelowConstk (λ {u} z → A⊆k⊔⊥ (inj₂ z)) ⟩

A⊆k⊔⊥→A⊑k : ∀{A}{B}{k : base-rep B}
          → A ⊆ (const k ⊔ ⊥)
          → A ⊑ const k
A⊆k⊔⊥→A⊑k A⊆k⊔⊥ = BelowConstk→⊑k (⊆k⊔⊥→BelowConstk A⊆k⊔⊥)

{- Atomic Subtyping 4 -}

atom-exists : ∀{v} → Σ[ u ∈ Value ] u ∈ v
atom-exists {⊥} = ⟨ ⊥ , refl ⟩
atom-exists {const k} = ⟨ const k , refl ⟩
atom-exists {v ↦ w} = ⟨ v ↦ w , refl ⟩
atom-exists {v₁ ⊔ v₂}
    with atom-exists {v₁}
... | ⟨ u , u∈v₁ ⟩ =   
      ⟨ u , (inj₁ u∈v₁) ⟩

atomic-sub-4 : ∀{A B C}
    → A ↦ B ⊑ C
    → Σ[ D ∈ Value ] Σ[ E ∈ Value ] D ↦ E ∈ C
atomic-sub-4 {A}{B}{C} A↦B⊑C
    with sub-inv-fun A↦B⊑C
... | ⟨ u , ⟨ fu , ⟨ uC , _ ⟩ ⟩ ⟩
    with atom-exists {u}
... | ⟨ u′ , u′∈u ⟩
    with fu u′∈u
... | fun {u′}{u₁}{u₂} eq rewrite eq =
      ⟨ u₁ , ⟨ u₂ , (uC u′∈u) ⟩ ⟩

{- Atomic Subtyping 5 (d_fun_atoms_L_inv) -}

∈-Below⊥ : ∀{v u} → u ∈ v → Below⊥ v → u ≡ ⊥
∈-Below⊥ {⊥} {u} u∈v bv = u∈v
∈-Below⊥ {const x} {u} u∈v ()
∈-Below⊥ {v ↦ v₁} {u} u∈v ()
∈-Below⊥ {v ⊔ v₁} {u} (inj₁ x) bv = ∈-Below⊥ x (proj₁ bv)
∈-Below⊥ {v ⊔ v₁} {u} (inj₂ y) bv = ∈-Below⊥ y (proj₂ bv)

atomic-sub-5 : ∀{u v} → v ⊑ u → Funs⊥ u → Funs⊥ v
atomic-sub-5 {u} {⊥} v⊑u Funs⊥u {u′} u′≡⊥ = bot u′≡⊥
atomic-sub-5 {u} {const k} v⊑u Funs⊥u {u′} u′≡k
    rewrite u′≡k 
    with Funs⊥u (k⊑A→k∈A v⊑u)
... | fun ()
... | bot ()
atomic-sub-5 {u} {v₁ ↦ v₂} v⊑u Funs⊥u u≡ = fun u≡
atomic-sub-5 {u} {v₁ ⊔ v₂} v⊑u Funs⊥u {u′} (inj₁ x) =
    atomic-sub-5 {u} {v₁} (⊔⊑R v⊑u) Funs⊥u x
atomic-sub-5 {u} {v₁ ⊔ v₂} v⊑u Funs⊥u {u′} (inj₂ y) =
    atomic-sub-5 {u} {v₂} (⊔⊑L v⊑u) Funs⊥u y

k~v→k⊔⊥⊆v : ∀{v : Value}{B : Base}{k : base-rep B}
        → const k ~ v
        → v ⊆ (const k ⊔ ⊥)
k~v→k⊔⊥⊆v {⊥} {B} {k} k~v {u} u≡⊥ = inj₂ u≡⊥
k~v→k⊔⊥⊆v {const {B′} k′} {B} {k} k~v {u} u≡k′
    with base-eq? B B′
... | yes eq rewrite eq | k~v = inj₁ u≡k′
... | no neq = ⊥-elim k~v
k~v→k⊔⊥⊆v {v ↦ w} {B} {k} () {u} u≡v↦w
k~v→k⊔⊥⊆v {v ⊔ v₁} {B} {k} k~v {u} (inj₁ x) = k~v→k⊔⊥⊆v (proj₁ k~v) x
k~v→k⊔⊥⊆v {v ⊔ v₁} {B} {k} k~v {u} (inj₂ y) = k~v→k⊔⊥⊆v (proj₂ k~v) y

k⊔⊥⊆v→k~v : ∀{v : Value}{B : Base}{k : base-rep B}
        → v ⊆ (const k ⊔ ⊥)
        → const k ~ v
k⊔⊥⊆v→k~v {⊥} {B} {k} v⊆k⊔⊥ = tt
k⊔⊥⊆v→k~v {const {B′} k′} {B} {k} v⊆k⊔⊥
    with base-eq? B B′
... | no neq
    with v⊆k⊔⊥ {const k′} refl
... | inj₂ ()
... | inj₁ refl = ⊥-elim (neq refl)
k⊔⊥⊆v→k~v {const {B′} k′} {B} {k} v⊆k⊔⊥ | yes eq
    rewrite eq
    with v⊆k⊔⊥ {const k′} refl
... | inj₁ refl = refl
... | inj₂ ()
k⊔⊥⊆v→k~v {v ↦ w} {B} {k} v⊆k⊔⊥
    with v⊆k⊔⊥ {v ↦ w} refl
... | inj₁ ()
... | inj₂ ()
k⊔⊥⊆v→k~v {v₁ ⊔ v₂} {B} {k} v⊆k⊔⊥ =
    ⟨ k⊔⊥⊆v→k~v (λ {u} z → v⊆k⊔⊥ (inj₁ z)) ,
      k⊔⊥⊆v→k~v (λ {u} z → v⊆k⊔⊥ (inj₂ z)) ⟩

∈-refl : ∀ {u v} → u ∈ v → u ∈ u
∈-refl {⊥} {v} u∈v = refl
∈-refl {const x} {v} u∈v = refl
∈-refl {u ↦ u₁} {v} u∈v = refl
∈-refl {u ⊔ u₁} {v} u∈v = ⊥-elim (not-u₁⊔u₂∈v u∈v)

v↦w~u→Funs⊥u : ∀{v w u} → v ↦ w ~ u → Funs⊥ u
v↦w~u→Funs⊥u {v} {w} {⊥} v↦w~u u≡⊥ = bot u≡⊥
v↦w~u→Funs⊥u {v} {w} {const k} ()
v↦w~u→Funs⊥u {v} {w} {u₁ ↦ u₂} v↦w~u u≡ = fun u≡
v↦w~u→Funs⊥u {v} {w} {u₁ ⊔ u₂} ⟨ fst , snd ⟩ {u} = G
  where
  ih1 : Funs⊥ u₁
  ih1 = v↦w~u→Funs⊥u {v}{w}{u₁} fst 
  ih2 : Funs⊥ u₂
  ih2 = v↦w~u→Funs⊥u {v}{w}{u₂} snd 
  G : u ∈ u₁ ⊎ u ∈ u₂ → Fun⊥ u
  G (inj₁ u∈u₁) = ih1 u∈u₁
  G (inj₂ u∈u₂) = ih2 u∈u₂

Funs⊥u→u∈v→Fun⊥u : ∀{u v} → Funs⊥ u → u ∈ v → Fun⊥ u
Funs⊥u→u∈v→Fun⊥u {⊥} {v} fu u∈v = fu refl
Funs⊥u→u∈v→Fun⊥u {const k} {v} fu u∈v = fu refl
Funs⊥u→u∈v→Fun⊥u {u₁ ↦ u₂} {v} fu u∈v = fu refl
Funs⊥u→u∈v→Fun⊥u {u ⊔ u₁} {v} fu u∈v = ⊥-elim (not-u₁⊔u₂∈v u∈v)

funs-B : ∀{A B} → A ~ B → ∀{A₁ A₂} → A₁ ↦ A₂ ∈ A → Funs⊥ B
funs-B {A}{B} A~B {A₁}{A₂} A₁↦A₂∈A {B′} B′∈B =
   (let A₁↦A₂~B′ = consistent→atoms{A}{B}{v′ = B′}
                               A~B A₁↦A₂∈A B′∈B in
   let funs-B′ = v↦w~u→Funs⊥u{A₁}{A₂}{B′} A₁↦A₂~B′ in
   Funs⊥u→u∈v→Fun⊥u funs-B′ B′∈B) 


∈cod : ∀{Γ A}
     → A ∈ cod Γ
     → (Σ[ A₁ ∈ Value ] Σ[ A₂ ∈ Value ] A₁ ↦ A₂ ∈ Γ × A ∈ A₂) ⊎ (A ≡ ⊥)
∈cod {⊥} {A} A∈codΓ rewrite A∈codΓ = inj₂ refl
∈cod {const k} {A} A∈codΓ rewrite A∈codΓ = inj₂ refl
∈cod {Γ₁ ↦ Γ₂} {A} A∈codΓ = inj₁ ⟨ Γ₁ , ⟨ Γ₂ , ⟨ refl , A∈codΓ ⟩ ⟩ ⟩
∈cod {Γ₁ ⊔ Γ₂} {A} (inj₁ x) 
   with ∈cod {Γ₁} {A} x
... | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ A₁↦A₂∈Γ₁ , A∈A₂ ⟩ ⟩ ⟩ =
      inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ inj₁ A₁↦A₂∈Γ₁ , A∈A₂ ⟩ ⟩ ⟩
... | inj₂ A≡⊥ = inj₂ A≡⊥
∈cod {Γ₁ ⊔ Γ₂} {A} (inj₂ y)
   with ∈cod {Γ₂} {A} y
... | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ A₁↦A₂∈Γ₂ , A∈A₂ ⟩ ⟩ ⟩ =
      inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ inj₂ A₁↦A₂∈Γ₂ , A∈A₂ ⟩ ⟩ ⟩
... | inj₂ A≡⊥ = inj₂ A≡⊥


depth : (v : Value) → ℕ
depth ⊥ = zero
depth (const k) = zero
depth (v ↦ w) = suc (max (depth v) (depth w))
depth (v₁ ⊔ v₂) = max (depth v₁) (depth v₂)

measure : (n : ℕ) → (A : Value) → (C : Value) → Set
measure n A C = depth A + depth C < n

not-measure-zero : ∀{A C} → ¬ measure zero A C
not-measure-zero {A}{C} mz
    with n≤0⇒n≡0 mz
... | ()


{- I can't find this in the old Agda std lib !! -}
max-lub : ∀{x y z : ℕ} → x ≤ z → y ≤ z → max x y ≤ z
max-lub {.0} {y} {z} _≤_.z≤n y≤z = y≤z
max-lub {suc x} {.0} {suc z} (_≤_.s≤s x≤z) _≤_.z≤n = _≤_.s≤s x≤z
max-lub {suc x} {suc y} {suc z} (_≤_.s≤s x≤z) (_≤_.s≤s y≤z) =
  let max-xy≤z = max-lub {x}{y}{z} x≤z y≤z in
  _≤_.s≤s max-xy≤z


∈→depth≤ : ∀{v u : Value} → u ∈ v → depth u ≤ depth v
∈→depth≤ {⊥} {u} u∈v rewrite u∈v = _≤_.z≤n
∈→depth≤ {const x} {u} u∈v rewrite u∈v = _≤_.z≤n
∈→depth≤ {v ↦ w} {u} u∈v rewrite u∈v = ≤-refl
∈→depth≤ {v₁ ⊔ v₂} {u} (inj₁ x) =
    ≤-trans (∈→depth≤ {v₁} {u} x) (m≤m⊔n (depth v₁) (depth v₂))
∈→depth≤ {v₁ ⊔ v₂} {u} (inj₂ y) =
    ≤-trans (∈→depth≤ {v₂} {u} y) (n≤m⊔n (depth v₁) (depth v₂))


⊆→depth≤ : ∀{u v : Value} → u ⊆ v → depth u ≤ depth v
⊆→depth≤ {⊥} {v} u⊆v = _≤_.z≤n
⊆→depth≤ {const x} {v} u⊆v = _≤_.z≤n
⊆→depth≤ {u₁ ↦ u₂} {v} u⊆v = ∈→depth≤ (u⊆v refl)
⊆→depth≤ {u₁ ⊔ u₂} {v} u⊆v
    with ⊔⊆-inv u⊆v
... | ⟨ u₁⊆v , u₂⊆v ⟩ =
    let u₁≤v = ⊆→depth≤ u₁⊆v in
    let u₂≤v = ⊆→depth≤ u₂⊆v in
    max-lub u₁≤v u₂≤v

dom-depth-≤ : ∀{u : Value} → depth (dom u) ≤ depth u
dom-depth-≤ {⊥} = _≤_.z≤n
dom-depth-≤ {const k} = _≤_.z≤n
dom-depth-≤ {v ↦ w} = ≤-step (m≤m⊔n (depth v) (depth w))
dom-depth-≤ {u ⊔ v} =
  let ih1 = dom-depth-≤ {u} in
  let ih2 = dom-depth-≤ {v} in
  ⊔-mono-≤ ih1 ih2

cod-depth-≤ : ∀{u : Value} → depth (cod u) ≤ depth u
cod-depth-≤ {⊥} = _≤_.z≤n
cod-depth-≤ {const k} = _≤_.z≤n
cod-depth-≤ {v ↦ w} = ≤-step (n≤m⊔n (depth v) (depth w))
cod-depth-≤ {u ⊔ v} =
  let ih1 = cod-depth-≤ {u} in
  let ih2 = cod-depth-≤ {v} in
  ⊔-mono-≤ ih1 ih2

consistent-⊑-aux : ∀{A B C D} {n : ℕ} {m : measure n A C }
    → A ~ B  →  C ⊑ A  → D ⊑ B
    → C ~ D
consistent-⊑-aux {A}{B}{C}{D} {zero} {m} A~B C⊑A D⊑B =
    ⊥-elim (not-measure-zero {A}{C} m)
consistent-⊑-aux {A}{B}{C}{D} {suc n} {m} A~B C⊑A D⊑B =
    atoms→consistent {C}{D} G
    where
    
    G : ∀ {C′ D′} → C′ ∈ C → D′ ∈ D → C′ ~ D′
    G {⊥} {D′} C′∈C D′∈D = tt
    G {const {b} k} {D′} C′∈C D′∈D =
       k⊔⊥⊆v→k~v D′⊆k⊔⊥
       where
       k∈A : const k ∈ A
       k∈A = k⊑A→k∈A (⊑-trans (∈→⊑ C′∈C) C⊑A)
       B⊆k⊔⊥ : B ⊆ (const k ⊔ ⊥)
       B⊆k⊔⊥ {B′} B′∈B = 
         let k~B′ = consistent→atoms A~B k∈A B′∈B in
         k~v→k⊔⊥⊆v{B′} k~B′ {B′} (∈-refl B′∈B)
       D′⊑B : D′ ⊑ B
       D′⊑B = ⊑-trans (∈→⊑ D′∈D) D⊑B
       D′⊆k⊔⊥ : D′ ⊆ (const k ⊔ ⊥)
       D′⊆k⊔⊥ = A⊑k→A⊆k⊔⊥ (⊑-trans D′⊑B (A⊆k⊔⊥→A⊑k B⊆k⊔⊥) )
    G {C₁ ↦ C₂} {D′} C₁↦C₂∈C D′∈D
        with sub-inv (⊑-trans (∈→⊑ C₁↦C₂∈C) C⊑A) refl
    ... | ⟨ Γ₁ , ⟨ funs-Γ₁ , ⟨ Γ₁⊆A , ⟨ domΓ₁⊑C₁ , C₂⊑codΓ₁ ⟩ ⟩ ⟩ ⟩
        with atomic-sub-4 (∈⊑⊑ C₁↦C₂∈C C⊑A)
    ... | ⟨ A₁ , ⟨ A₂ , A₁↦A₂∈A ⟩ ⟩
        with (atomic-sub-5 D⊑B (funs-B A~B A₁↦A₂∈A)) D′∈D
    ... | bot eq rewrite eq = tt
    ... | fun {D}{D₁}{D₂} eq
        rewrite eq 
        with sub-inv (∈⊑⊑ D′∈D D⊑B) refl
    ... | ⟨ Γ₂ , ⟨ funs-Γ₂ , ⟨ Γ₂⊆B , ⟨ domΓ₂⊑D₁ , D₂⊑codΓ₂ ⟩ ⟩ ⟩ ⟩
        with consistent? C₁ D₁
    ... | no C₁~̸D₁ = inj₂ λ C₁~D₁ → contradiction C₁~D₁ C₁~̸D₁
    ... | yes C₁~D₁ =  inj₁ ⟨ C₁~D₁ , C₂~D₂ ⟩
        where
        m1 : measure n C₁ (dom Γ₁)
        m1 rewrite +-comm (depth C₁) (depth (dom Γ₁)) =
          let C₁<C = ≤-trans (_≤_.s≤s (m≤m⊔n (depth C₁) (depth C₂)))
                             (∈→depth≤ C₁↦C₂∈C) in
          let domΓ₁≤A = ≤-trans (dom-depth-≤ {Γ₁}) (⊆→depth≤ Γ₁⊆A) in
          let A+C≤n = ≤-pred m in
          let domΓ₁+C₁<A+C = +-mono-≤-< domΓ₁≤A C₁<C in
          let domΓ₁+C₁<n = ≤-trans domΓ₁+C₁<A+C  A+C≤n in
          domΓ₁+C₁<n

        domΓ₁~domΓ₂ : dom Γ₁ ~ dom Γ₂
        domΓ₁~domΓ₂ = consistent-⊑-aux{n = n}{m1} C₁~D₁ domΓ₁⊑C₁ domΓ₂⊑D₁

        H : ∀{A′ B′} → A′ ∈ cod Γ₁ → B′ ∈ cod Γ₂ → A′ ~ B′
        H {A′} {B′} A′∈codΓ₁ B′∈codΓ₂
            with ∈cod {Γ₁} A′∈codΓ₁ | ∈cod {Γ₂} B′∈codΓ₂
        ... | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ A₁↦A₂∈Γ₁ , A′∈A₂ ⟩ ⟩ ⟩ | inj₂ B′≡⊥
            rewrite B′≡⊥ =
              v~⊥ {A′}
        H {A′} {B′} A′∈codΓ₁ B′∈codΓ₂ | inj₂ A′≡⊥ | _ rewrite A′≡⊥ =
              tt
        H {A′} {B′} A′∈codΓ₁ B′∈codΓ₂
            | inj₁ ⟨ A₁ , ⟨ A₂ , ⟨ A₁↦A₂∈Γ₁ , A′∈A₂ ⟩ ⟩ ⟩ 
            | inj₁ ⟨ B₁ , ⟨ B₂ , ⟨ B₁↦B₂∈Γ₂ , B′∈B₂ ⟩ ⟩ ⟩
            with consistent→atoms{A}{B}{A₁ ↦ A₂}{B₁ ↦ B₂}
                                   A~B (Γ₁⊆A A₁↦A₂∈Γ₁) (Γ₂⊆B B₁↦B₂∈Γ₂)
        ... | inj₁ ⟨ A₁~B₁ , A₂~B₂ ⟩ =
              consistent→atoms{A₂}{B₂}{A′}{B′} A₂~B₂ A′∈A₂ B′∈B₂
        ... | inj₂ A₁~̸B₁ =
              let A₁⊆domΓ₁ = ↦∈→⊆dom A₁↦A₂∈Γ₁ in
              let B₁⊆domΓ₂ = ↦∈→⊆dom B₁↦B₂∈Γ₂ in
              let A₁~B₁ = atoms→consistent{A₁}{B₁}
                          (λ {A₁′} {B₁′} A₁′∈A₁ B₁′∈B₁ →
                           let A₁′∈domΓ₁ = A₁⊆domΓ₁ A₁′∈A₁ in
                           let B₁′∈domΓ₂ = B₁⊆domΓ₂ B₁′∈B₁ in
                           consistent→atoms domΓ₁~domΓ₂ A₁′∈domΓ₁ B₁′∈domΓ₂) in
              ⊥-elim (contradiction A₁~B₁ A₁~̸B₁)

        codΓ₁~codΓ₂ : cod Γ₁ ~ cod Γ₂
        codΓ₁~codΓ₂ = atoms→consistent H

        m2 : measure n (cod Γ₁) C₂
        m2 =
          let C₂<C = ≤-trans (_≤_.s≤s (n≤m⊔n (depth C₁) (depth C₂)))
                             (∈→depth≤ C₁↦C₂∈C) in
          let codΓ₁≤A = ≤-trans (cod-depth-≤ {Γ₁}) (⊆→depth≤ Γ₁⊆A) in
          let A+C≤n = ≤-pred m in
          let codΓ₁+C₂<A+C = +-mono-≤-< codΓ₁≤A C₂<C in
          let codΓ₁+C₂<n = ≤-trans codΓ₁+C₂<A+C A+C≤n in
          codΓ₁+C₂<n

        C₂~D₂ : C₂ ~ D₂
        C₂~D₂ = consistent-⊑-aux{n = n}{m2} codΓ₁~codΓ₂ C₂⊑codΓ₁ D₂⊑codΓ₂
        
    G {C₁ ⊔ C₂} {D′} C′∈C D′∈D = ⊥-elim (not-u₁⊔u₂∈v C′∈C)

consistent-⊑ : ∀{A B C D}
    → A ~ B  →  C ⊑ A  → D ⊑ B
    → C ~ D
consistent-⊑ {A}{B}{C}{D} =
    consistent-⊑-aux {A}{B}{C}{D} {suc (depth A + depth C)} {_≤_.s≤s ≤-refl}


consistent : Consistent domain ordering
consistent = record {
    wf = wf ;
    _~_ = _~_ ;
    ~-refl = ~-refl ;
    ~-⊑ = consistent-⊑ ;
    ~-↦ = λ {v} {w} {v′} {w′} z → z ;
    wf-fun = wf-fun ;
    wf-⊔ = wf-⊔
    }

open ConsistentAux domain ordering consistent

app-join : ∀{u₁ u₂ v₁ w₁ v₂ w₂}
  → v₁ ↦ w₁ ⊑ u₁
  → v₂ ↦ w₂ ⊑ u₂
  → (v₁ ⊔ v₂) ↦ (w₁ ⊔ w₂) ⊑ (u₁ ⊔ u₂)
app-join {u₁} {u₂} {v₁} {w₁} {v₂} {w₂} v₁↦w₁⊑u₁ v₂↦w₂⊑u₂ =
  let xx : (v₁ ⊔ v₂) ↦ (w₁ ⊔ w₂) ⊑ (v₁ ↦ w₁) ⊔ (v₂ ↦ w₂)
      xx = Dist⊔↦⊔ in
  let yy : (v₁ ↦ w₁) ⊔ (v₂ ↦ w₂) ⊑ u₁ ⊔ u₂
      yy = ⊑-conj-L (⊑-conj-R1 v₁↦w₁⊑u₁) (⊑-conj-R2 v₂↦w₂⊑u₂) in
  ⊑-trans xx yy



{------------------------------
  Consistent Domain

Value′ : Set
Value′ = Σ[ V ∈ Value ] wf V

⊥′ : Value′
⊥′ = ⟨ ⊥ , wf-bot ⟩

_↦′_ : Value′ → Value′ → Value′
⟨ v , wfv ⟩ ↦′ ⟨ w , wfw ⟩ = ⟨ (v ↦ w) , (wf-fun wfv wfw) ⟩

_⊔′_ : Value′ → Value′ → Value′
⟨ u , wfu ⟩ ⊔′ ⟨ v , wfv ⟩
    with consistent? u v
... | yes u~v = ⟨ u ⊔ v , wf-⊔ u~v wfu wfv ⟩
... | no u~̸v = ⟨ ⊥ , wf-bot ⟩   {- ????? -}

domain′ : Domain
domain′ =
  record { Value = Value′ ;
           ⊥ = ⊥′ ;
           _↦_ = _↦′_ ;
          _⊔_ = _⊔′_ }

_⊑′_ : Value′ → Value′ → Set
⟨ u , wfu ⟩ ⊑′ ⟨ v , wfv ⟩ = u ⊑ v

⊑′-⊥ : ∀ {v} → ⊥′ ⊑′ v
⊑′-⊥ {⟨ v , wfv ⟩} = ⊑-⊥

⊑′-conj-L : ∀ {u v w} → v ⊑′ u → w ⊑′ u → (v ⊔′ w) ⊑′ u
⊑′-conj-L {⟨ u , wfu ⟩}{⟨ v , wfv ⟩}{⟨ w , wfw ⟩} vu wu
    with consistent? v w
... | yes v~w = ⊑-conj-L vu wu
... | no v~̸w = ⊑-⊥  

⊑′-conj-R1 : ∀ {u v w} → u ⊑′ v → u ⊑′ (v ⊔′ w)
⊑′-conj-R1 {⟨ u , wfu ⟩}{⟨ v , wfv ⟩}{⟨ w , wfw ⟩} uv
    with consistent? v w
... | yes v~w = ⊑-conj-R1 uv
... | no v~̸w = {!!}               {- Nope, this won't work! -}

 -------------------------------}
