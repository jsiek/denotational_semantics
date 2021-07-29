module GraphModel where

import Level
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic renaming (⊤ to ptop ; tt to ptt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import ScopedTuple hiding (𝒫)
open import ModelISWIM
open import Sig
open import Utilities using (extensionality)

𝒫 : Set → Set₁
𝒫 V = V → Set

↓ : Value → 𝒫 Value
↓ v w = w ⊑ v

{- Function Abstraction -}

𝐺 : (𝒫 Value → 𝒫 Value) → 𝒫 Value
𝐺 f ⊥ = ⊤
𝐺 f (const k) = Bot
𝐺 f (v ↦ w) = f (↓ v) w
𝐺 f (u ⊔ v) = 𝐺 f u × 𝐺 f v

{- Function Application -}

𝐹 : 𝒫 Value → 𝒫 Value → 𝒫 Value
𝐹 d₁ d₂ w = Σ[ v ∈ Value ] wf v × d₁ (v ↦ w) × d₂ v 

infixl 7 _▪_
_▪_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
d₁ ▪ d₂ = 𝐹 d₁ d₂

{- Iterated Function Abstraction -}

𝐺-iter : ∀ n → ArgTy (𝒫 Value) (ℕ→sig n) → 𝒫 Value
𝐺-iter zero f = f
𝐺-iter (suc n) f = 𝐺 (λ D → 𝐺-iter n (f D))

𝐺-iter0≡id : ∀{x : 𝒫 Value}
  → 𝐺-iter 0 x ≡ x
𝐺-iter0≡id {x} = refl  

𝐺-iter1≡𝐺 : ∀{f : 𝒫 Value → 𝒫 Value}
  → 𝐺-iter 1 f ≡ 𝐺 f
𝐺-iter1≡𝐺 {f} = refl  

{-
𝐺-iter zero f = f
𝐺-iter (suc n) f ⊥ = Bot
𝐺-iter (suc n) f (const c) = Bot
𝐺-iter (suc n) f (v ↦ w) = 𝐺-iter n (f (↓ v)) w
𝐺-iter (suc n) f (u ⊔ v) =
  𝐺-iter (suc n) f u  ×  𝐺-iter (suc n) f v
-}

{- Denotations of natural numbers -}

𝟘 : 𝒫 Value
𝟘 v = const 0 ⊑ v

𝟙 : 𝒫 Value
𝟙 v = const 1 ⊑ v

ℕ⟦_⟧ : ℕ → 𝒫 Value
ℕ⟦ n ⟧ v = {- const n ⊑ v × v ⊑ const n -} v ≡ const n {- temporary -}

{- Iterated Function Application -}

𝐹-iter : ∀ (n : ℕ) → 𝒫 Value → 𝒫 Value → 𝒫 Value
𝐹-iter zero df das  = df
𝐹-iter (suc n) df das = 𝐹 (𝐹-iter n df das) (𝐹 das ℕ⟦ n ⟧)

{------------------------------------------------------------------------------
  An encoding of products and sums using functions
 -----------------------------------------------------------------------------}

{-
⟬_,_⟭ : 𝒫 Value → 𝒫 Value → 𝒫 Value
⟬_,_⟭ D₁ D₂ ⊥ = ⊤
⟬_,_⟭ D₁ D₂ (const k) = Bot
⟬_,_⟭ D₁ D₂ (v ↦ w) =   (const 0 ⊑ v × D₁ w)
                      ⊎ (const 1 ⊑ v × D₂ w)
⟬_,_⟭ D₁ D₂ (v₁ ⊔ v₂) = ⟬ D₁ , D₂ ⟭ v₁ × ⟬ D₁ , D₂ ⟭ v₂
-}

π₁ : 𝒫 Value → 𝒫 Value
π₁ D = 𝐹 D 𝟘

π₂ : 𝒫 Value → 𝒫 Value
π₂ D = 𝐹 D 𝟙

Prod : {ℓ : Level} → ℕ → Set ℓ → Set ℓ
Prod 0 A = ptop
Prod (suc n) A = A × Prod n A

{-
⟬_⟭ : ∀{n : ℕ} → Prod n (𝒫 Value) → 𝒫 Value
⟬_⟭ {n = zero} ptop u = ⊤
⟬_⟭ {n = suc n} ⟨ d , ds ⟩ u = (∀ w → d w → (const n) ↦ w ⊑ u) × ⟬ ds ⟭ u

tuple≡prod : ∀ n → Tuple (replicate n ■) (ArgTy (𝒫 Value)) ≡ Prod n (𝒫 Value)
tuple≡prod zero = refl
tuple≡prod (suc n) rewrite tuple≡prod n = refl

-}

𝒫empty : 𝒫 Value
𝒫empty u = ⊤

𝒫set : ∀ (i : ℕ) → 𝒫 Value → 𝒫 Value → 𝒫 Value
𝒫set i d ds u = (Σ[ w ∈ Value ] d w × (const i) ↦ w ∈ u) × ds u

make-tuple : ∀ (i : ℕ) n → Tuple (replicate n ■) (ArgTy (𝒫 Value)) → 𝒫 Value
make-tuple i zero ptop = 𝒫empty
make-tuple i (suc n) ⟨ d , ds ⟩ = 𝒫set i d (make-tuple (suc i) n ds)

⟬_⟭ : ∀{n : ℕ} → Tuple (replicate n ■) (ArgTy (𝒫 Value)) → 𝒫 Value
⟬_⟭ {n} tup = make-tuple 0 n tup

ℕth : 𝒫 Value → ℕ → 𝒫 Value
ℕth D i = D ▪ ℕ⟦ i ⟧

{-
test : ℕth (⟬_⟭ {1} ⟨ ℕ⟦ 42 ⟧ , Level.lift tt ⟩) 0 (const 42)
test = ⟨ (const 0) ,
       ⟨ wf-const , ⟨ ⟨ (λ w x → ⊑-fun′ ⊑-const {!!}) , tt ⟩ ,
       refl ⟩ ⟩ ⟩
-}

{-
  Denotational Equality and Inequality
 -}

infix 6 _≲_
_≲_ : 𝒫 Value → 𝒫 Value → Set
D₁ ≲ D₂ = ∀ (v : Value) → wf v → D₁ v → D₂ v

≲-refl : {D : 𝒫 Value} → D ≲ D
≲-refl {D} v wfv Dv = Dv

≲-trans : {D₁ D₂ D₃ : 𝒫 Value} → D₁ ≲ D₂ → D₂ ≲ D₃ → D₁ ≲ D₃
≲-trans D12 D23 v wfv D₁v = D23 v wfv (D12 v wfv D₁v)

infix 6 _≃_
data _≃_ : 𝒫 Value → 𝒫 Value → Set₁ where
  equal : ∀{D₁ D₂} → D₁ ≲ D₂  →  D₂ ≲ D₁  → D₁ ≃ D₂

to : ∀{D₁ D₂} → D₁ ≃ D₂ → D₁ ≲ D₂
to (equal a b) = a

from : ∀{D₁ D₂} → D₁ ≃ D₂ → D₂ ≲ D₁
from (equal a b) = b

≃-refl : {D : 𝒫 Value} → D ≃ D
≃-refl {D} = equal ≲-refl ≲-refl

≃-sym : {D₁ D₂ : 𝒫 Value} → D₁ ≃ D₂ → D₂ ≃ D₁
≃-sym (equal t f) = equal f t

≃-trans : {D₁ D₂ D₃ : 𝒫 Value} → D₁ ≃ D₂ → D₂ ≃ D₃ → D₁ ≃ D₃
≃-trans (equal d12 d21) (equal d23 d32) =
    equal (≲-trans d12 d23) (≲-trans d32 d21)

