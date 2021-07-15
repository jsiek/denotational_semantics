module GraphModel where

import Level
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic renaming (⊤ to ptop ; tt to ptt)

open import ModelISWIM
open import Sig

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

{- Iterated Function Abstraction -}

𝐺-iter : ∀ n → ArgTy (𝒫 Value) (ℕ→sig n) → 𝒫 Value
𝐺-iter zero f = f
𝐺-iter (suc n) f ⊥ = Bot
𝐺-iter (suc n) f (const c) = Bot
𝐺-iter (suc n) f (v ↦ w) = 𝐺-iter n (f (↓ v)) w
𝐺-iter (suc n) f (u ⊔ v) =
  𝐺-iter (suc n) f u  ×  𝐺-iter (suc n) f v

{- Denotations of natural numbers -}

𝟘 : 𝒫 Value
𝟘 v = const 0 ⊑ v

𝟙 : 𝒫 Value
𝟙 v = const 1 ⊑ v

ℕ⟦_⟧ : ℕ → 𝒫 Value
ℕ⟦ n ⟧ v = const n ⊑ v × v ⊑ const n

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

⟬_⟭ : ∀{n : ℕ} → Prod n (𝒫 Value) → 𝒫 Value
⟬_⟭ {n = zero} ptop u = ⊤
⟬_⟭ {n = suc n} ⟨ d , ds ⟩ u = (∀ w → d w → (const n) ↦ w ⊑ u) × ⟬ ds ⟭ u

ℕth : 𝒫 Value → ℕ → 𝒫 Value
ℕth d i = 𝐹 d ℕ⟦ i ⟧

test : ℕth (⟬_⟭ {1} ⟨ ℕ⟦ 42 ⟧ , Level.lift tt ⟩) 0 (const 42)
test = ⟨ (const 0) ,
       ⟨ wf-const , ⟨ ⟨ (λ w x → ⊑-fun′ ⊑-const (proj₂ x)) , tt ⟩ ,
       ⟨ ⊑-const , ⊑-const ⟩ ⟩ ⟩ ⟩
