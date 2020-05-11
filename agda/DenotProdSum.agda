module DenotProdSum where

open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import ModelISWIM
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
𝟘 γ v = ℘ {base Nat} 0 v

𝟙 : Denotation
𝟙 γ v = ℘ {base Nat} 1 v

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

