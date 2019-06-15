open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary.Negation using (contradiction)


open import Variables
open import Structures
import ValueStructAux


module ConsistentAux (D : ValueStruct) (V : ValueOrdering D) (C : Consistent D V)
  where
  open ValueStruct D
  open ValueOrdering V
  open Consistent C
  open ValueStructAux D

  wf : Value → Set
  wf v = v ~ v

  WFEnv : ∀ {Γ : ℕ} → Env Γ → Set
  WFEnv {Γ} γ = ∀{x : Var Γ} → wf (γ x)

  _~′_ : ∀{Γ} → Env Γ → Env Γ → Set
  _~′_ {Γ} γ δ = ∀{x : Var Γ} → γ x ~ δ x

{-
  ~′-refl : ∀{Γ}{γ : Env Γ} → γ ~′ γ
  ~′-refl {Γ}{γ}{x} = ~-refl
-}
  
  app-consistency : ∀{u₁ u₂ v₁ w₁ v₂ w₂}
        → u₁ ~ u₂
        → v₁ ~ v₂
        → v₁ ↦ w₁ ⊑ u₁
        → v₂ ↦ w₂ ⊑ u₂
        → w₁ ~ w₂
  app-consistency {u₁}{u₂}{v₁}{w₁}{v₂}{w₂} u₁~u₂ v₁~v₂ v₁↦w₁⊑u₁ v₂↦w₂⊑u₂
      with ~-⊑ u₁~u₂ v₁↦w₁⊑u₁ v₂↦w₂⊑u₂
  ... | v₁↦w₁~v₂↦w₂ 
      with ~-↦ {v₁}{w₁}{v₂}{w₂} v₁↦w₁~v₂↦w₂ 
  ... | inj₁ ⟨ _ , w₁~w₂ ⟩ = w₁~w₂
  ... | inj₂ v₁~̸v₂ = ⊥-elim (contradiction v₁~v₂ v₁~̸v₂)


  wf-⊔ : ∀{u v} → u ~ v → wf u → wf v → wf (u ⊔ v)
  wf-⊔ {u}{v} u~v wfu wfv = ~-⊔-cong wfu u~v (~-sym u~v) wfv
