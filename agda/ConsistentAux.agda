open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary.Negation using (contradiction)


open import Variables
open import Structures
import ValueStructAux


module ConsistentAux
  (D : ValueStruct) (V : ValueOrdering D) (C : Consistent D V)
  where
  
  open ValueStruct D
  open ValueOrdering V
  open import OrderingAux D V
  open Consistent C
  open ValueStructAux D

  WFEnv : ∀ {Γ : ℕ} → Env Γ → Set
  WFEnv {Γ} γ = ∀{x : Var Γ} → wf (γ x)

  WFEnv-extend : ∀{Γ}{γ : Env Γ}{v}
              → WFEnv {Γ} γ
              → wf v
              → WFEnv {suc Γ} (γ `, v)
  WFEnv-extend {Γ} {γ} {v} wfγ wfv {Z} = wfv
  WFEnv-extend {Γ} {γ} {v} wfγ wfv {S x} = wfγ

  _~′_ : ∀{Γ} → Env Γ → Env Γ → Set
  _~′_ {Γ} γ δ = ∀{x : Var Γ} → γ x ~ δ x

  ~′-refl : ∀{Γ}{γ : Env Γ}
              → WFEnv {Γ} γ
              → γ ~′ γ
  ~′-refl {Γ}{γ} wfγ {x} = ~-refl {γ x} {wfγ} 


  ~′-extend : ∀{Γ}{γ δ : Env Γ}{u v}
            → γ ~′ δ → u ~ v
            → (γ `, u) ~′ (δ `, v)
  ~′-extend γ~′δ u~v {Z} = u~v
  ~′-extend γ~′δ u~v {S x} = γ~′δ

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


  ~-↦-~ : ∀{v w v′ w′} → (v ↦ w ~ v′ ↦ w′) → v ~ v′ → w ~ w′
  ~-↦-~ vw~vw′ v~v'
      with ~-↦ vw~vw′
  ... | inj₁ ⟨ _ , w~w′ ⟩ = w~w′
  ... | inj₂ ¬v~v′ = ⊥-elim (contradiction v~v' ¬v~v′)
