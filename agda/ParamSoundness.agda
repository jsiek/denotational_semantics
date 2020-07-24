
open import Values
open import LambdaV
  using (AST; $; _·_; ƛ; Term; t-var; t-lam; t-app; Subst; ⌊_⌋; ⟪_⟫; lam; app)
open LambdaV.ASTMod using (Var; Z; S_; `_; α_; _⦅_⦆; extensionality; Subst; exts)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)


module ParamSoundness
  (D : Set)
  (_⊑_ : D → D → Set)
  (_⊔_ : D → D → D)
  where

  module LM = LambdaModelMod D _⊑_ _⊔_
  open LM
  open LambdaModel

  import ParamDenot
  module Denot = ParamDenot D model
  open Denot

  `ℰ : ∀{Δ Γ} → TSubst Γ Δ → Env Δ D → Env Γ D → Set
  `ℰ {Δ}{Γ} σ δ γ = (x : Var Γ) → ℰ (σ x) δ (γ x)

  subst-pres : ∀ {Γ Δ} {γ : Env Γ D} {δ : Env Δ D} {M : Term Γ}{v : D}
    → (σ : TSubst Γ Δ)
    → `ℰ σ δ γ
    → ℰ M γ v → ℰ (⟪ σ ⟫ M) δ v
  subst-pres {Γ}{Δ}{γ = γ}{δ = δ} {M = ⟨ _ , t-var x ⟩}{v} σ ℰσδγ ℰMγv =
     ℰ-⊑{M = ⟪ σ ⟫ ⟨ ` x , t-var x ⟩}{γ = δ}{v = γ x}{w = v} (ℰσδγ x) ℰMγv
  subst-pres {M = ⟨ lam ⦅ (α N) ∷ [] ⦆ , t-lam Nt ⟩} σ ℰσδγ = {!!}
  subst-pres {M = ⟨ app ⦅ L ∷ M ∷ [] ⦆ , t-app Lt Mt ⟩} σ ℰσδγ = {!!}
