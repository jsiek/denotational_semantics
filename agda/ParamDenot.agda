open import Primitives
open import LambdaV
   using (AST; $; _·_; ƛ; Term; t-var; t-lam; t-app; lam; app; rename)
open LambdaV.ASTMod
   using (Var; Z; S_; `_; α_; _⦅_⦆; extensionality; Rename; Subst; ext; exts)
open import Structures

open import Data.List using (List; []; _∷_)
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)

module ParamDenot
    (D : Set)
    (_⊑_ : D → D → Set)
    (_⊔_ : D → D → D)
    where

module LM = LambdaModelMod D _⊑_ _⊔_
open LM

module Denot (model : LambdaModel) where

  open LambdaModel model

  ℰ : ∀{Γ} → Term Γ → Denotation Γ
  ℰ ⟨ _ , t-var x ⟩ = var x
  ℰ ⟨ lam ⦅ (α N) ∷ [] ⦆ , t-lam Nt ⟩ = ℱ (ℰ ⟨ N , Nt ⟩)
  ℰ ⟨ app ⦅ L ∷ M ∷ [] ⦆ , t-app Lt Mt ⟩ = (ℰ ⟨ L , Lt ⟩) ● (ℰ ⟨ M , Mt ⟩)

  {-
  ℰ-⊑ : ∀{Γ}{M : Term Γ}{γ : Env Γ}{v w : D}
      → ℰ M γ v  → w ⊑ v
        ----------------
      → ℰ M γ w
  ℰ-⊑ {M = ⟨ _ , t-var x ⟩} ℰMγv w⊑v = Trans⊑ w⊑v ℰMγv
  ℰ-⊑ {M = ⟨ lam ⦅ (α N) ∷ [] ⦆ , t-lam Nt ⟩} ℰMγv w⊑v =
     ?
  ℰ-⊑ {M = ⟨ app ⦅ L ∷ M ∷ [] ⦆ , t-app Lt Mt ⟩}{γ}{v}{w} ℰMγv w⊑v =
     ?
  -}
  {-
  var-inv : ∀ {Γ v x} {γ : Env Γ}
    → ℰ (` x) γ v
      -------------------
    → v ⊑ γ x
  var-inv (ℰ-var) = Refl⊑
  var-inv (ℰ-⊔ d₁ d₂) = ConjL⊑ (var-inv d₁) (var-inv d₂)
  var-inv (ℰ-⊑ d lt) = Trans⊑ lt (var-inv d)

  lambda-inversion
    : ∀{Γ} {γ : Env Γ} {M : Term Γ} {N : Term (suc Γ)} {v v₁ v₂ : Value}
    → ℰ M γ v → M ≡ (ƛ N) → v ≡ (v₁ ↦ v₂)
      -----------------------------------
    → ℰ N (γ `, v₁) v₂
  lambda-inversion {v₁ = v₁} {v₂} ℰ-var ()
  lambda-inversion {v₁ = v₁} {v₂} (ℰ-lit x) ()
  lambda-inversion {v₁ = v₁} {v₂} (ℰ-app d d₁) ()
  lambda-inversion {v₁ = v₁} {v₂} (ℰ-lam{v₁ = u₁}{v₂ = u₂} d) refl eq
      with Cong↦ eq 
  ... | ⟨ eq1 , eq2 ⟩ rewrite eq1 | eq2 =
      d
  lambda-inversion {v₁ = v₁} {v₂} ℰ-⊥ eq1 eq2 = ⊥-elim (⊥≢↦ eq2)
  lambda-inversion {v₁ = v₁} {v₂} (ℰ-⊔ d d₁) eq1 eq2 = ⊥-elim (⊔≢↦ eq2)
  lambda-inversion {v₁ = v₁} {v₂} (ℰ-⊑ ℰMv₁ v⊑v₁) eq1 eq2 =

    {!!}
  -}

{-
  lambda-inversion
    : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v v₁ v₂ : Value}
    → Denotation.E (ℱ D) γ v → v ≡ (v₁ ↦ v₂)
      --------------------------------------------------
    → ℰ N (γ `, v₁) v₂
-}

  ext-nth : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
    → (ρ : Rename Γ Δ)
    → γ `⊑ (δ ∘ ρ)
      ------------------------------
    → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
  ext-nth ρ lt Z = Refl⊑
  ext-nth ρ lt (S n′) = lt n′

  rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
    → (ρ : Rename Γ Δ)
    → γ `⊑ (δ ∘ ρ)
    → Denotation.E (ℰ M) γ v
      ---------------------------------
    → Denotation.E (ℰ (rename ρ M)) δ v
  rename-pres {Γ} {Δ} {v} {γ} {δ} {⟨ _ , t-var x ⟩} ρ γ⊑δ∘ρ ℰMγv =
    {!!}
  rename-pres {Γ} {Δ} {v} {γ} {δ} {⟨ (lam ⦅ (α N) ∷ [] ⦆) , t-lam Nt ⟩} ρ γ⊑δ∘ρ ℱℰNγv =
     let ih = rename-pres {v = v}{γ `, v}{δ `, v}{⟨ N , Nt ⟩ } (ext ρ) (ext-nth ρ γ⊑δ∘ρ) {!!} in
     {!!}
{-
    let ih = rename-pres {v = v}{δ = δ `, v}{M = {!!}} (ext ρ) (ext-nth ρ γ⊑δ∘ρ) ℰNγv in
    ih
-}
  rename-pres {Γ} {Δ} {v} {γ} {δ} {⟨ (app ⦅ L ∷ M ∷ [] ⦆) , t-app Lt Mt ⟩} ρ γ⊑δ∘ρ ℰMγv = {!!}




  {-
  rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
    → (ρ : Rename Γ Δ)
    → γ `⊑ (δ ∘ ρ)
    → ℰ M γ v
      ---------------------
    → ℰ (rename ρ M) δ v
  rename-pres ρ lt (ℰ-lit p) = ℰ-lit p
  rename-pres {Γ}{Δ}{c}{γ}{δ}{M} ρ lt (ℰ-var {x = x}) =
     ℰ-⊑ (ℰ-var{Δ}{δ}{ρ x}) (lt x)
  rename-pres ρ lt (ℰ-app d d₁) =
     ℰ-app (rename-pres ρ lt d) (rename-pres ρ lt d₁) 
  rename-pres ρ lt (ℰ-lam d) =
     ℰ-lam (rename-pres (ext ρ) (ext-nth ρ lt) d)
  rename-pres ρ lt ℰ-⊥ = ℰ-⊥
  rename-pres ρ lt (ℰ-⊔ d d₁) =
     ℰ-⊔ (rename-pres ρ lt d) (rename-pres ρ lt d₁)
  rename-pres ρ lt (ℰ-⊑ d lt′) =
     ℰ-⊑ (rename-pres ρ lt d) lt′


  `ℰ : ∀{Δ Γ} → Subst Γ Δ → Env Δ → Env Γ → Set
  `ℰ {Δ}{Γ} σ δ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))

  subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
    → (σ : Subst Γ Δ)
    → `ℰ σ δ γ
     ------------------------------
    → `ℰ (exts σ) (δ `, v) (γ `, v)
  subst-ext σ d Z = ℰ-var
  subst-ext σ d (S x′) = rename-pres S_ (λ _ → Refl⊑) (d x′)

  -}
