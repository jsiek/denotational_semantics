open import Structures
open import Variables
open import Primitives
import Syntax3
import ValueStructAux
import CurryApplyStruct

open import Data.Bool using (Bool)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_; Dec; yes; no)

module RenamePreserveReflect
  (D : ValueStruct)
  (V : ValueOrdering D)
  (C : Consistent D V)
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
     → ValueStructAux.Denotation D Γ)
  (MV : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  where
  
  open ValueStruct D
  open ValueStructAux D
  open ValueOrdering V
  open import OrderingAux D V
  open Consistent C
  open import ConsistentAux D V C
  open CurryApplyStruct.CurryApplyStruct MV
  open CurryApplyStruct.CurryStruct model_curry

  ⊑-ext-R : ∀{Γ Δ} {γ : Env Γ} {δ : Env Δ} {ρ : Rename Γ Δ}{v}
        → γ `⊑ (δ ∘ ρ)
          ------------------------------
        → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
  ⊑-ext-R {v = v} γ⊑δ∘ρ Z = ⊑-refl
  ⊑-ext-R {v = v} γ⊑δ∘ρ (S x) = γ⊑δ∘ρ x

  ⊑-ext-L : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {ρ : Rename Γ Δ} {v}
        → (δ ∘ ρ) `⊑ γ
          ---------------------------------
        → ((δ `, v) ∘ ext ρ) `⊑ (γ `, v)
  ⊑-ext-L δ∘ρ⊑γ Z = ⊑-refl
  ⊑-ext-L δ∘ρ⊑γ (S x) = δ∘ρ⊑γ x

  module ForLambda where
  
    open import Lambda
    open import LambdaDenot D V _●_ ℱ

    rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
           → (ρ : Rename Γ Δ)
           → γ `⊑ (δ ∘ ρ)
           → wf v
           → ℰ M γ v
             ------------------
           → ℰ (rename ρ M) δ v
    rename-pres {v = v}{γ}{δ}{` x} ρ γ⊑δ∘ρ wfv ℰMγv =
        v  ⊑⟨ ℰMγv ⟩ γ x  ⊑⟨ γ⊑δ∘ρ x ⟩ δ (ρ x) ◼
    rename-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ cons (bind (ast N)) nil ⦆} ρ γ⊑δ∘ρ =
       ℱ-≲ (λ wfv₁ → rename-pres {M = N} (ext ρ) (⊑-ext-R γ⊑δ∘ρ)) 

    rename-pres {M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆} ρ γ⊑δ∘ρ wfv =
        ●-≲ (rename-pres {M = L} ρ γ⊑δ∘ρ) (rename-pres {M = M} ρ γ⊑δ∘ρ) wfv

    ⊑-env : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
      → wf v
      → γ `⊑ δ
      → ℰ M γ v
        ----------
      → ℰ M δ v
    ⊑-env{Γ}{γ}{δ}{M}{v} wfv γ⊑δ ℰMγv
          with rename-pres{Γ}{Γ}{v}{γ}{δ}{M} (λ x → x) γ⊑δ wfv ℰMγv
    ... | d′ rewrite rename-id {Γ}{M} =
          d′

    EnvExt⊑ : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
      → wf v
      → u₁ ⊑ u₂
      → ℰ M (γ `, u₁) v
        -----------------
      → ℰ M (γ `, u₂) v
    EnvExt⊑ {M = M} wfv lt d = ⊑-env{M = M} wfv (env-le lt) d
      where
      env-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
      env-le lt Z = lt
      env-le lt (S n) = ⊑-refl

    rename-reflect : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} { M : Term Γ}
                       {ρ : Rename Γ Δ}
      → (δ ∘ ρ) `⊑ γ
        -------------------------
      → ℰ (rename ρ M) δ ≲ ℰ M γ
    rename-reflect {Γ}{Δ}{γ}{δ}{` x} {ρ} δ∘ρ⊑γ {v} wfv ℰρMδv =
       v  ⊑⟨ ℰρMδv ⟩ δ (ρ x)  ⊑⟨ δ∘ρ⊑γ x ⟩  γ x ◼
    rename-reflect {Γ}{Δ}{γ}{δ}{lam ⦅ cons (bind (ast N)) nil ⦆} {ρ} δ∘ρ⊑γ =
       ℱ-≲ (λ wfv′ → rename-reflect{M = N}{ρ = ext ρ} (⊑-ext-L δ∘ρ⊑γ)) 
    rename-reflect {M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {ρ} δ∘ρ⊑γ =
       ●-≲ (rename-reflect{M = L} δ∘ρ⊑γ) (rename-reflect{M = M} δ∘ρ⊑γ)

    rename-inc-reflect : ∀ {Γ v′ v} {γ : Env Γ} { M : Term Γ}
      → wf v
      → ℰ (rename S_ M) (γ `, v′) v
        ----------------------------
      → ℰ M γ v
    rename-inc-reflect {v = v}{M = M} wfv d =
       rename-reflect {M = M} `Refl⊑ wfv d

    δu⊢extσ⊥ : ∀{Γ}{Δ}{δ : Env Δ}{σ : Subst Γ Δ}{u}
             → δ `⊢ σ ↓ `⊥ → δ `, u `⊢ exts σ ↓ `⊥
    δu⊢extσ⊥ δ⊢σ↓⊥ Z = ⊑-⊥
    δu⊢extσ⊥ {σ = σ} δ⊢σ↓⊥ (S x) =
       rename-pres {M = σ x} S_ (λ x₁ → ⊑-refl) wf-bot (δ⊢σ↓⊥ x) 

  module ForISWIM
    (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
    where
  
    open import ISWIM
    open import ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)

    rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
           → (ρ : Rename Γ Δ)
           → γ `⊑ (δ ∘ ρ)
           → wf v
           → ℰ M γ v
             ------------------
           → ℰ (rename ρ M) δ v
    rename-pres {M = $ P k} ρ γ⊑δ∘ρ wfv ℰMγv = ℰMγv
    rename-pres {v = v}{γ}{δ}{` x} ρ γ⊑δ∘ρ wfv ℰMγv =
        v  ⊑⟨ ℰMγv ⟩ γ x  ⊑⟨ γ⊑δ∘ρ x ⟩ δ (ρ x) ◼
    rename-pres {Γ}{Δ}{v}{γ}{δ}{ƛ N} ρ γ⊑δ∘ρ =
        ℱ-≲ (λ wfv₁ → rename-pres {M = N} (ext ρ) (⊑-ext-R γ⊑δ∘ρ))
    rename-pres {M = L · M} ρ γ⊑δ∘ρ =
        ●-≲ (rename-pres {M = L} ρ γ⊑δ∘ρ) (rename-pres {M = M} ρ γ⊑δ∘ρ)

    ⊑-env : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
      → wf v
      → γ `⊑ δ
      → ℰ M γ v
        ----------
      → ℰ M δ v
    ⊑-env{Γ}{γ}{δ}{M}{v} wfv lt d
          with rename-pres{Γ}{Γ}{v}{γ}{δ}{M} (λ x → x) lt wfv d
    ... | d′ rewrite rename-id {Γ}{M} =
          d′

    EnvExt⊑ : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
      → wf v
      → u₁ ⊑ u₂
      → ℰ M (γ `, u₁) v
        -----------------
      → ℰ M (γ `, u₂) v
    EnvExt⊑ {M = M} wfv lt d = ⊑-env{M = M} wfv (env-le lt) d
      where
      env-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
      env-le lt Z = lt
      env-le lt (S n) = ⊑-refl

    rename-reflect : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} { M : Term Γ}
                       {ρ : Rename Γ Δ}
      → (δ ∘ ρ) `⊑ γ
        -------------------------
      → ℰ (rename ρ M) δ ≲ ℰ M γ
    rename-reflect {M = $ P k} δ∘ρ⊑γ wfv ℰρMδv = ℰρMδv
    rename-reflect {Γ}{Δ}{γ}{δ}{` x} {ρ} δ∘ρ⊑γ {v} wfv ℰρMδv  =
       v  ⊑⟨ ℰρMδv ⟩ δ (ρ x)  ⊑⟨ δ∘ρ⊑γ x ⟩  γ x ◼
    rename-reflect {Γ}{Δ}{γ}{δ}{ƛ N} {ρ} δ∘ρ⊑γ =
       ℱ-≲ (λ wfv′ → rename-reflect{M = N}{ρ = ext ρ} (⊑-ext-L δ∘ρ⊑γ)) 
    rename-reflect {M = L · M} {ρ} δ∘ρ⊑γ =
       ●-≲ (rename-reflect{M = L} δ∘ρ⊑γ) (rename-reflect{M = M} δ∘ρ⊑γ)

    rename-inc-reflect : ∀ {Γ v′ v} {γ : Env Γ} { M : Term Γ}
      → wf v
      → ℰ (rename S_ M) (γ `, v′) v
        ----------------------------
      → ℰ M γ v
    rename-inc-reflect {M = M} wfv d = rename-reflect {M = M} `Refl⊑ wfv d

    δu⊢extσ⊥ : ∀{Γ}{Δ}{δ : Env Δ}{σ : Subst Γ Δ}{u}
             → δ `⊢ σ ↓ `⊥ → δ `, u `⊢ exts σ ↓ `⊥
    δu⊢extσ⊥ δ⊢σ↓⊥ Z = ⊑-⊥
    δu⊢extσ⊥ {σ = σ} δ⊢σ↓⊥ (S x) =
       rename-pres {M = σ x} S_ (λ x₁ → ⊑-refl) wf-bot (δ⊢σ↓⊥ x)

