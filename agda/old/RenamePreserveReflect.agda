{-# OPTIONS --rewriting #-}

open import Values
open import Primitives
open import Syntax using (Rename)
import ValueStructAux
import CurryApplyStruct

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.Bool.Properties using (∨-comm)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; inspect; [_])
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)

module RenamePreserveReflect
  (D : ValueStruct)
  (V : ValueOrdering D)
  (C : Consistent D V)
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
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
  open import Syntax using (Rename; ext; ⦉_⦊; ext-0; ext-suc)

  ⊑-ext-R : ∀ {γ : Env} {δ : Env} {ρ : Rename}{v}
        → γ `⊑ (δ ∘ ⦉ ρ ⦊)
          ---------------------------------
        → (γ `, v) `⊑ ((δ `, v) ∘ ⦉ ext ρ ⦊)
  ⊑-ext-R {ρ = ρ}{v = v} γ⊑δ∘ρ 0 rewrite ext-0 ρ = ⊑-refl
  ⊑-ext-R {ρ = ρ}{v = v} γ⊑δ∘ρ (suc x) rewrite ext-suc ρ x = γ⊑δ∘ρ x

  ⊑-ext-L : ∀ {γ : Env} {δ : Env} {ρ : Rename} {v}
        → (δ ∘ ⦉ ρ ⦊) `⊑ γ
          ---------------------------------
        → ((δ `, v) ∘ ⦉ ext ρ ⦊) `⊑ (γ `, v)
  ⊑-ext-L {ρ = ρ} δ∘ρ⊑γ 0 rewrite ext-0 ρ = ⊑-refl
  ⊑-ext-L {ρ = ρ} δ∘ρ⊑γ (suc x) rewrite ext-suc ρ x = δ∘ρ⊑γ x

  module ForLambda where
  
    open import Lambda
    open import LambdaDenot D V _●_ ℱ
    open ASTMod
      using (Subst; exts; ⟦_⟧; rename; rename-subst; rename-id; exts-0; exts-suc-rename)

    rename-pres : ∀ {v} {γ : Env} {δ : Env} {M : Term}
           → (ρ : Rename)
           → γ `⊑ (δ ∘ ⦉ ρ ⦊)
           → wf v
           → ℰ M γ v
             ------------------
           → ℰ (rename ρ M) δ v
    rename-pres {v = v}{γ}{δ}{` x} ρ γ⊑δ∘ρ wfv ℰMγv =
        v  ⊑⟨ ℰMγv ⟩ γ x  ⊑⟨ γ⊑δ∘ρ x ⟩ δ (⦉ ρ ⦊ x) ◼
    rename-pres {v}{γ}{δ}{lam ⦅ cons (bind (ast N)) nil ⦆} ρ γ⊑δ∘ρ =
       ℱ-≲ (λ wfv₁ → rename-pres {M = N} (ext ρ) (⊑-ext-R γ⊑δ∘ρ)) 

    rename-pres {M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆} ρ γ⊑δ∘ρ wfv =
        ●-≲ (rename-pres {M = L} ρ γ⊑δ∘ρ) (rename-pres {M = M} ρ γ⊑δ∘ρ) wfv

    ⊑-env : ∀ {γ : Env} {δ : Env} {M v}
      → wf v
      → γ `⊑ δ
      → ℰ M γ v
        ----------
      → ℰ M δ v
    ⊑-env {γ}{δ}{M}{v} wfv γ⊑δ ℰMγv
          with rename-pres {v}{γ}{δ}{M} id γ⊑δ wfv ℰMγv
    ... | d′ rewrite rename-id {M} =
          d′

    EnvExt⊑ : ∀ {γ : Env} {M v u₁ u₂}
      → wf v
      → u₁ ⊑ u₂
      → ℰ M (γ `, u₁) v
        -----------------
      → ℰ M (γ `, u₂) v
    EnvExt⊑ {M = M} wfv lt d = ⊑-env{M = M} wfv (env-le lt) d
      where
      env-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
      env-le lt 0 = lt
      env-le lt (suc n) = ⊑-refl

    rename-reflect : ∀ {γ : Env} {δ : Env} { M : Term}
                       {ρ : Rename}
      → (δ ∘ ⦉ ρ ⦊) `⊑ γ
        -------------------------
      → ℰ (rename ρ M) δ ≲ ℰ M γ
    rename-reflect {γ}{δ}{` x} {ρ} δ∘ρ⊑γ {v} wfv ℰρMδv =
       v  ⊑⟨ ℰρMδv ⟩ δ (⦉ ρ ⦊ x)  ⊑⟨ δ∘ρ⊑γ x ⟩  γ x ◼
    rename-reflect {γ}{δ}{lam ⦅ cons (bind (ast N)) nil ⦆} {ρ} δ∘ρ⊑γ =
       ℱ-≲ (λ wfv′ → rename-reflect{M = N}{ρ = ext ρ} (⊑-ext-L δ∘ρ⊑γ)) 
    rename-reflect {M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {ρ} δ∘ρ⊑γ =
       ●-≲ (rename-reflect{M = L}{ρ} δ∘ρ⊑γ) (rename-reflect{M = M}{ρ} δ∘ρ⊑γ)

    rename-inc-reflect : ∀ {v′ v} {γ : Env} { M : Term}
      → wf v
      → ℰ (rename (↑ 1) M) (γ `, v′) v
        ----------------------------
      → ℰ M γ v
    rename-inc-reflect {v = v}{M = M} wfv d =
       rename-reflect {M = M}{↑ 1} `Refl⊑ wfv d

    δu⊢extσ⊥ : ∀{δ : Env}{σ : Subst}{u}
             → δ `⊢ σ ↓ `⊥ → δ `, u `⊢ exts σ ↓ `⊥
    δu⊢extσ⊥ {σ = σ} δ⊢σ↓⊥ 0 rewrite exts-0 σ = ⊑-⊥
    δu⊢extσ⊥ {δ}{σ = σ}{u} δ⊢σ↓⊥ (suc x)
        rewrite sym (rename-subst (↑ 1) (⟦ σ ⟧ x)) | exts-suc-rename σ x =
        rename-pres {M = ⟦ σ ⟧ x} (↑ 1) (λ x₁ → ⊑-refl) wf-bot (δ⊢σ↓⊥ x)


  module ForISWIM
    (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
    where
  
    open import ISWIM
    open import ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open ASTMod using (⟦_⟧; rename-subst; FV?; exts-0; exts-suc-rename)

    rename-pres : ∀ {v} {γ : Env} {δ : Env} {M : Term}
           → (ρ : Rename)
           → γ `⊑ (δ ∘ ⦉ ρ ⦊)
           → wf v
           → ℰ M γ v
             ------------------
           → ℰ (rename ρ M) δ v
    rename-pres {M = $ P k} ρ γ⊑δ∘ρ wfv ℰMγv = ℰMγv
    rename-pres {v = v}{γ}{δ}{` x} ρ γ⊑δ∘ρ wfv ℰMγv =
        v  ⊑⟨ ℰMγv ⟩ γ x  ⊑⟨ γ⊑δ∘ρ x ⟩ δ (⦉ ρ ⦊ x) ◼
    rename-pres {v}{γ}{δ}{ƛ N} ρ γ⊑δ∘ρ =
        ℱ-≲ (λ wfv₁ → rename-pres {M = N} (ext ρ) (⊑-ext-R γ⊑δ∘ρ))
    rename-pres {M = L · M} ρ γ⊑δ∘ρ =
        ●-≲ (rename-pres {M = L} ρ γ⊑δ∘ρ) (rename-pres {M = M} ρ γ⊑δ∘ρ)

    {-

     A stronger version of rename-pres that only requires the
     environments to agree on free variables.

     -}
    rename-pres-FV : ∀ {M : Term} {v} {γ : Env} {δ : Env} 
           → (ρ : Rename)
           → (∀ x → T (FV? M x) → γ x ⊑ (δ ∘ ⦉ ρ ⦊) x)
           → wf v
           → ℰ M γ v
             ------------------
           → ℰ (rename ρ M) δ v
    rename-pres-FV {` x} {v} {γ} {δ} ρ γ⊑δ∘ρ wfv ℰMγv =
        v  ⊑⟨ ℰMγv ⟩ γ x  ⊑⟨ γ⊑δ∘ρ x G ⟩ δ (⦉ ρ ⦊ x) ◼
        where
        G : T (FV? (` x) x)
        G   with x ≟ x
        ... | yes xx = tt
        ... | no xx = xx refl
    rename-pres-FV {$ p k} {v} ρ γ⊑δ∘ρ wfv ℰMγv = ℰMγv
    rename-pres-FV {ƛ N} {v} {γ} {δ} ρ γ⊑δ∘ρ =
        ℱ-≲ (λ {v₁} wfv₁ {v₂} → rename-pres-FV {M = N} (ext ρ) G)
        where
        G : ∀{v₁} → (∀ x → T (FV? N x)
            → (γ `, v₁) x ⊑ ((δ `, v₁) ∘ ⦉ ext ρ ⦊) x)
        G {v₁} zero fvNx rewrite ext-0 ρ = ⊑-refl
        G {v₁} (suc x) fvNx rewrite ext-suc ρ x
            with FV? N (suc x) | inspect (FV? N) (suc x)
        ... | false | [ fvN[sx] ] = ⊥-elim fvNx
        ... | true | [ fvN[sx] ] = γ⊑δ∘ρ x H
            where H : T (FV? N (suc x) ∨ false)
                  H rewrite ∨-comm (FV? N (suc x)) false
                    | fvN[sx] = tt
    rename-pres-FV {L · M} {v} {γ} {δ} ρ γ⊑δ∘ρ =
        ●-≲ (rename-pres-FV {M = L} ρ γ⊑δ∘ρ[L])
            (rename-pres-FV {M = M} ρ γ⊑δ∘ρ[M])
        where
        γ⊑δ∘ρ[L] : (∀ x → T (FV? L x) → γ x ⊑ (δ ∘ ⦉ ρ ⦊) x)
        γ⊑δ∘ρ[L] x fvL
            with FV? L x | inspect (FV? L) x
        ... | false | [ fvLx ] = ⊥-elim fvL
        ... | true | [ fvLx ]
            with γ⊑δ∘ρ x
        ... | γ⊑δ∘ρ[x] rewrite fvLx = γ⊑δ∘ρ[x] tt

        γ⊑δ∘ρ[M] : (∀ x → T (FV? M x) → γ x ⊑ (δ ∘ ⦉ ρ ⦊) x)
        γ⊑δ∘ρ[M] x fvM
            with FV? M x | inspect (FV? M) x
        ... | false | [ fvMx ] = ⊥-elim fvM
        ... | true | [ fvMx ]
            with γ⊑δ∘ρ x
        ... | γ⊑δ∘ρ[x] rewrite fvMx | ∨-comm (FV? L x) true = γ⊑δ∘ρ[x] tt

    ⊑-env : ∀ {γ : Env} {δ : Env} {M v}
      → wf v
      → γ `⊑ δ
      → ℰ M γ v
        ----------
      → ℰ M δ v
    ⊑-env {γ}{δ}{M}{v} wfv lt d
          with rename-pres {v}{γ}{δ}{M} id lt wfv d
    ... | d′ rewrite rename-id {M} =
          d′

    EnvExt⊑ : ∀ {γ : Env} {M v u₁ u₂}
      → wf v
      → u₁ ⊑ u₂
      → ℰ M (γ `, u₁) v
        -----------------
      → ℰ M (γ `, u₂) v
    EnvExt⊑ {M = M} wfv lt d = ⊑-env{M = M} wfv (env-le lt) d
      where
      env-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
      env-le lt 0 = lt
      env-le lt (suc n) = ⊑-refl

    rename-reflect : ∀ {γ : Env} {δ : Env} { M : Term}
                       {ρ : Rename}
      → (δ ∘ ⦉ ρ ⦊) `⊑ γ
        -------------------------
      → ℰ (rename ρ M) δ ≲ ℰ M γ
    rename-reflect {M = $ P k} δ∘ρ⊑γ wfv ℰρMδv = ℰρMδv
    rename-reflect {γ}{δ}{` x} {ρ} δ∘ρ⊑γ {v} wfv ℰρMδv  =
       v  ⊑⟨ ℰρMδv ⟩ δ (⦉ ρ ⦊ x)  ⊑⟨ δ∘ρ⊑γ x ⟩  γ x ◼
    rename-reflect {γ}{δ}{ƛ N} {ρ} δ∘ρ⊑γ =
       ℱ-≲ (λ wfv′ → rename-reflect{M = N}{ρ = ext ρ} (⊑-ext-L δ∘ρ⊑γ)) 
    rename-reflect {M = L · M} {ρ} δ∘ρ⊑γ =
       ●-≲ (rename-reflect{M = L}{ρ} δ∘ρ⊑γ) (rename-reflect{M = M}{ρ} δ∘ρ⊑γ)

    rename-inc-reflect : ∀ {v′ v} {γ : Env} { M : Term}
      → wf v
      → ℰ (rename (↑ 1) M) (γ `, v′) v
        ----------------------------
      → ℰ M γ v
    rename-inc-reflect {M = M} wfv d = rename-reflect {M = M}{↑ 1} `Refl⊑ wfv d

    δu⊢extσ⊥ : ∀{δ : Env}{σ : Subst}{u}
             → δ `⊢ σ ↓ `⊥ → δ `, u `⊢ exts σ ↓ `⊥
    δu⊢extσ⊥ {σ = σ} δ⊢σ↓⊥ 0 rewrite exts-0 σ = ⊑-⊥
    δu⊢extσ⊥ {σ = σ} δ⊢σ↓⊥ (suc x) rewrite exts-suc-rename σ x
       | sym (rename-subst (↑ 1) (⟦ σ ⟧ x)) =
       rename-pres {M = ⟦ σ ⟧ x} (↑ 1) (λ x₁ → ⊑-refl) wf-bot (δ⊢σ↓⊥ x)

