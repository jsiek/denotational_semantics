open import Structures
open import Variables
open import Lambda using (_·_; ƛ; Term; lam; app)
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)

module RenamePreserveReflect
  (D : Domain)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (MV : OrderingAux.LambdaModelBasics D V _●_ ℱ)
  where
  
  open Domain D
  open DomainAux D
  open ValueOrdering V
  open OrderingAux D V
  open LambdaDenot D V _●_ ℱ
  open LambdaModelBasics MV

  ⊑-ext-R : ∀{Γ Δ} {γ : Env Γ} {δ : Env Δ} {ρ : Rename Γ Δ}{v}
        → γ `⊑ (δ ∘ ρ)
          ------------------------------
        → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
  ⊑-ext-R {v = v} γ⊑δ∘ρ Z = ⊑-refl
  ⊑-ext-R {v = v} γ⊑δ∘ρ (S x) = γ⊑δ∘ρ x

  rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
         → (ρ : Rename Γ Δ)
         → γ `⊑ (δ ∘ ρ)
         → ℰ M γ v
           ------------------
         → ℰ (rename ρ M) δ v
  rename-pres {v = v}{γ}{δ}{` x} ρ γ⊑δ∘ρ ℰMγv =
      v  ⊑⟨ ℰMγv ⟩ γ x  ⊑⟨ γ⊑δ∘ρ x ⟩ δ (ρ x) ◼
  rename-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} ρ γ⊑δ∘ρ =
      ℱ-≲ (rename-pres {M = N} (ext ρ) (⊑-ext-R γ⊑δ∘ρ)) {v}
  rename-pres {M = app ⦅ cons L (cons M nil) ⦆} ρ γ⊑δ∘ρ =
      ●-≲ (rename-pres {M = L} ρ γ⊑δ∘ρ) (rename-pres {M = M} ρ γ⊑δ∘ρ)

  ⊑-env : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
    → ℰ M γ v
    → γ `⊑ δ
      ----------
    → ℰ M δ v
  ⊑-env{Γ}{γ}{δ}{M}{v} d lt
        with rename-pres{Γ}{Γ}{v}{γ}{δ}{M} (λ x → x) lt d
  ... | d′ rewrite rename-id {Γ}{M} =
        d′

  EnvExt⊑ : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
    → ℰ M (γ `, u₁) v
    → u₁ ⊑ u₂
      -----------------
    → ℰ M (γ `, u₂) v
  EnvExt⊑ {M = M} d lt = ⊑-env{M = M} d (env-le lt)
    where
    env-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
    env-le lt Z = lt
    env-le lt (S n) = ⊑-refl

  ⊑-ext-L : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {ρ : Rename Γ Δ} {v}
        → (δ ∘ ρ) `⊑ γ
          ---------------------------------
        → ((δ `, v) ∘ ext ρ) `⊑ (γ `, v)
  ⊑-ext-L δ∘ρ⊑γ Z = ⊑-refl
  ⊑-ext-L δ∘ρ⊑γ (S x) = δ∘ρ⊑γ x

  rename-reflect : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} { M : Term Γ}
                     {ρ : Rename Γ Δ}
    → (δ ∘ ρ) `⊑ γ
      -------------------------
    → ℰ (rename ρ M) δ ≲ ℰ M γ
  rename-reflect {Γ}{Δ}{γ}{δ}{` x} {ρ} δ∘ρ⊑γ {v} ℰρMδv  =
     v  ⊑⟨ ℰρMδv ⟩ δ (ρ x)  ⊑⟨ δ∘ρ⊑γ x ⟩  γ x ◼
  rename-reflect {Γ}{Δ}{γ}{δ}{lam ⦅ bind N nil ⦆} {ρ} δ∘ρ⊑γ {v} =
     ℱ-≲ (rename-reflect{M = N}{ρ = ext ρ} (⊑-ext-L δ∘ρ⊑γ)) {v}
  rename-reflect {M = app ⦅ cons L (cons M nil) ⦆} {ρ} δ∘ρ⊑γ =
     ●-≲ (rename-reflect{M = L} δ∘ρ⊑γ) (rename-reflect{M = M} δ∘ρ⊑γ)

  rename-inc-reflect : ∀ {Γ v′ v} {γ : Env Γ} { M : Term Γ}
    → ℰ (rename S_ M) (γ `, v′) v
      ----------------------------
    → ℰ M γ v
  rename-inc-reflect {M = M} d = rename-reflect {M = M} `Refl⊑ d

  rename-equiv : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {M : Term Γ} {ρ : Rename Γ Δ}
    → γ `≡ (δ ∘ ρ)
      ------------------------
    → ℰ M γ ≃ ℰ (rename ρ M) δ
  rename-equiv {γ = γ}{δ}{M}{ρ} γ≡δ∘ρ =
      ⟨ rename-pres {M = M} ρ γ⊑δ∘ρ , rename-reflect {M = M} {ρ} δ∘ρ⊑γ ⟩
      where γ⊑δ∘ρ : γ `⊑ (δ ∘ ρ)
            γ⊑δ∘ρ x rewrite γ≡δ∘ρ x = ⊑-refl

            δ∘ρ⊑γ : (δ ∘ ρ) `⊑ γ
            δ∘ρ⊑γ x rewrite γ≡δ∘ρ x = ⊑-refl

