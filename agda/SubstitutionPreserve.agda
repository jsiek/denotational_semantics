open import Variables
open import Structures
open import Primitives
import RenamePreserveReflect
import Filter

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


module SubstitutionPreserve
  (D : Domain)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (MB : OrderingAux.LambdaModelBasics D V _●_ ℱ)
  where

  open Domain D
  open DomainAux D
  open ValueOrdering V
  open OrderingAux D V
  open LambdaModelBasics MB

  module ForLambda where

    open import Lambda using (_·_; ƛ; Term; lam; app)
    open Lambda.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule)
    open Lambda.ASTMod
       using (`_; _⦅_⦆; Subst;
              exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
    open LambdaDenot D V _●_ ℱ
    open RenamePreserveReflect.ForLambda D V _●_ ℱ MB
      using (⊑-env; rename-pres)
    open Filter.ForLambda D V _●_ ℱ MB

    subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
       --------------------------
      → δ `, v `⊢ exts σ ↓ γ `, v
    subst-ext σ d Z = ⊑-refl
    subst-ext σ d (S x′) = rename-pres {M = σ x′} S_ (λ _ → ⊑-refl) (d x′)

    subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
      → ℰ M γ v
        ------------------
      → ℰ (⟪ σ ⟫ M) δ v
    subst-pres {M = ` x} σ δ⊢σ↓γ ℰMγv = ℰ-⊑ {M = σ x} (δ⊢σ↓γ x) ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} σ δ⊢σ↓γ ℰMγv =
       (ℱ-≲ {Γ}{Δ}{γ}{δ}{ℰ N}{ℰ (⟪ exts σ ⟫ N)}
             λ {v} → subst-pres {γ = γ `, v}{δ = δ `, v}{M = N} (exts σ)
                          (subst-ext σ δ⊢σ↓γ)) {v}
        ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆} σ δ⊢σ↓γ ℰMγv =
       (●-≲{Γ}{Δ}{γ}{δ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ (⟪ σ ⟫ L)}
            {D₂′ = ℰ (⟪ σ ⟫ M)}
            (λ ℰLγv → subst-pres {Γ}{Δ}{γ = γ}{δ}{L} σ δ⊢σ↓γ ℰLγv)
            (λ ℰMδv → subst-pres {Γ}{Δ}{γ = γ}{δ}{M} σ δ⊢σ↓γ ℰMδv))
        ℰMγv

    substitution : ∀ {Γ} {γ : Env Γ} {N M v w}
       → ℰ N (γ `, v) w
       → ℰ M γ v
         ---------------
       → ℰ (N [ M ]) γ w   
    substitution{Γ}{γ}{N}{M}{v}{w} dn dm =
      subst-pres{M = N} (subst-zero M) sub-z-ok dn
      where
      sub-z-ok : γ `⊢ subst-zero M ↓ (γ `, v)
      sub-z-ok Z = dm
      sub-z-ok (S x) = ⊑-refl

  module ISWIM
    (℘ : ∀{P : Prim} → rep P → Domain.Value D → Set)
    (℘-⊔ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → ℘ {P} D (u ⊔ v))
    (℘-⊑ : ∀{P : Prim} {D : rep P} {v w : Value}
          → ℘ {P} D v → w ⊑ v → ℘ {P} D w)
    where

    open import ISWIM
    open ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM D V _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
      using (⊑-env; rename-pres)
    open Filter.ForISWIM D V _●_ ℱ MB (λ {P} k v → ℘ {P} k v) ℘-⊔ ℘-⊑

    subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
       --------------------------
      → δ `, v `⊢ exts σ ↓ γ `, v
    subst-ext σ d Z = ⊑-refl
    subst-ext σ d (S x′) = rename-pres {M = σ x′} S_ (λ _ → ⊑-refl) (d x′)

    subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
      → ℰ M γ v
        ------------------
      → ℰ (⟪ σ ⟫ M) δ v
    subst-pres {M = lit {P} k ⦅ nil ⦆} σ δ⊢σ↓γ ℰMγv = ℰMγv
    subst-pres {M = ` x} σ δ⊢σ↓γ ℰMγv = ℰ-⊑ {M = σ x} (δ⊢σ↓γ x) ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} σ δ⊢σ↓γ ℰMγv =
       (ℱ-≲ {Γ}{Δ}{γ}{δ}{ℰ N}{ℰ (⟪ exts σ ⟫ N)}
             λ {v} → subst-pres {γ = γ `, v}{δ = δ `, v}{M = N} (exts σ)
                          (subst-ext σ δ⊢σ↓γ)) {v}
        ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆} σ δ⊢σ↓γ ℰMγv =
       (●-≲{Γ}{Δ}{γ}{δ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ (⟪ σ ⟫ L)}
            {D₂′ = ℰ (⟪ σ ⟫ M)}
            (λ ℰLγv → subst-pres {Γ}{Δ}{γ = γ}{δ}{L} σ δ⊢σ↓γ ℰLγv)
            (λ ℰMδv → subst-pres {Γ}{Δ}{γ = γ}{δ}{M} σ δ⊢σ↓γ ℰMδv))
        ℰMγv

    substitution : ∀ {Γ} {γ : Env Γ} {N M v w}
       → ℰ N (γ `, v) w
       → ℰ M γ v
         ---------------
       → ℰ (N [ M ]) γ w   
    substitution{Γ}{γ}{N}{M}{v}{w} dn dm =
      subst-pres{M = N} (subst-zero M) sub-z-ok dn
      where
      sub-z-ok : γ `⊢ subst-zero M ↓ (γ `, v)
      sub-z-ok Z = dm
      sub-z-ok (S x) = ⊑-refl
