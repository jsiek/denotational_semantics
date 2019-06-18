open import Variables
open import Structures
open import Primitives
import RenamePreserveReflect
import Filter
import ValueStructAux
import CurryApplyStruct

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
  (D : ValueStruct)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
     → ValueStructAux.Denotation D Γ)
  (C : Consistent D V)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  where

  open ValueStruct D
  open ValueStructAux D
  open ValueOrdering V
  open Consistent C
  open import OrderingAux D V
  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry
  open import ConsistentAux D V C

  module ForLambda where

    open import Lambda using (_·_; ƛ; Term; lam; app)
    open Lambda.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule)
    open Lambda.ASTMod
       using (`_; _⦅_⦆; Subst;
              exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
    open import LambdaDenot D V _●_ ℱ
    open RenamePreserveReflect.ForLambda D V _●_ ℱ C MB
      using (⊑-env; rename-pres)
    open Filter.ForLambda D V _●_ ℱ C MB

    subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
       --------------------------
      → δ `, v `⊢ exts σ ↓ γ `, v
    subst-ext σ d Z = ⊑-refl
    subst-ext σ d (S x′) = rename-pres {M = σ x′} S_ (λ _ → ⊑-refl) (d x′)

    subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
      → WFEnv γ → WFEnv δ → wf v
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
      → ℰ M γ v
        ------------------
      → ℰ (⟪ σ ⟫ M) δ v
    subst-pres {M = ` x} wfγ wfδ wfv σ δ⊢σ↓γ ℰMγv =
        ℰ-⊑ {M = σ x} wfδ wfγ wfv ℰMγv (δ⊢σ↓γ x)
    subst-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} wfγ wfδ wfv σ δ⊢σ↓γ ℰMγv =
       (ℱ-≲ {Γ}{Δ}{ℰ N}{ℰ (⟪ exts σ ⟫ N)}{γ}{δ}
             λ {v′} wfv′ → subst-pres {γ = γ `, v′}{δ = δ `, v′}{M = N} (WFEnv-extend wfγ wfv) (WFEnv-extend wfδ wfv) {!wfv′!}
                       (exts σ) (subst-ext σ δ⊢σ↓γ)) {v}
        ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆}
       wfγ wfδ wfv σ δ⊢σ↓γ ℰMγv =
       {!!}
{-       
       (●-≲{Γ}{Δ}{γ}{δ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ (⟪ σ ⟫ L)}
            {D₂′ = ℰ (⟪ σ ⟫ M)}
            (λ ℰLγv → subst-pres {Γ}{Δ}{γ = γ}{δ}{L} σ δ⊢σ↓γ ℰLγv)
            (λ ℰMδv → subst-pres {Γ}{Δ}{γ = γ}{δ}{M} σ δ⊢σ↓γ ℰMδv))
        ℰMγv
-}

    substitution : ∀ {Γ} {γ : Env Γ} {N M v w}
       → ℰ N (γ `, v) w
       → ℰ M γ v
         ---------------
       → ℰ (N [ M ]) γ w   
    substitution{Γ}{γ}{N}{M}{v}{w} dn dm =
      subst-pres{M = N} {!!} {!!} {!!} (subst-zero M) sub-z-ok dn
      where
      sub-z-ok : γ `⊢ subst-zero M ↓ (γ `, v)
      sub-z-ok Z = dm
      sub-z-ok (S x) = ⊑-refl


  module ISWIM
    (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
    (℘-⊔ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → ℘ {P} D (u ⊔ v))
    (℘-⊑ : ∀{P : Prim} {D : rep P} {v w : Value}
          → ℘ {P} D v → w ⊑ v → ℘ {P} D w)
    (℘-~ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → u ~ v)
    where

    open import ISWIM
    open import ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM D V _●_ ℱ C MB (λ {P} k v → ℘ {P} k v)
      using (⊑-env; rename-pres)
    open Filter.ForISWIM D V _●_ ℱ C MB (λ {P} k v → ℘ {P} k v) ℘-⊔ ℘-⊑ ℘-~

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
    subst-pres {M = ` x} σ δ⊢σ↓γ ℰMγv =
        {!!}
        {- ℰ-⊑ {M = σ x} (δ⊢σ↓γ x) ℰMγv -}
    subst-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} σ δ⊢σ↓γ ℰMγv =
       {!!}
       {-
       (ℱ-≲ {Γ}{Δ}{γ}{δ}{ℰ N}{ℰ (⟪ exts σ ⟫ N)}
             λ {v} → subst-pres {γ = γ `, v}{δ = δ `, v}{M = N} (exts σ)
                          (subst-ext σ δ⊢σ↓γ)) {v}
        ℰMγv
        -}
    subst-pres {Γ}{Δ}{v}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆} σ δ⊢σ↓γ ℰMγv =
       {!!}
       {-
       (●-≲{Γ}{Δ}{γ}{δ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ (⟪ σ ⟫ L)}
            {D₂′ = ℰ (⟪ σ ⟫ M)}
            (λ ℰLγv → subst-pres {Γ}{Δ}{γ = γ}{δ}{L} σ δ⊢σ↓γ ℰLγv)
            (λ ℰMδv → subst-pres {Γ}{Δ}{γ = γ}{δ}{M} σ δ⊢σ↓γ ℰMδv))
        ℰMγv
        -}

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
