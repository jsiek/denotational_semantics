open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import CurryApplyStruct
import OrderingAux
open import Primitives
open import Structures
import ValueStructAux
import WFDenotMod

module Compositionality where

module DenotAux
  (D : ValueStruct) (V : ValueOrdering D) 
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
      → ValueStructAux.Denotation D Γ)
  (C : Consistent D V)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  where
  open ValueStruct D
  open ValueStructAux D
  open OrderingAux D V
  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry
  open import CurryApplyAux D V C _●_ ℱ MB

  open import LambdaDenot D V _●_ ℱ
  open import Lambda
  open ASTMod
  
  ƛ-⊥ : ∀{Γ}{N : Term (suc Γ)}{γ : Env Γ}
      → ℰ (ƛ N) γ ⊥
  ƛ-⊥ = ℱ-⊥

  compositionality : ∀{Γ Δ}{C : Ctx Γ Δ} {M N : Term Γ}
                → ℰ M ≃ ℰ N
                  ---------------------------
                → ℰ (plug C M) ≃ ℰ (plug C N)
  compositionality {C = CHole} M≃N = M≃N
  
  compositionality {C = COp lam (cbind {Γ}{Δ}{bs}{bs'} C′ nil refl)}{M}{N} M≃N =
     ℱ-cong (compositionality {C = C′} M≃N)

  compositionality {C = COp lam (tbind N Cs refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
  compositionality {C = COp lam (ccons C Ms ())} M≃N
  compositionality {C = COp lam (tcons N Cs ())} M≃N
  
  compositionality {C = COp app (cbind C′ Ms ())} M≃N
  compositionality {C = COp app (tbind L Cs ())} M≃N
  
  compositionality {C = COp app (ccons C′ (cons M nil) refl)} M≃N =
     ●-cong (compositionality {C = C′} M≃N)
            (λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩)
  compositionality {C = COp app (tcons L (ccons C′ nil refl) refl)} M≃N =
     ●-cong (λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩)
            (compositionality {C = C′} M≃N)
  compositionality {C = COp app (tcons L (cbind C′ Ms ()) refl)} M≃N
  compositionality {C = COp app (tcons L (tbind M Cs ()) refl)} M≃N
  compositionality {C = COp app (tcons L (tcons M Cs refl) refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
  

module ISWIMDenotAux
  (D : ValueStruct) (V : ValueOrdering D) 
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
       → ValueStructAux.Denotation D Γ)
  (C : Consistent D V)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
  where
  
  open ValueStruct D
  open ValueStructAux D
  open OrderingAux D V
  open import ISWIMDenot D V _●_ ℱ  (λ {P} k v → ℘ {P} k v)
  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry
  open import CurryApplyAux D V C _●_ ℱ MB
  
  open import ISWIM
  open ASTMod
  
  ƛ-⊥ : ∀{Γ}{N : Term (suc Γ)}{γ : Env Γ}
      → ℰ (ƛ N) γ ⊥
  ƛ-⊥ = ℱ-⊥

  compositionality : ∀{Γ Δ}{C : Ctx Γ Δ} {M N : Term Γ}
                → ℰ M ≃ ℰ N
                  ---------------------------
                → ℰ (plug C M) ≃ ℰ (plug C N)
  compositionality {C = CHole} M≃N = M≃N

  compositionality {C = COp (lit {P} k) (tbind N Cs ())} M≃N
  compositionality {C = COp (lit {P} k) (cbind C Ns ())} M≃N
  compositionality {C = COp (lit {P} k) (tcons C Ms ())} M≃N
  compositionality {C = COp (lit {P} k) (ccons M Cs ())} M≃N

  compositionality {C = COp lam (cbind {Γ}{Δ}{bs}{bs'} C′ nil refl)}{M}{N} M≃N =
     ℱ-cong (compositionality {C = C′} M≃N)

  compositionality {C = COp lam (tbind N Cs refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
  compositionality {C = COp lam (ccons C Ms ())} M≃N
  compositionality {C = COp lam (tcons N Cs ())} M≃N
  
  compositionality {C = COp app (cbind C′ Ms ())} M≃N
  compositionality {C = COp app (tbind L Cs ())} M≃N
  
  compositionality {C = COp app (ccons C′ (cons M nil) refl)} M≃N =
     ●-cong (compositionality {C = C′} M≃N)
            (λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩)
  compositionality {C = COp app (tcons L (ccons C′ nil refl) refl)} M≃N =
     ●-cong (λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩)
            (compositionality {C = C′} M≃N)
  compositionality {C = COp app (tcons L (cbind C′ Ms ()) refl)} M≃N
  compositionality {C = COp app (tcons L (tbind M Cs ()) refl)} M≃N
  compositionality {C = COp app (tcons L (tcons M Cs refl) refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
