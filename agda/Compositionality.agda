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
  (D : ValueStruct)
  (V : ValueOrdering D) 
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (C : Consistent D V)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  where
  open ValueStruct D
  open ValueStructAux D
  open OrderingAux D V
  open import ConsistentAux D V C
  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry
  open import CurryApplyAux D V C _●_ ℱ MB

  open import LambdaDenot D V _●_ ℱ
  open import Lambda
  open ASTMod
  
  ƛ-⊥ : ∀{N : Term}{γ : Env}
      → ℰ (ƛ N) γ ⊥
  ƛ-⊥ = ℱ-⊥

  compositionality : ∀{C : Ctx} {M N : Term}
                → ℰ M ≃ ℰ N
                  ---------------------------
                → ℰ (plug C M) ≃ ℰ (plug C N)
  compositionality {C = CHole} M≃N = M≃N
  compositionality {C = COp lam (tcons (bind (ast N)) Cs refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
  compositionality {C = COp lam (ccons (CBind (CAst C′)) nil refl)} M≃N =
     ℱ-cong (compositionality {C = C′} M≃N)
  compositionality {C = COp app (tcons (ast L) (tcons x Cs refl) refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
  compositionality {C = COp app (tcons (ast L) (ccons (CAst C′) nil refl) refl)} M≃N =
     ●-cong ≃-refl (compositionality {C = C′} M≃N)
  compositionality {C = COp app (ccons (CAst C′) (cons (ast M) nil) refl)} M≃N =
     ●-cong (compositionality {C = C′} M≃N) ≃-refl
  
module ISWIMDenotAux
  (D : ValueStruct) (V : ValueOrdering D) 
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (C : Consistent D V)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
  where
  
  open ValueStruct D
  open ValueStructAux D
  open OrderingAux D V
  open import ConsistentAux D V C
  open import ISWIMDenot D V _●_ ℱ  (λ {P} k v → ℘ {P} k v)
  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry
  open import CurryApplyAux D V C _●_ ℱ MB
  
  open import ISWIM
  open ASTMod
  
  ƛ-⊥ : ∀{N : Term}{γ : Env}
      → ℰ (ƛ N) γ ⊥
  ƛ-⊥ = ℱ-⊥

  compositionality : ∀{C : Ctx} {M N : Term}
                → ℰ M ≃ ℰ N
                  ---------------------------
                → ℰ (plug C M) ≃ ℰ (plug C N)
  compositionality {C = CHole} M≃N = M≃N
  compositionality {C = COp lam (tcons (bind (ast N)) Cs refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
  compositionality {C = COp lam (ccons (CBind (CAst C′)) nil refl)} M≃N =
     ℱ-cong (compositionality {C = C′} M≃N)
  compositionality {C = COp app (tcons (ast L) (tcons x Cs refl) refl)} M≃N =
     ⊥-elim (cargs-not-empty Cs)
  compositionality {C = COp app (tcons (ast L) (ccons (CAst C′) nil refl) refl)} M≃N =
     ●-cong ≃-refl (compositionality {C = C′} M≃N)
  compositionality {C = COp app (ccons (CAst C′) (cons (ast M) nil) refl)} M≃N =
     ●-cong (compositionality {C = C′} M≃N) ≃-refl
