module Structures where

open import Variables
open import Primitives

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool
open import Data.List
open import Function using (_∘_)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)

record Domain : Set₁ where
  infixr 7 _↦_
  infixl 5 _⊔_
  field
    Value : Set
    ⊥ : Value
    _↦_ : Value → Value → Value
    _⊔_ : (u : Value) → (v : Value) → {c : u ~ v} → Value

record ValueOrdering (D : Domain) : Set₁ where
  open Domain D
  infix 4 _⊑_
  field
    _⊑_ : Value → Value → Set

    ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

    ⊑-conj-L : ∀ {u v w}
        → v ⊑ u
        → w ⊑ u
          -----------
        → v ⊔ w ⊑ u

    ⊑-conj-R1 : ∀ {u v w}
       → u ⊑ v
         ------------------
       → u ⊑ v ⊔ w

    ⊑-conj-R2 : ∀ {u v w}
       → u ⊑ w
         -----------
       → u ⊑ v ⊔ w

    ⊑-trans : ∀ {u v w}
       → u ⊑ v
       → v ⊑ w
         -----
       → u ⊑ w

    ⊑-fun : ∀ {v w v′ w′}
         → v′ ⊑ v
         → w ⊑ w′
           -------------------
         → v ↦ w ⊑ v′ ↦ w′
         
    ⊑-refl : ∀ {v} → v ⊑ v

    ⊑-dist : ∀{v w w′}
           -----------------------------
         → v ↦ (w ⊔ w′) ⊑ v ↦ w ⊔ v ↦ w′


record Consistent (D : Domain) (V : ValueOrdering D) : Set₁ where
  open Domain D
  open ValueOrdering V
  infix 4 _~_
  field
    _~_ : Value → Value → Set
    ~-⊑ : ∀{u v u′ v′}  → u ~ v → u′ ⊑ u → v′ ⊑ v → u′ ~ v′
    ~-↦-cong : ∀{u v u′ v′} → u ~ u′ → v ~ v′ → (u ↦ v) ~ (u′ ↦ v′)
    
    ~-refl : ∀{v} → v ~ v
    
    ~-↦ : ∀{v w v′ w′} → (v ↦ w ~ v′ ↦ w′) → ((v ~ v′ × w ~ w′) ⊎ ¬ (v ~ v′))
    
    ~-⊔-cong : ∀{u v u′ v′}
             → (u ~ u′) → (u ~ v′)
             → (v ~ u′) → (v ~ v′)
             → {c1 : (u ~ v)} {c2 : (u′ ~ v′)}
             → ((u ⊔ v){c1}) ~ ((u′ ⊔ v′){c2})
             
    


{-

  The following caused problems with equality. -Jeremy

  record LambdaModel : Set₁ where
    field
      _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
      ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
-}


module DenotAux
  (D : Domain) (V : ValueOrdering D) 
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (MB : ModelMod.LambdaModelBasics D V _●_ ℱ)
  where
  open Domain D
  open DomainAux D
  open OrderingAux D V
  open ModelMod.LambdaModelBasics MB
  open ModelMod.ModelCurry model_curry
  open ℱ-●-cong D V _●_ ℱ MB

  open LambdaDenot D V _●_ ℱ
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
  (D : Domain) (V : ValueOrdering D) 
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (MB : ModelMod.LambdaModelBasics D V _●_ ℱ)
  (℘ : ∀{P : Prim} → rep P → Domain.Value D → Set)
  where
  
  open Domain D
  open DomainAux D
  open OrderingAux D V
  open ISWIMDenot D V _●_ ℱ  (λ {P} k v → ℘ {P} k v)
  open ModelMod.LambdaModelBasics MB
  open ModelMod.ModelCurry model_curry
  open ℱ-●-cong D V _●_ ℱ MB
  
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
