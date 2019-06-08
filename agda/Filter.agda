open import Structures
open import Variables
open import Primitives
import RenamePreserveReflect

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

module Filter
  (D : Domain)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (C : Consistent D V)
  (MB : ModelMod.LambdaModelBasics D V C _●_ ℱ)
  where
  
  open Domain D
  open DomainAux D
  open ValueOrdering V
  open OrderingAux D V
  open ModelMod.LambdaModelBasics MB
  open Consistent C
  open ConsistentAux D V C
  open WFDenotMod D V C

  module ForLambda where
  
    open import Lambda
    open LambdaDenot D V _●_ ℱ

    open RenamePreserveReflect.ForLambda D V _●_ ℱ C MB
       using (⊑-env; rename-pres)  

    ℰ-⊔ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-~ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → WFEnv γ → ℰ M γ u → ℰ M γ v → u ~ v
    ℰ-⊑ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v w : Value}
        → ℰ M γ v → w ⊑ v → ℰ M γ w

    ℰ-~ {Γ}{γ}{M = ` x}{u}{v} wfγ ℰMγu ℰMγv = ~-⊑ (~-refl (wfγ {x})) ℰMγu ℰMγv
    ℰ-~ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} wfγ ℰMγu ℰMγv =
       ℱ-~ {Γ}{ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-~ {Γ}{γ}{app ⦅ cons L (cons M nil) ⦆}{u}{v} wfγ ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-~ G H ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = ⊑-env {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = ⊑-env {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }

    ℰ-⊔ {M = ` x} ℰMγu ℰMγv = ⊑-conj-L ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} ℰMγu ℰMγv =
       ℱ-⊔ {Γ}{ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ = γ}{app ⦅ cons L (cons M nil) ⦆} ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ G H ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = ⊑-env {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = ⊑-env {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }


    ℰ-⊑ {M = ` x} ℰMγv w⊑v = ⊑-trans w⊑v ℰMγv
    ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} ℰMγv w⊑v =
      ℱ-⊑ G ℰMγv w⊑v
      where G : WFDenot (suc Γ) (ℰ N)
            G = record { ⊑-env = ⊑-env {M = N} ;
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} ;
                         ~-closed = ℰ-~ {M = N} }

    ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} ℰMγv w⊑v =
       ●-⊑ G ℰMγv w⊑v
       where G : WFDenot Γ (ℰ L)
             G = record { ⊑-env = ⊑-env {M = L} ;
                          ⊑-closed = ℰ-⊑ {M = L} ;
                          ⊔-closed = ℰ-⊔ {M = L} ;
                          ~-closed = ℰ-~ {M = L} }

    WF : ∀{Γ}{M : Term Γ} → WFDenot Γ (ℰ M)
    WF {Γ} {M} = record { ⊑-env = ⊑-env {M = M} ;
                          ⊑-closed = ℰ-⊑ {M = M} ;
                          ⊔-closed = ℰ-⊔ {M = M} ;
                          ~-closed = ℰ-~ {M = M} }

    subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
               → γ `⊢ σ ↓ γ₁
               → γ `⊢ σ ↓ γ₂
                 -------------------------
               → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
    subst-⊔ {σ = σ} γ₁-ok γ₂-ok x = ℰ-⊔ {M = σ x} (γ₁-ok x) (γ₂-ok x)

  module ForISWIM 
    (℘ : ∀{P : Prim} → rep P → Domain.Value D → Set)
    (℘-⊔ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → ℘ {P} D (u ⊔ v))
    (℘-⊑ : ∀{P : Prim} {D : rep P} {v w : Value}
          → ℘ {P} D v → w ⊑ v → ℘ {P} D w)
    (℘-~ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → u ~ v)
    where
  
    open import ISWIM
    open ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)

    open RenamePreserveReflect.ForISWIM D V _●_ ℱ C MB (λ {P} k v → ℘ {P} k v)
       using (⊑-env; rename-pres)  

    ℰ-⊔ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-~ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → WFEnv γ → ℰ M γ u → ℰ M γ v → u ~ v
    ℰ-⊑ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v w : Value}
        → ℰ M γ v → w ⊑ v → ℰ M γ w

    ℰ-~ {M = ` x} wfγ ℰMγu ℰMγv = ~-⊑ (~-refl (wfγ {x})) ℰMγu ℰMγv
    ℰ-~ {M = lit {P} k ⦅ nil ⦆} wfγ ℰMγu ℰMγv = ℘-~ ℰMγu ℰMγv
    ℰ-~ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} wfγ ℰMγu ℰMγv =
       ℱ-~ {Γ}{ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-~ {Γ}{γ}{app ⦅ cons L (cons M nil) ⦆} wfγ ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-~ G H ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = ⊑-env {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = ⊑-env {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }
    
    ℰ-⊔ {M = lit {P} k ⦅ nil ⦆} ℰMγu ℰMγv = ℘-⊔ ℰMγu ℰMγv
    ℰ-⊔ {M = ` x} ℰMγu ℰMγv = ⊑-conj-L ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} ℰMγu ℰMγv =
       ℱ-⊔ {Γ}{ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ = γ}{app ⦅ cons L (cons M nil) ⦆} ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ G H ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = ⊑-env {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = ⊑-env {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }


    ℰ-⊑ {M = lit {P} k ⦅ nil ⦆} ℰMγv w⊑v = ℘-⊑ ℰMγv w⊑v
    ℰ-⊑ {M = ` x} ℰMγv w⊑v = ⊑-trans w⊑v ℰMγv
    ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} ℰMγv w⊑v =
      ℱ-⊑ G ℰMγv w⊑v
      where G : WFDenot (suc Γ) (ℰ N)
            G = record { ⊑-env = ⊑-env {M = N} ;
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} ;
                         ~-closed = ℰ-~ {M = N} }

    ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} ℰMγv w⊑v =
       ●-⊑ G ℰMγv w⊑v
       where G : WFDenot Γ (ℰ L)
             G = record { ⊑-env = ⊑-env {M = L} ;
                          ⊑-closed = ℰ-⊑ {M = L} ;
                          ⊔-closed = ℰ-⊔ {M = L} ;
                          ~-closed = ℰ-~ {M = L} }

    WF : ∀{Γ}{M : Term Γ} → WFDenot Γ (ℰ M)
    WF {Γ} {M} = record { ⊑-env = ⊑-env {M = M} ;
                          ⊑-closed = ℰ-⊑ {M = M} ;
                          ⊔-closed = ℰ-⊔ {M = M} ;
                          ~-closed = ℰ-~ {M = M} }

    subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
               → γ `⊢ σ ↓ γ₁
               → γ `⊢ σ ↓ γ₂
                 -------------------------
               → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
    subst-⊔ {σ = σ} γ₁-ok γ₂-ok x = ℰ-⊔ {M = σ x} (γ₁-ok x) (γ₂-ok x)


