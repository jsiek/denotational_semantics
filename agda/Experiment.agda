open import Structures
open import Lambda using (_·_; ƛ; Term; lam; app)
open Lambda.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule)
open Lambda.ASTMod
   using (Var; Z; S_; `_; _⦅_⦆; extensionality; Rename; Subst;
          ext; exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)

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

module Experiment where


record ModelCong
       (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
       : Set₁ where
  field
    ●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
         → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ


record ModelBasics
       (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
       : Set₁ where
  field
    Cong : ModelCong _●_
    ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
         → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v → (D₁ ● D₂) γ w
    ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
         → WFDenot Γ D₁ → WFDenot Γ D₂
         → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)

module Denot
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  where

  ℰ : ∀{Γ} → Term Γ → Denotation Γ
  ℰ {Γ} (` x) γ v = v ⊑ γ x
  ℰ {Γ} (lam ⦅ bind N nil ⦆) = ℱ (ℰ N)
  ℰ {Γ} (app ⦅ cons L (cons M nil) ⦆) = (ℰ L) ● (ℰ M)

  infix 3 _`⊢_↓_
  _`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
  _`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))

module RenamePreserveReflect
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (Cong : ModelCong _●_)
  where

  module Den = Denot _●_
  open Den
  open ModelCong Cong

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

module Filter
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (MB : ModelBasics _●_)
    where

  open ModelBasics MB

  module Den = Denot _●_
  open Den

  module RP = RenamePreserveReflect _●_ Cong
  open RP using (⊑-env; rename-pres)  

  ℰ-⊔ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
      → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
  ℰ-⊑ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v w : Value}
      → ℰ M γ v → w ⊑ v → ℰ M γ w

  ℰ-⊔ {M = ` x} ℰMγu ℰMγv = ⊑-conj-L ℰMγu ℰMγv
  ℰ-⊔ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} ℰMγu ℰMγv =
     ℱ-⊔ {Γ}{ℰ N}{γ}{u}{v} ℰMγu ℰMγv
  ℰ-⊔ {Γ}{γ = γ}{app ⦅ cons L (cons M nil) ⦆} ℰMγu ℰMγv =
     let a = ℰ-⊔ {γ = γ} {M = L} in
     let b = ℰ-⊔ {γ = γ} {M = M} in
     let c = ℰ-⊑ {γ = γ} {M = L} in
     ●-⊔ G H ℰMγu ℰMγv
    where G : WFDenot Γ (ℰ L)
          G = record { ⊑-env = ⊑-env{M = L} ;
                       ⊑-closed = ℰ-⊑ {M = L} ;
                       ⊔-closed = ℰ-⊔ {M = L}  }
          H : WFDenot Γ (ℰ M)
          H = record { ⊑-env = ⊑-env{M = M} ;
                       ⊑-closed = ℰ-⊑ {M = M} ;
                       ⊔-closed = ℰ-⊔ {M = M}  }


  ℰ-⊑ {M = ` x} ℰMγv w⊑v = ⊑-trans w⊑v ℰMγv
  ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} ℰMγv w⊑v =
    ℱ-⊑ G ℰMγv w⊑v
    where G : WFDenot (suc Γ) (ℰ N)
          G = record { ⊑-env = ⊑-env{M = N} ;
                       ⊑-closed = ℰ-⊑ {M = N} ;
                       ⊔-closed = ℰ-⊔ {M = N} }

  ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} ℰMγv w⊑v =
     ●-⊑ G ℰMγv w⊑v
     where G : WFDenot Γ (ℰ L)
           G = record { ⊑-env = ⊑-env{M = L} ;
                        ⊑-closed = ℰ-⊑ {M = L} ;
                        ⊔-closed = ℰ-⊔ {M = L} }

  WF : ∀{Γ}{M : Term Γ} → WFDenot Γ (ℰ M)
  WF {Γ} {M} = record { ⊑-env = ⊑-env {M = M} ;
                        ⊑-closed = ℰ-⊑ {M = M} ;
                        ⊔-closed = ℰ-⊔ {M = M} }

module SubstPres
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (MB : ModelBasics _●_)
  where

  open Denot _●_
  open ModelBasics MB
  open ModelCong Cong
  module RP = RenamePreserveReflect _●_ Cong
  open RP using (⊑-env; rename-pres)  
  open Filter _●_ MB using (ℰ-⊑; ℰ-⊔)

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


`⊥ : ∀ {Γ} → Env Γ
`⊥ x = ⊥

record ModelBot
       (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
       : Set₁ where
  field
    MB : ModelBasics _●_
    ●-⊥ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ}
         → (D₁ ● D₂) γ ⊥

record ModelExtra
       (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
       : Set₁ where
  field
    MBot : ModelBot _●_
    ●-≡ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {w : Value}
        → (D₁ ● D₂) γ w ≡ (w ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v))
    ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
          → ℱ D γ u
          → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ]
                      (D (γ `, v) w) × ((v ↦ w) ⊑ u))

