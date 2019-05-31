open import Structures
open import Variables
open import Lambda using (_·_; ƛ; Term; lam; app)
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
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
  (LM : DomainAux.LambdaModel D)
  (MV : OrderingAux.LambdaModelBasics D V LM)
  where
  
  open Domain D
  open DomainAux D
  open ValueOrdering V
  open OrderingAux D V
  open LambdaDenot D V LM
  open LambdaModelBasics MV

  open RenamePreserveReflect D V LM MV  using (⊑-env; rename-pres)  

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
          G = record { ⊑-env = ⊑-env {M = L} ;
                       ⊑-closed = ℰ-⊑ {M = L} ;
                       ⊔-closed = ℰ-⊔ {M = L}  }
          H : WFDenot Γ (ℰ M)
          H = record { ⊑-env = ⊑-env {M = M} ;
                       ⊑-closed = ℰ-⊑ {M = M} ;
                       ⊔-closed = ℰ-⊔ {M = M}  }


  ℰ-⊑ {M = ` x} ℰMγv w⊑v = ⊑-trans w⊑v ℰMγv
  ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} ℰMγv w⊑v =
    ℱ-⊑ G ℰMγv w⊑v
    where G : WFDenot (suc Γ) (ℰ N)
          G = record { ⊑-env = ⊑-env {M = N} ;
                       ⊑-closed = ℰ-⊑ {M = N} ;
                       ⊔-closed = ℰ-⊔ {M = N} }

  ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} ℰMγv w⊑v =
     ●-⊑ G ℰMγv w⊑v
     where G : WFDenot Γ (ℰ L)
           G = record { ⊑-env = ⊑-env {M = L} ;
                        ⊑-closed = ℰ-⊑ {M = L} ;
                        ⊔-closed = ℰ-⊔ {M = L} }

  WF : ∀{Γ}{M : Term Γ} → WFDenot Γ (ℰ M)
  WF {Γ} {M} = record { ⊑-env = ⊑-env {M = M} ;
                        ⊑-closed = ℰ-⊑ {M = M} ;
                        ⊔-closed = ℰ-⊔ {M = M} }

