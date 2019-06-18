open import Structures
open import Variables
open import Primitives
import ValueStructAux
import CurryApplyStruct
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
  open import OrderingAux D V
  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry
  open Consistent C
  open import ConsistentAux D V C
  open import WFDenotMod D V C

  module ForLambda where
  
    open import Lambda
    open import LambdaDenot D V _●_ ℱ

    open RenamePreserveReflect.ForLambda D V _●_ ℱ C MB
       using (⊑-env; rename-pres)  

    ⊑-env′ : ∀{Γ}{M}{γ δ}{v} → WFEnv γ → WFEnv δ → wf v → γ `⊑ δ → (ℰ M) γ v → (ℰ M) δ v
    ⊑-env′ {Γ}{M}{γ}{δ}{v} wfγ wfδ wfv γ⊑δ ℰMγv = ⊑-env {Γ}{γ}{δ}{M}{v} ℰMγv γ⊑δ

    ℰ-⊔ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → WFEnv γ → wf u → wf v
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-~ : ∀{Γ} {γ : Env Γ} {δ : Env Γ} {M : Term Γ} {u v : Value}
        → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v → ℰ M γ u → ℰ M δ v → u ~ v
    ℰ-⊑ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v w : Value}
        → WFEnv γ → wf v → wf w 
        → w ⊑ v → ℰ M γ v → ℰ M γ w

    ℰ-~ {Γ}{γ}{δ}{` x}{u}{v} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv =
        ~-⊑ (γ~δ {x}) ℰMγu ℰMδv
    ℰ-~ {Γ}{γ}{δ}{lam ⦅ bind N nil ⦆}{u}{v} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv =
       ℱ-~ {Γ}{ℰ N}{γ}{δ}{u}{v} G wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv
       where G : WFDenot (suc Γ) (ℰ N)
             G = record { ⊑-env = ⊑-env′ {M = N} ;
                          ⊑-closed = ℰ-⊑ {M = N} ;
                          ⊔-closed = ℰ-⊔ {M = N} ;
                          ~-closed = ℰ-~ {M = N} }

    ℰ-~ {Γ}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆}{u}{v} wfγ wfδ γ~δ wfu wfv
       ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-~ G H  wfγ wfδ γ~δ wfu wfv ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = ⊑-env′ {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = ⊑-env′ {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }

    ℰ-⊔ {M = ` x} wfγ wfδ γ~δ ℰMγu ℰMδv = ⊑-conj-L ℰMγu {!!}
    ℰ-⊔ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} wfγ wfu wfv ℰMγu ℰMγv =
       ℱ-⊔ {Γ}{ℰ N}{γ}{u}{v} ℰMγu {!!}
    ℰ-⊔ {Γ}{γ}{app ⦅ cons L (cons M nil) ⦆} wfγ wfu wfv ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ G H wfγ {!!} {!!} ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = {!!} {- ⊑-env {M = L} -};
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = {!!} {- ⊑-env {M = M} -} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }


    ℰ-⊑ {M = ` x} wfγ wfv wfw  w⊑v ℰMγv = ⊑-trans w⊑v ℰMγv
    ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} ℰMγv w⊑v =
      let xx = ℱ-⊑ {!!} {!!} {!!} {!!} {!!} {!!} in {!!}
      where G : WFDenot (suc Γ) (ℰ N)
            G = record { ⊑-env = {!!} {-⊑-env {M = N} -};
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} ;
                         ~-closed = ℰ-~ {M = N} }

    ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} ℰMγv w⊑v =
       ●-⊑ G ℰMγv w⊑v
       where G : WFDenot Γ (ℰ L)
             G = record { ⊑-env = {!!} {- ⊑-env {M = L} -} ;
                          ⊑-closed = ℰ-⊑ {M = L} ;
                          ⊔-closed = ℰ-⊔ {M = L} ;
                          ~-closed = ℰ-~ {M = L} }

    WF : ∀{Γ}{M : Term Γ} → WFDenot Γ (ℰ M)
    WF {Γ} {M} = record { ⊑-env = {!!} {- ⊑-env {M = M}  -} ;
                          ⊑-closed = ℰ-⊑ {M = M} ;
                          ⊔-closed = ℰ-⊔ {M = M} ;
                          ~-closed = ℰ-~ {M = M} }

    subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
               → WFEnv γ
               → γ `⊢ σ ↓ γ₁
               → γ `⊢ σ ↓ γ₂
                 -------------------------
               → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
    subst-⊔ {σ = σ} wfγ γ₁-ok γ₂-ok x =
        ℰ-⊔ {M = σ x} wfγ {!!} {!!} (γ₁-ok x) (γ₂-ok x)

  module ForISWIM 
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

    ℰ-⊔ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → WFEnv γ → wf u → wf v
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-~ : ∀{Γ} {γ : Env Γ} {δ : Env Γ} {M : Term Γ} {u v : Value}
        → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v → ℰ M γ u → ℰ M δ v → u ~ v
    ℰ-⊑ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v w : Value}
        → WFEnv γ → wf v → wf w 
        → w ⊑ v → ℰ M γ v → ℰ M γ w

    ℰ-~ {M = ` x} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv = ~-⊑ (γ~δ {x}) ℰMγu ℰMδv
    ℰ-~ {M = lit {P} k ⦅ nil ⦆} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv = ℘-~ ℰMγu ℰMδv
    ℰ-~ {Γ}{γ}{δ}{lam ⦅ bind N nil ⦆}{u}{v} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv =
       ℱ-~ {Γ}{ℰ N}{γ}{δ}{u}{v} G wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv
       where G : WFDenot (suc Γ) (ℰ N)
             G = record { ⊑-env = {!!} {- ⊑-env {M = N} -} ;
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} ;
                         ~-closed = ℰ-~ {M = N} }
             

    ℰ-~ {Γ}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-~  G H wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = {!!} {-⊑-env {M = L} -};
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = {!!} {-⊑-env {M = M} -};
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }
    
    ℰ-⊔ {M = lit {P} k ⦅ nil ⦆} wfγ wfu wfv ℰMγu ℰMγv = ℘-⊔ ℰMγu ℰMγv
    ℰ-⊔ {M = ` x} wfγ wfu wfv ℰMγu ℰMγv = ⊑-conj-L ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} wfγ wfu wfv ℰMγu ℰMγv =
       ℱ-⊔ {Γ}{ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ}{app ⦅ cons L (cons M nil) ⦆} wfγ wfu wfv ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ G H wfγ wfu wfv ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = {!!} {-⊑-env {M = L} -};
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = {!!} {-⊑-env {M = M} -};
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }


    ℰ-⊑ {M = lit {P} k ⦅ nil ⦆} wfγ wfv wfw w⊑v ℰMγv = ℘-⊑ ℰMγv w⊑v
    ℰ-⊑ {M = ` x} wfγ wfv wfw w⊑v ℰMγv = ⊑-trans w⊑v ℰMγv
    ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} wfγ wfv wfw w⊑v ℰMγv =
      ℱ-⊑ G {!!} {!!} {!!} w⊑v ℰMγv 
      where G : WFDenot (suc Γ) (ℰ N)
            G = record { ⊑-env = {!!} {-⊑-env {M = N} -};
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} ;
                         ~-closed = ℰ-~ {M = N} }

    ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} wfγ wfv wfw w⊑v ℰMγv =
       ●-⊑ G {!!} {!!} {!!} w⊑v ℰMγv 
       where G : WFDenot Γ (ℰ L)
             G = record { ⊑-env = {!!} {-⊑-env {M = L} -};
                          ⊑-closed = ℰ-⊑ {M = L} ;
                          ⊔-closed = ℰ-⊔ {M = L} ;
                          ~-closed = ℰ-~ {M = L} }

    WF : ∀{Γ}{M : Term Γ} → WFDenot Γ (ℰ M)
    WF {Γ} {M} = record { ⊑-env = {!!} {-⊑-env {M = M} -};
                          ⊑-closed = ℰ-⊑ {M = M} ;
                          ⊔-closed = ℰ-⊔ {M = M} ;
                          ~-closed = ℰ-~ {M = M} }

    subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
               → WFEnv γ
               → γ `⊢ σ ↓ γ₁
               → γ `⊢ σ ↓ γ₂
                 -------------------------
               → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
    subst-⊔ {σ = σ} wfγ γ₁-ok γ₂-ok x = ℰ-⊔ {M = σ x} wfγ {!!} {!!} (γ₁-ok x) (γ₂-ok x)


