open import Structures
open import Primitives
import ValueStructAux
import CurryApplyStruct
import RenamePreserveReflect

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
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
  (C : Consistent D V)
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
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
    open ASTMod using (Subst; ⟦_⟧)

    open RenamePreserveReflect.ForLambda D V C _●_ ℱ MB
       using (⊑-env; rename-pres)  

    ⊑-env′ : ∀{M}{γ δ : Env}{v} → WFEnv γ → WFEnv δ → wf v → γ `⊑ δ
           → (ℰ M) γ v → (ℰ M) δ v
    ⊑-env′ {M}{γ}{δ}{v} wfγ wfδ wfv γ⊑δ ℰMγv =
        ⊑-env {γ}{δ}{M}{v} wfv γ⊑δ ℰMγv 

    ℰ-⊔ : ∀ {γ : Env} {M : Term} {u v : Value}
        → WFEnv γ → wf u → wf v
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-~ : ∀ {γ : Env} {δ : Env} {M : Term} {u v : Value}
        → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
        → ℰ M γ u → ℰ M δ v → u ~ v
    ℰ-⊑ : ∀ {γ : Env} {M : Term} {v w : Value}
        → WFEnv γ → wf v → wf w 
        → w ⊑ v → ℰ M γ v → ℰ M γ w

    ℰ-~ {γ}{δ}{` x}{u}{v} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv =
        ~-⊑ (γ~δ x) ℰMγu ℰMδv
    ℰ-~ {γ}{δ}{lam ⦅ cons (bind (ast N)) nil ⦆}{u}{v} wfγ wfδ γ~δ wfu wfv
         ℰMγu ℰMδv =
       ℱ-~ {ℰ N}{γ}{δ}{u}{v} G wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv
       where G : WFDenot (ℰ N)
             G = record { ⊑-env = ⊑-env′ {M = N} ;
                          ⊑-closed = ℰ-⊑ {M = N} ;
                          ⊔-closed = ℰ-⊔ {M = N} ;
                          ~-closed = ℰ-~ {M = N} }

    ℰ-~ {γ}{δ}{app ⦅ cons (ast L) (cons (ast M) nil) ⦆}{u}{v} wfγ wfδ γ~δ
        wfu wfv
       ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-~ G H  wfγ wfδ γ~δ wfu wfv ℰMγu ℰMγv
      where G : WFDenot (ℰ L)
            G = record { ⊑-env = ⊑-env′ {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot (ℰ M)
            H = record { ⊑-env = ⊑-env′ {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }

    ℰ-⊔ {M = ` x} wfγ wfδ γ~δ ℰMγu ℰMδv = ⊑-conj-L ℰMγu ℰMδv
    ℰ-⊔ {γ}{lam ⦅ cons (bind (ast N)) nil ⦆}{u}{v} wfγ wfu wfv ℰMγu ℰMγv =
       ℱ-⊔ {ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-⊔ {γ}{app ⦅ cons (ast L) (cons (ast M) nil) ⦆} wfγ wfu wfv ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ G H wfγ wfu wfv ℰMγu ℰMγv
      where G : WFDenot (ℰ L)
            G = record { ⊑-env = ⊑-env′ {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot (ℰ M)
            H = record { ⊑-env = ⊑-env′ {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }


    ℰ-⊑ {M = ` x} wfγ wfv wfw  w⊑v ℰMγv = ⊑-trans w⊑v ℰMγv
    ℰ-⊑ {γ}{lam ⦅ cons (bind (ast N)) nil ⦆}{v}{w} wfγ wfv wfw w⊑v ℰMγv  =
      ℱ-⊑ G wfγ wfv wfw w⊑v ℰMγv
      where G : WFDenot (ℰ N)
            G = record { ⊑-env = ⊑-env′ {M = N} ;
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} ;
                         ~-closed = ℰ-~ {M = N} }

    ℰ-⊑ {γ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {v} {w} ℰMγv w⊑v =
       ●-⊑ G ℰMγv w⊑v
       where G : WFDenot (ℰ L)
             G = record { ⊑-env = ⊑-env′ {M = L} ;
                          ⊑-closed = ℰ-⊑ {M = L} ;
                          ⊔-closed = ℰ-⊔ {M = L} ;
                          ~-closed = ℰ-~ {M = L} }

    WFD : ∀ {M : Term} → WFDenot (ℰ M)
    WFD {M} = record { ⊑-env = ⊑-env′ {M = M} ;
                      ⊑-closed = ℰ-⊑ {M = M} ;
                      ⊔-closed = ℰ-⊔ {M = M} ;
                      ~-closed = ℰ-~ {M = M} }

    subst-⊔ : ∀{γ : Env}{γ₁ γ₂ : Env}{σ : Subst}
               → WFEnv γ → WFEnv γ₁ → WFEnv γ₂
               → γ `⊢ σ ↓ γ₁
               → γ `⊢ σ ↓ γ₂
                 -------------------------
               → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
    subst-⊔ {σ = σ} wfγ wfγ₁ wfγ₂ γ₁-ok γ₂-ok x =
        ℰ-⊔ {M = ⟦ σ ⟧ x} wfγ (wfγ₁ x) (wfγ₂ x) (γ₁-ok x) (γ₂-ok x)

  module ForISWIM 
    (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
    (℘-⊔ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → ℘ {P} D (u ⊔ v))
    (℘-⊑ : ∀{P : Prim} {D : rep P} {v w : Value}
          → wf w → ℘ {P} D v → w ⊑ v → ℘ {P} D w)
    (℘-~ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → u ~ v)
    where
  
    open import ISWIM
    open import ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)

    open RenamePreserveReflect.ForISWIM D V C _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
       using (⊑-env; rename-pres)
       
    ⊑-env′ : ∀{M}{γ δ : Env}{v} → WFEnv γ → WFEnv δ → wf v → γ `⊑ δ
           → (ℰ M) γ v → (ℰ M) δ v
    ⊑-env′ {M}{γ}{δ}{v} wfγ wfδ wfv γ⊑δ ℰMγv =
       ⊑-env {γ}{δ}{M}{v} wfv γ⊑δ ℰMγv 

    ℰ-⊔ : ∀ {γ : Env} {M : Term} {u v : Value}
        → WFEnv γ → wf u → wf v
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-~ : ∀ {γ : Env} {δ : Env} {M : Term} {u v : Value}
        → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v → ℰ M γ u → ℰ M δ v → u ~ v
    ℰ-⊑ : ∀ {γ : Env} {M : Term} {v w : Value}
        → WFEnv γ → wf v → wf w 
        → w ⊑ v → ℰ M γ v → ℰ M γ w

    ℰ-~ {M = ` x} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv = ~-⊑ (γ~δ x) ℰMγu ℰMδv
    ℰ-~ {M = $ P k} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv = ℘-~ ℰMγu ℰMδv
    ℰ-~ {γ}{δ}{lam ⦅ cons (bind (ast N)) nil ⦆}{u}{v} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv =
       ℱ-~ {ℰ N}{γ}{δ}{u}{v} G wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv
       where G : WFDenot (ℰ N)
             G = record { ⊑-env = ⊑-env′ {M = N} ;
                          ⊑-closed = ℰ-⊑ {M = N} ;
                          ⊔-closed = ℰ-⊔ {M = N} ;
                          ~-closed = ℰ-~ {M = N} }
             

    ℰ-~ {γ}{δ}{app ⦅ cons (ast L) (cons (ast M) nil) ⦆} wfγ wfδ γ~δ wfu wfv
        ℰMγu ℰMδv =
       ●-~  G H wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv
      where G : WFDenot (ℰ L)
            G = record { ⊑-env = ⊑-env′ {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot (ℰ M)
            H = record { ⊑-env = ⊑-env′ {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }
    
    ℰ-⊔ {M = $ P k} wfγ wfu wfv ℰMγu ℰMγv = ℘-⊔ ℰMγu ℰMγv
    ℰ-⊔ {M = ` x} wfγ wfu wfv ℰMγu ℰMγv = ⊑-conj-L ℰMγu ℰMγv
    ℰ-⊔ {γ}{lam ⦅ cons (bind (ast N)) nil ⦆}{u}{v} wfγ wfu wfv ℰMγu ℰMγv =
       ℱ-⊔ {ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-⊔ {γ}{app ⦅ cons (ast L) (cons (ast M) nil) ⦆} wfγ wfu wfv ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ G H wfγ wfu wfv ℰMγu ℰMγv
      where G : WFDenot (ℰ L)
            G = record { ⊑-env = ⊑-env′ {M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L} ;
                         ~-closed = ℰ-~ {M = L} }
            H : WFDenot (ℰ M)
            H = record { ⊑-env = ⊑-env′ {M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M} ;
                         ~-closed = ℰ-~ {M = M} }


    ℰ-⊑ {M = $ P k} wfγ wfv wfw w⊑v ℰMγv = ℘-⊑ wfw ℰMγv w⊑v
    ℰ-⊑ {M = ` x} wfγ wfv wfw w⊑v ℰMγv = ⊑-trans w⊑v ℰMγv
    ℰ-⊑ {γ}{ƛ N}{v}{w} wfγ wfv wfw w⊑v ℰMγv =
      ℱ-⊑ G wfγ wfv wfw w⊑v ℰMγv 
      where G : WFDenot (ℰ N)
            G = record { ⊑-env = ⊑-env′ {M = N} ;
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} ;
                         ~-closed = ℰ-~ {M = N} }

    ℰ-⊑ {γ} {L · M} {v} {w} wfγ wfv wfw
        w⊑v ℰMγv =
       ●-⊑ G wfγ wfv wfw w⊑v ℰMγv 
       where G : WFDenot (ℰ L)
             G = record { ⊑-env = ⊑-env′ {M = L} ;
                          ⊑-closed = ℰ-⊑ {M = L} ;
                          ⊔-closed = ℰ-⊔ {M = L} ;
                          ~-closed = ℰ-~ {M = L} }

    WFD : ∀{M : Term} → WFDenot (ℰ M)
    WFD {M} = record { ⊑-env = ⊑-env′ {M = M} ;
                      ⊑-closed = ℰ-⊑ {M = M} ;
                      ⊔-closed = ℰ-⊔ {M = M} ;
                      ~-closed = ℰ-~ {M = M} }

    subst-⊔ : ∀{γ : Env}{γ₁ γ₂ : Env}{σ : Subst}
               → WFEnv γ → WFEnv γ₁ → WFEnv γ₂
               → γ `⊢ σ ↓ γ₁
               → γ `⊢ σ ↓ γ₂
                 -------------------------
               → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
    subst-⊔ {σ = σ} wfγ wfγ₁ wfγ₂ γ₁-ok γ₂-ok x =
        ℰ-⊔ {M = ⟦ σ ⟧ x} wfγ (wfγ₁ x) (wfγ₂ x) (γ₁-ok x) (γ₂-ok x)


