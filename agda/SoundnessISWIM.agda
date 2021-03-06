open import Primitives
open import Values
open import ISWIM
open import ModelISWIM
open import ValueConst
open import CurryConst
open import ModelCurryConst
open import Consistency
open import ConsistentAux value_struct ordering consistent
open import ISWIMDenot value_struct ordering _●_ ℱ (λ {P} k v → ℘ {P} k v)
open import PrimConst
import Filter
open Filter.ForISWIM value_struct ordering consistent _●_ ℱ model_curry_apply
   (λ {P} k v → ℘ {P} k v)
   (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
   ℘-⊑
import SubstitutionPreserve
open SubstitutionPreserve.ISWIM value_struct ordering _●_ ℱ consistent model_curry_apply
   (λ {P} k v → ℘ {P} k v)
   (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
   ℘-⊑
   (λ {P} {k} {u} {v} → ℘-~ {P} {k} {u} {v})
import RenamePreserveReflect


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)

module SoundnessISWIM where

open RenamePreserveReflect.ForISWIM value_struct ordering consistent _●_ ℱ model_curry_apply
   (λ {P} k v → ℘ {P} k v) using (⊑-env; rename-pres; rename-pres-FV) public
import SubstitutionReflect
open SubstitutionReflect.ISWIM using (substitution-reflect)

ℰ-⊥ : ∀{γ : Env}{M : Term}
    → TermValue M
    → ℰ M γ ⊥
ℰ-⊥ {M = $ p k} V-lit = tt
ℰ-⊥ {M = (` x)} V-var = ⊑-⊥
ℰ-⊥ {γ}{ƛ N} V-ƛ = ℱ-⊥ {ℰ N}{γ}

reflect-beta : ∀{γ : Env}{M N}{v}
    → WFEnv γ → wf v
    → TermValue M
    → ℰ (N [ M ]) γ v
    → ℰ ((ƛ N) · M) γ v
reflect-beta {γ}{M}{N}{v} wfγ wfv Mv d 
    with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M} Mv) wfγ wfv
... | ⟨ v₂′ , ⟨ wfv₂ , ⟨ d₁′ , d₂′ ⟩ ⟩ ⟩ =
      ⟨ v₂′ , ⟨ wfv₂ , ⟨ d₂′ , d₁′ ⟩ ⟩ ⟩ 

reflect : ∀ {γ : Env} {M M′ N}
  →  WFEnv γ
  →  M —→ M′  →   M′ ≡ N
    --------------------
    →  ℰ N γ ≲ ℰ M γ
reflect {γ = γ} wfγ (ξ₁-rule {L = L}{L′}{M} L—→L′) L′·M≡N
    rewrite sym L′·M≡N =
    ●-≲ {D₁ = ℰ L′}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (reflect wfγ L—→L′ refl) (≲-refl {d = ℰ M γ})
reflect {γ = γ} wfγ (ξ₂-rule {L = L}{M}{M′} v M—→M′) L·M′≡N
    rewrite sym L·M′≡N =
    ●-≲ {D₁ = ℰ L}{D₂ = ℰ M′}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (≲-refl {d = ℰ L γ}) (reflect wfγ M—→M′ refl)
reflect wfγ (β-rule {N = N}{M = M} Mv) M′≡N rewrite sym M′≡N =
    λ wfv → reflect-beta {M = M}{N} wfγ wfv Mv
reflect wfγ (δ-rule {B}{P}{f}{k}) M′≡N {v} wfv ℘fkv
   rewrite sym M′≡N = 
    ⟨ const {B} k , ⟨ wf-const , ⟨ ⟨ k , ⟨ ⊑-const , ℘fkv ⟩ ⟩ , ℘kk ⟩ ⟩ ⟩
   where
   ℘kk : ℘ k (const {B} k)
   ℘kk
       with base-eq? B B
   ... | no neq = ⊥-elim (neq refl)      
   ... | yes eq rewrite eq = refl

   G : ∀ {k₁} → const k ⊑ const k₁ → ℘ {P} (f k₁) v
   G ⊑-const = ℘fkv

preserve : ∀ {γ : Env} {M N}
  → M —→ N  →  WFEnv γ
    ------------------
  → ℰ M γ ≲ ℰ N γ
preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) wfγ =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
              (preserve L—→L′ wfγ)
              (λ wf x → x)
preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} v M—→M′) wfγ =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
              (λ wf x → x)
              (preserve M—→M′ wfγ)
preserve {γ}{app ⦅ cons (ast (lam ⦅ cons (bind (ast N)) nil ⦆)) (cons (ast M) nil) ⦆}{_}
                (β-rule{N = N}{M = M} Mv) wfγ wfv ℰƛN·Mγw
    with ℰƛN·Mγw
... | ⟨ v' , ⟨ wfv' , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ ⟩ =
      substitution {N = N}{ M} {v'} wfγ wfv wfv' ℰNγvw ℰMγv 
preserve {γ} (δ-rule {B} {P} {f} {k}) wfγ {v} wfv
   ⟨ u , ⟨ wfu , ⟨ ⟨ k′ , ⟨ k′⊑u , ℘fk′v ⟩ ⟩ , ℘ku ⟩ ⟩ ⟩
    with ⊑-trans k′⊑u (BelowConstk→⊑k {B}{k}{u} (℘k→BelowConstk {B}{k}{u} ℘ku))
... | ⊑-const = ℘fk′v   
    
reduce-equal : ∀ {M : Term} {N : Term}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {M}{N} r γ v wfγ wfv =
    ⟨ preserve r wfγ wfv , reflect wfγ r refl wfv ⟩


soundness : ∀ {M : Term} {N : Term}
  → TermValue N
  → M —↠ N
    -----------------
  → ℰ M ≃ ℰ N
soundness Mv (M □) = ℰ M ≃⟨⟩ ℰ M ■
soundness {M}{N} Nv (_—→⟨_⟩_ M {M = M′} M—→M′ M′—↠N) =
     ℰ M
   ≃⟨ reduce-equal M—→M′ ⟩ 
     ℰ M′
   ≃⟨ soundness Nv M′—↠N ⟩ 
     ℰ N
   ■
