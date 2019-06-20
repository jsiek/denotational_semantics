open import Variables
open import Primitives
open import Structures
open import ISWIM
open import ModelISWIM
open import ValueConst
open import CurryConst
open import ModelCurryConst
open import ValueStructAux value_struct
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
import RenamePreserveReflect
open RenamePreserveReflect.ForISWIM value_struct ordering consistent _●_ ℱ model_curry_apply
   (λ {P} k v → ℘ {P} k v) using (⊑-env)  
import SubstitutionReflect
open SubstitutionReflect.ISWIM using (substitution-reflect)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)


module SoundnessISWIM where


ℰ-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
    → TermValue M
    → ℰ M γ ⊥
ℰ-⊥ {M = lit {p} k ⦅ nil ⦆} V-lit = tt
ℰ-⊥ {M = (` x)} V-var = ⊑-⊥
ℰ-⊥ {Γ}{γ}{(lam ⦅ bind N nil ⦆)} V-ƛ = ℱ-⊥ {Γ}{ℰ N}{γ}


reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → TermValue M
    → ℰ (N [ M ]) γ v
    → ℰ ((ƛ N) · M) γ v
reflect-beta {Γ}{γ}{M}{N}{v} Mv d 
    with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M} Mv) ? ?
... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ =
      ⟨ v₂′ , ⟨ ? , ⟨ d₂′ , d₁′ ⟩ ⟩ ⟩ 


reflect : ∀ {Γ} {γ : Env Γ} {M M′ N}
  →  M —→ M′  →   M′ ≡ N
    --------------------
    →  ℰ N γ ≲ ℰ M γ
reflect {γ = γ} (ξ₁-rule {L = L}{L′}{M} L—→L′) L′·M≡N
    rewrite sym L′·M≡N =
    ●-≲ {D₁ = ℰ L′}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (reflect L—→L′ refl) (≲-refl {d = ℰ M γ})
reflect {γ = γ} (ξ₂-rule {L = L}{M}{M′} v M—→M′) L·M′≡N
    rewrite sym L·M′≡N =
    ●-≲ {D₁ = ℰ L}{D₂ = ℰ M′}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (≲-refl {d = ℰ L γ}) (reflect M—→M′ refl)
reflect (β-rule {N = N}{M = M} Mv) M′≡N rewrite sym M′≡N =
    λ wfv → reflect-beta {M = M}{N} Mv
reflect {v = v}(δ-rule {Γ}{B}{P}{f}{k}) M′≡N ℘fkv rewrite sym M′≡N =
   ⟨ const {B} k , ⟨ {!!} , ℘kk ⟩ ⟩
   where
   ℘kk : ℘ k (const {B} k)
   ℘kk
       with base-eq? B B
   ... | no neq = ⊥-elim (neq refl)      
   ... | yes eq rewrite eq = refl

   G : ∀ {k₁} → const k ⊑ const k₁ → ℘ {P} (f k₁) v
   G ⊑-const = ℘fkv
{-
   G {k₁} (⊑-trans{v = v} k⊑k₁ k⊑k₂)
        with base-eq? B B | BelowConst-⊑ (⊑k→BelowConstk k⊑k₂) k⊑k₁
   ... | yes eq | b rewrite eq | b = ℘fkv
   ... | no neq | ()
-}


preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → M —→ N
  → ℰ M γ v
    ----------
  → ℰ N γ v
preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
              (λ x → preserve L—→L′ x)
              (λ x → x)
preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} v M—→M′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
              (λ x → x)
              (λ x → preserve M—→M′ x)
preserve {Γ}{γ}{app ⦅ cons (lam ⦅ bind N nil ⦆) (cons M nil) ⦆}{_}
               {v} (β-rule{N = N}{M = M} Mv) ℰƛN·Mγw
    with ℰƛN·Mγw
... | ⟨ v' , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ = 
      substitution{N = N}{M = M} {v'} ℰNγvw ℰMγv
preserve {Γ} {γ} {v = v} (δ-rule {Γ} {B} {P} {f} {k})
   ⟨ u , ⟨ ∀k,u⊑k→℘fkv , ℘ku ⟩ ⟩ = G
    where
    G : ℘ {P} (f k) v
    G =
     let bku = (℘k→BelowConstk {B}{k}{u} ℘ku) in
     {- ∀k,u⊑k→℘fkv {k} (BelowConstk→⊑k bku) -}
     {!!}
    

reduce-equal : ∀ {Γ} {M : Term Γ} {N : Term Γ}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {Γ}{M}{N} r γ v =
    ⟨ (λ m → preserve r m) , (λ n → reflect r refl n) ⟩


soundness : ∀{Γ} {M : Term Γ} {N : Term Γ}
  → TermValue N
  → M —↠ N
    -----------------
  → ℰ M ≃ ℰ N
soundness Nv (_ □) γ v = ⟨ (λ x → x) , (λ x → x) ⟩
soundness {Γ} Nv (L —→⟨ r ⟩ M—↠N) γ v =
   let ih = soundness Nv M—↠N in
   let e = reduce-equal r in
   ≃-trans {Γ} e ih γ v
