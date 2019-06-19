open import Variables
open import Structures
open import Lambda
open import LambdaCallByValue
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open import ValueBCD
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import ConsistentAux value_struct ordering consistent
open import ModelCallByValue value_struct ordering consistent ℱ model_curry
open import LambdaDenot value_struct ordering _●_ ℱ
open import Filter value_struct ordering consistent _●_ ℱ model_curry_apply
import SubstitutionPreserve
open SubstitutionPreserve.ForLambda value_struct ordering _●_ ℱ consistent model_curry_apply
import RenamePreserveReflect
open RenamePreserveReflect.ForLambda value_struct ordering consistent _●_ ℱ model_curry_apply
   using (⊑-env)  
import SubstitutionReflect
open SubstitutionReflect.CallByValue

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)


module SoundnessCallByValue where


ℰ-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
    → TermValue M
    → ℰ M γ ⊥
ℰ-⊥ {M = (` x)} V-var = ⊑-⊥
ℰ-⊥ {Γ}{γ}{(lam ⦅ bind N nil ⦆)} V-ƛ = ℱ-⊥ {Γ}{ℰ N}{γ}


reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → TermValue M
    → ℰ (N [ M ]) γ v
    → ℰ ((ƛ N) · M) γ v
reflect-beta {Γ}{γ}{M}{N}{v} Mv d 
    with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M} Mv) (λ {x} → tt) tt
... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ =
      ⟨ v₂′ , ⟨ tt , ⟨ d₂′ , d₁′ ⟩ ⟩ ⟩


reflect : ∀ {Γ} {γ : Env Γ} {M M′ N}
  →  M —→ M′  →   M′ ≡ N
    ---------------------
    → ℰ N γ ≲ ℰ M γ
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


preserve : ∀ {Γ} {γ : Env Γ} {M N}
  → M —→ N
    -------------
  → ℰ M γ ≲ ℰ N γ
preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
              (preserve L—→L′)
              (λ wf x → x)
preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} v M—→M′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
              (λ wf x → x)
              (preserve M—→M′)
preserve {Γ}{γ}{app ⦅ cons (lam ⦅ bind N nil ⦆) (cons M nil) ⦆}{_}
               (β-rule{N = N}{M = M} Mv) _ ℰƛN·Mγw
    with ℰƛN·Mγw
... | ⟨ v' , ⟨ wfv' , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ ⟩ = 
      substitution{N = N}{M = M} {v'} (λ {x} → tt) tt tt ℰNγvw ℰMγv


reduce-equal : ∀ {Γ} {M : Term Γ} {N : Term Γ}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {Γ}{M}{N} r γ v wfv =
    ⟨ preserve r tt , reflect r refl tt ⟩


soundness : ∀{Γ} {M : Term Γ} {N : Term (suc Γ)}
  → M —↠ ƛ N
    -----------------
  → ℰ M ≃ ℰ (ƛ N)
soundness (_ □) γ v wfv = ⟨ (λ x → x) , (λ x → x) ⟩
soundness {Γ} (L —→⟨ r ⟩ M—↠N) γ v =
   let ih = soundness M—↠N in
   let e = reduce-equal r in
   ≃-trans {Γ} e ih γ v
