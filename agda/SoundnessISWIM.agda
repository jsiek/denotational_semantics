open import Variables
open import Structures
open import ISWIM
open import ModelISWIM

open import Filter domain ordering _●_ ℱ model_basics
open import SubstitutionPreserve domain ordering _●_ ℱ model_basics
open import RenamePreserveReflect domain ordering _●_ ℱ model_basics
   using (⊑-env)  
import SubstitutionReflect
open SubstitutionReflect.ISWIM using (substitution-reflect)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_)


module SoundnessISWIM where


ℰ-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
    → TermValue M
    → ℰ M γ ⊥
ℰ-⊥ {M = lit {p} k ⦅ nil ⦆} V-lit = ?
ℰ-⊥ {M = (` x)} V-var = ⊑-⊥
ℰ-⊥ {Γ}{γ}{(lam ⦅ bind N nil ⦆)} V-ƛ = ℱ-⊥ {Γ}{ℰ N}{γ}


reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → TermValue M
    → ℰ (N [ M ]) γ v
    → ℰ ((ƛ N) · M) γ v
reflect-beta {Γ}{γ}{M}{N}{v} Mv d 
    with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M} Mv)
... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ =
      ⟨ v₂′ , ⟨ d₂′ , d₁′ ⟩ ⟩


reflect : ∀ {Γ} {γ : Env Γ} {M M′ N v}
  →  M —→ M′  →   M′ ≡ N  →  ℰ N γ v
    --------------------------------
  → ℰ M γ v    
reflect {γ = γ} (ξ₁-rule {L = L}{L′}{M} L—→L′) L′·M≡N
    rewrite sym L′·M≡N =
    ●-≲ {D₁ = ℰ L′}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (reflect L—→L′ refl) (≲-refl {d = ℰ M γ})
reflect {γ = γ} (ξ₂-rule {L = L}{M}{M′} v M—→M′) L·M′≡N
    rewrite sym L·M′≡N =
    ●-≲ {D₁ = ℰ L}{D₂ = ℰ M′}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (≲-refl {d = ℰ L γ}) (reflect M—→M′ refl)
reflect (β-rule {N = N}{M = M} Mv) M′≡N rewrite sym M′≡N =
    reflect-beta {M = M}{N} Mv


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


reduce-equal : ∀ {Γ} {M : Term Γ} {N : Term Γ}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {Γ}{M}{N} r γ v =
    ⟨ (λ m → preserve r m) , (λ n → reflect r refl n) ⟩


soundness : ∀{Γ} {M : Term Γ} {N : Term (suc Γ)}
  → M —↠ ƛ N
    -----------------
  → ℰ M ≃ ℰ (ƛ N)
soundness (_ □) γ v = ⟨ (λ x → x) , (λ x → x) ⟩
soundness {Γ} (L —→⟨ r ⟩ M—↠N) γ v =
   let ih = soundness M—↠N in
   let e = reduce-equal r in
   ≃-trans {Γ} e ih γ v
