import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_)


open import Variables
open import Structures
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open Lambda.Reduction
  using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule; _—↠_; _—→⟨_⟩_; _□)
open import ValueBCD
open DomainAux domain
open OrderingAux domain ordering
open import ModelCallByName
open LambdaDenot domain ordering _●_ ℱ
import Filter
open Filter.ForLambda domain ordering _●_ ℱ consistent model_basics
import SubstitutionPreserve
open SubstitutionPreserve.ForLambda domain ordering _●_ ℱ model_basics
import RenamePreserveReflect
open RenamePreserveReflect.ForLambda domain ordering _●_ ℱ model_basics
   using (⊑-env)  
import SubstitutionReflect
open SubstitutionReflect.CallByName



module SoundnessCallByName where

reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → ℰ (N [ M ]) γ v
    → ℰ ((ƛ N) · M) γ v
reflect-beta {Γ}{γ}{M}{N}{v} d 
    with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M})
... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ =
      inj₂ ⟨ v₂′ , ⟨ d₂′ , d₁′ ⟩ ⟩


reflect : ∀ {Γ} {γ : Env Γ} {M M′ N v}
  →  M —→ M′  →   M′ ≡ N  →  ℰ N γ v
    --------------------------------
  → ℰ M γ v    
reflect {γ = γ} (ξ₁-rule {L = L}{L′}{M} L—→L′) L′·M≡N
    rewrite sym L′·M≡N =
    ●-≲ {D₁ = ℰ L′}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (reflect L—→L′ refl) (≲-refl {d = ℰ M γ})
reflect {γ = γ} (ξ₂-rule {L = L}{M}{M′} M—→M′) L·M′≡N
    rewrite sym L·M′≡N =
    ●-≲ {D₁ = ℰ L}{D₂ = ℰ M′}{D₁′ = ℰ L}{D₂′ = ℰ M}
        (≲-refl {d = ℰ L γ}) (reflect M—→M′ refl)
reflect (β-rule {N = N}{M = M}) M′≡N rewrite sym M′≡N =
    reflect-beta {M = M}{N}
reflect {v = v} (ζ-rule {Γ}{N}{N′} N—→N′) M′≡N rewrite sym M′≡N =
    ℱ-≲ (reflect N—→N′ refl) {v}


preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → M —→ N
  → ℰ M γ v
    ----------
  → ℰ N γ v
preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
              (λ x → preserve L—→L′ x)
              (λ x → x)
preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} M—→M′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
              (λ x → x)
              (λ x → preserve M—→M′ x)
preserve {Γ}{γ}{app ⦅ cons (lam ⦅ bind N nil ⦆) (cons M nil) ⦆}{_}
               {v} (β-rule{N = N}{M = M}) ℰƛN·Mγw
    with ℰƛN·Mγw
... | inj₁ w⊑⊥ =
      ℰ-⊑ {M = ⟪ subst-zero M ⟫ N} (ℰ-⊥{M = ⟪ subst-zero M ⟫ N}) w⊑⊥
... | inj₂ ⟨ v' , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ = 
      substitution{N = N}{M = M} {v'} ℰNγvw ℰMγv
preserve {v = v} (ζ-rule {Γ}{N}{N′} N—→N′) = ℱ-≲ (preserve N—→N′) {v}


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
