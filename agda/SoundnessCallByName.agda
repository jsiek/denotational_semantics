import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)

open import Values
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open Lambda.Reduction
  using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule; _—↠_; _—→⟨_⟩_; _□)
open import ValueBCD
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import ConsistentAux value_struct ordering consistent
open import ModelCallByName
open import LambdaDenot value_struct ordering _●_ ℱ
import Filter
open Filter.ForLambda value_struct ordering consistent _●_ ℱ model_curry_apply
import SubstitutionPreserve
open SubstitutionPreserve.ForLambda value_struct ordering _●_ ℱ consistent model_curry_apply
import RenamePreserveReflect
open RenamePreserveReflect.ForLambda value_struct ordering consistent _●_ ℱ model_curry_apply
   using (⊑-env)  
import SubstitutionReflect
open SubstitutionReflect.CallByName

module SoundnessCallByName where

reflect-beta : ∀{γ : Env}{M N}
    → ℰ (N [ M ]) γ ≲ ℰ ((ƛ N) · M) γ
reflect-beta {γ}{M}{N} {v} wfv d
    with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M}) (λ x → tt) tt 
... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ =
      inj₂ ⟨ v₂′ , ⟨ d₂′ , d₁′ ⟩ ⟩


reflect : ∀ {γ : Env} {M M′ N}
  →  M —→ M′  →   M′ ≡ N
    --------------------------------
  →  ℰ N γ ≲ ℰ M γ
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
reflect (ζ-rule {N}{N′} N—→N′) M′≡N {v} rewrite sym M′≡N =
    ℱ-≲ (λ {v′} wfv′ → reflect N—→N′ refl) {v}

preserve : ∀ {γ : Env} {M N}
  → M —→ N
  → ℰ M γ ≲ ℰ N γ
preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
              (preserve L—→L′)
              (λ x y → y)
preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} M—→M′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
              (λ x y → y)
              (preserve M—→M′)
preserve {γ}{app ⦅ cons (ast (lam ⦅ cons (bind (ast N)) nil ⦆)) (cons (ast M) nil) ⦆}
               (β-rule{N = N}{M = M}) _ ℰƛN·Mγw
    with ℰƛN·Mγw
... | inj₁ w⊑⊥ =
      ℰ-⊑ {M = ⟪ subst-zero M ⟫ N} (λ x → tt) tt tt w⊑⊥ (ℰ-⊥{M = ⟪ subst-zero M ⟫ N})
... | inj₂ ⟨ v' , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ =
      substitution{N = N}{M = M} {v'} (λ x → tt) tt tt ℰNγvw ℰMγv
preserve (ζ-rule {N}{N′} N—→N′) {v} = ℱ-≲ (λ wfv' → preserve N—→N′) {v}


reduce-equal : ∀ {M : Term} {N : Term}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {M}{N} r γ v wfγ wfv = ⟨ preserve r tt , reflect r refl tt ⟩

soundness : ∀ {M : Term} {N : Term}
  → M —↠ ƛ N
    -----------------
  → ℰ M ≃ ℰ (ƛ N)
soundness (M □) = ℰ M ≃⟨⟩ ℰ M ■
soundness {M}{N} (_—→⟨_⟩_ M {M = M′} M—→M′ M′—↠N) =
     ℰ M
   ≃⟨ reduce-equal M—→M′ ⟩ 
     ℰ M′
   ≃⟨ soundness M′—↠N ⟩ 
     ℰ (ƛ N)
   ■


