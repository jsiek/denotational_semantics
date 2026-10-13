{-

  The compiler, observed through the machines, in the graph model with
  errors: for a closed ISWIM program M, the ISWIM machine on M and the
  Clos5 machine on compile M (and the X86 machine on compile-x86 M) stop
  with an error together, stop with the same constants, stop with an
  answer together, and diverge together.

  Each follows from adequacy at both ends (Adequacy/GraphErr/ISWIM.agda,
  Clos5.agda, X86.agda) and from the compiler's correctness in the model
  (Correctness/GraphErr/CompilerCorrect.agda, Same).

-}

module proof.Adequacy.GraphErr.EndToEnd where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Framework.GraphModel.ErrorOps using (val∈)
open import Language.ISWIM using (AST)
open import Semantics.Observation using (Obs; o-const; o-error; Converges; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Semantics.CEK.Smallstep using (Machine)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Clos5 as Clos5ₘ
import Semantics.CEK.X86 as X86ₘ
open import Compiler.Pipeline using (compile; compile-x86)
open import Compiler.EncloseScope using (Closed)
open import proof.Correctness.GraphErr.CompilerCorrect using (Same; ⇔-trans; compile-same; compile-x86-same)
import proof.Adequacy.GraphErr.ISWIM as A
import proof.Adequacy.GraphErr.Clos5 as A5
import proof.Adequacy.GraphErr.X86 as Aₓ

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (¬_)

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym ⟨ f , g ⟩ = ⟨ g , f ⟩

{- a set is empty exactly when it has neither ω nor another element -}
private
  empty-Same : ∀ {D E} → Same D E → (∀ d → ¬ (d ∈ D)) → (∀ d → ¬ (d ∈ E))
  empty-Same ⟨ ⟨ _ , ωE→ ⟩ , ⟨ _ , ⟨ _ , vE→ ⟩ ⟩ ⟩ empty d d∈ =
    let d≢ : d ≢ ω
        d≢ = λ { refl → empty ω (ωE→ d∈) }
        ⟨ d' , ⟨ d'∈ , _ ⟩ ⟩ = vE→ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩
    in empty d' d'∈

  Same-sym : ∀ {D E} → Same D E → Same E D
  Same-sym ⟨ e , ⟨ c , v ⟩ ⟩ = ⟨ ⇔-sym e , ⟨ (λ k → ⇔-sym (c k)) , ⇔-sym v ⟩ ⟩

{- the four outcomes of two machines agree, when each is characterized by
   its denotation and the two denotations are the Same -}
record Agree (L₁ L₂ : Machine) : Set where
  field
    error : Terminates L₁ o-error ⇔ Terminates L₂ o-error
    const : ∀ {B} (k : base-rep B) → Terminates L₁ (o-const B k) ⇔ Terminates L₂ (o-const B k)
    converges : Converges (Terminates L₁) ⇔ Converges (Terminates L₂)
    diverges : Diverges L₁ ⇔ Diverges L₂

agree : ∀ {D E} {L₁ L₂ : Machine} → Same D E
  → (ω ∈ D) ⇔ Terminates L₁ o-error → (ω ∈ E) ⇔ Terminates L₂ o-error
  → (∀ {B} {k : base-rep B} → (dconst k ∈ D) ⇔ Terminates L₁ (o-const B k))
  → (∀ {B} {k : base-rep B} → (dconst k ∈ E) ⇔ Terminates L₂ (o-const B k))
  → val∈ D ⇔ Converges (Terminates L₁) → val∈ E ⇔ Converges (Terminates L₂)
  → Diverges L₁ ⇔ (∀ d → ¬ (d ∈ D)) → Diverges L₂ ⇔ (∀ d → ¬ (d ∈ E))
  → Agree L₁ L₂
agree S@(⟨ e , ⟨ c , v ⟩ ⟩) e₁ e₂ c₁ c₂ v₁ v₂ d₁ d₂ = record
  { error = ⇔-trans (⇔-sym e₁) (⇔-trans e e₂)
  ; const = λ k → ⇔-trans (⇔-sym c₁) (⇔-trans (c k) c₂)
  ; converges = ⇔-trans (⇔-sym v₁) (⇔-trans v v₂)
  ; diverges = ⇔-trans d₁ (⇔-trans ⟨ empty-Same S , empty-Same (Same-sym S) ⟩ (⇔-sym d₂))
  }

{- the ISWIM machine and the Clos5 machine on the compiled program -}
end-to-end : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (Clos5ₘ.sem (compile M))
end-to-end M c =
  agree (compile-same M c) (A.error-iff M c) (A5.clos5-error-iff M c) (A.const-iff M c) (A5.clos5-const-iff M c)
    (A.converges-iff M c) (A5.clos5-converges-iff M c) (A.diverges-iff M c) (A5.clos5-diverges-iff M c)

{- the ISWIM machine and the X86 machine on the compiled program -}
end-to-end-x86 : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (X86ₘ.sem (compile-x86 M))
end-to-end-x86 M c =
  agree (compile-x86-same M c) (A.error-iff M c) (Aₓ.x86-error-iff M c) (A.const-iff M c) (Aₓ.x86-const-iff M c)
    (A.converges-iff M c) (Aₓ.x86-converges-iff M c) (A.diverges-iff M c) (Aₓ.x86-diverges-iff M c)
