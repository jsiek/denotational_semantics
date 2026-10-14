{-

  Two machines agree on every outcome (Agree: they stop with an error
  together, stop with the same constants, stop with an answer together,
  and diverge together) when each is characterized by its denotation in
  the graph model with errors and the two denotations are the Same: they
  err together, have the same constants, and have values together.
  Used by the end-to-end theorems of the graph model with errors
  (Adequacy/GraphErr/EndToEnd.agda, and those of the preserved untyped
  compiler).

-}

module proof.Adequacy.GraphErr.Agree where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω) renaming (const to dconst)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import Semantics.Observation using (Obs; o-const; o-error; Converges; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Semantics.CEK.Smallstep using (Machine)

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (¬_)

{- two sets err together, have the same constants, and have values together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = ((ω ∈ D) ⇔ (ω ∈ E)) × (∀ {B} (c : base-rep B) → ((dconst c ∈ D) ⇔ (dconst c ∈ E))) × (val∈ D ⇔ val∈ E)

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym ⟨ f , g ⟩ = ⟨ g , f ⟩

{- a set is empty exactly when it has neither ω nor another element -}
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
