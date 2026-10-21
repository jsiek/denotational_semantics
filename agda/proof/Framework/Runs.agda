{-

  Runs s ↠ t of a machine given by its step function, from any state (not
  only the start state of a Machine), and their determinism: used by the
  adequacy proofs, whose logical relations speak of runs from any state.

-}

module proof.Framework.Runs {Obs : Set} where

open import Framework.Smallstep Obs

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

module Runs {S : Set} (step : S → Next S) where

  infixr 5 _∷↠_
  infix 4 _↠_
  data _↠_ : S → S → Set where
    done : ∀ {s} → s ↠ s
    _∷↠_ : ∀ {s s' s''} → step s ≡ next s' → s' ↠ s'' → s ↠ s''

  infixr 5 _++↠_
  _++↠_ : ∀ {s s' s''} → s ↠ s' → s' ↠ s'' → s ↠ s''
  done ++↠ τ = τ
  (st ∷↠ σ) ++↠ τ = st ∷↠ (σ ++↠ τ)

  {- a run in the machine with any start -}
  ↠→star : ∀ {s₀ s t} → s ↠ t → Star (machine S step s₀) s t
  ↠→star done = ε
  ↠→star (st ∷↠ σ) = st ◅ ↠→star σ

  star→↠ : ∀ {s₀ s t} → Star (machine S step s₀) s t → s ↠ t
  star→↠ ε = done
  star→↠ (st ◅ σ) = st ∷↠ star→↠ σ

  private
    next-inj : ∀ {a b : S} → next a ≡ next b → a ≡ b
    next-inj refl = refl

  {- two runs to final states end in the same state -}
  ↠-final-det : ∀ {s t₁ t₂ o₁ o₂} → s ↠ t₁ → s ↠ t₂
    → step t₁ ≡ stop o₁ → step t₂ ≡ stop o₂ → t₁ ≡ t₂
  ↠-final-det done done f₁ f₂ = refl
  ↠-final-det done (st ∷↠ σ) f₁ f₂ with trans (sym f₁) st
  ... | ()
  ↠-final-det (st ∷↠ σ) done f₁ f₂ with trans (sym f₂) st
  ... | ()
  ↠-final-det (st₁ ∷↠ σ₁) (st₂ ∷↠ σ₂) f₁ f₂ with next-inj (trans (sym st₁) st₂)
  ... | refl = ↠-final-det σ₁ σ₂ f₁ f₂
