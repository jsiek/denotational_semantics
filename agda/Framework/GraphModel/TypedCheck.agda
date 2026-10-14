{-

  The check of the error monad (checked, Framework/GraphModel/ErrorMonad.agda)
  with the kinds of the values seen through a map φ on kinds: A, and ω
  when X has a value whose kind, through φ, is not k. With φ the
  identity it is checked; a φ that maps pairs to functions lets a
  language whose closures are pairs check them as functions.

-}

module Framework.GraphModel.TypedCheck where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.ErrorMonad using (Kind; kind)

open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

checkedᵠ : (Kind → Kind) → Kind → 𝒫 Value → 𝒫 Value → 𝒫 Value
checkedᵠ φ k X A w = (w ≡ ω × Σ[ d ∈ Value ] d ∈ X × φ (kind d) ≢ k) ⊎ w ∈ A
