{-

  A guard in the graph model: D, provided that D has an element that P
  accepts, and ∅ otherwise. It is the meaning of a project in a graph
  model without errors: a failed project means ∅, as an error does.

-}

module Framework.GraphModel.TypedGuard where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain

open import Data.Product using (_×_; Σ-syntax)

guardᵖ : (Value → Set) → 𝒫 Value → 𝒫 Value
guardᵖ P D w = (Σ[ d ∈ Value ] d ∈ D × P d) × w ∈ D
