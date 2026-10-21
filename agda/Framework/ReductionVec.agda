{-

  Reduction semantics (Framework/Reduction.agda) of terms whose tuples
  have a vector of operands: the operands are reduced left to right,
  given the reduction r of the first and rs of the rest.

-}

module Framework.ReductionVec (Obs : Set) (o-error : Obs) where

open import Framework.Reduction Obs o-error using (Red; val; step-in)

open import Data.Nat using (suc)
open import Data.Vec using (Vec; _∷_)

red-∷ : ∀ {A : Set} {n} (M : A) (Ms : Vec A n) → Red A → Red (Vec A n) → Red (Vec A (suc n))
red-∷ M Ms r rs = step-in (_∷ Ms) r (step-in (M ∷_) rs val)
