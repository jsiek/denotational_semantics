{-

  Reduction semantics (Framework/Reduction.agda) of terms whose tuples
  have a heterogeneous vector of operands (All, FPC/Framework/AllUtil.agda),
  as Framework/ReductionVec.agda for vectors: the operands are reduced
  left to right, given the reduction r of the first and rs of the rest
  (red-∷). The lemmas about it are in FPC/proof/Framework/ReductionAll.agda.

-}

module FPC.Framework.ReductionAll (Obs : Set) (o-error : Obs) where

open import Framework.Reduction Obs o-error using (Red; val; step-in)
open import FPC.Framework.AllUtil using (All; _∷_)

open import Data.List using (_∷_)

red-∷ : ∀ {X : Set} {P : X → Set} {A Δ} (M : P A) (Ms : All P Δ) → Red (P A) → Red (All P Δ) → Red (All P (A ∷ Δ))
red-∷ M Ms r rs = step-in (_∷ Ms) r (step-in (M ∷_) rs val)
