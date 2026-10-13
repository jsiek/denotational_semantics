{-

  The machines' transition systems (Semantics/CEK/Smallstep.agda)
  with the lemmas about their runs (proof/Framework/Smallstep.agda), at
  this compiler's observations.

-}

module proof.Semantics.CEK.Smallstep where

open import Semantics.Observation using (Obs)
open import Semantics.CEK.Smallstep public
open import proof.Framework.Smallstep Obs public
