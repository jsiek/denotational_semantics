{-

  Forward simulations (proof/Framework/Simulation.agda) between the
  machines of this compiler's languages, which stop with its observations
  (Semantics/Observation.agda), and the end theorem they give (Equivalent,
  in Framework/Smallstep.agda). See the design note in
  Semantics/CEK/Smallstep.agda.

-}

module proof.Semantics.CEK.Simulation where

open import Semantics.Observation using (Obs)
open import Semantics.CEK.Smallstep using (Equivalent) public
open import proof.Framework.Simulation Obs public
