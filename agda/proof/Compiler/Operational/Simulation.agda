{-

  Forward simulations (proof/Framework/Simulation.agda) between the
  machines of this compiler's languages, which stop with its observations
  (Compiler/Observation.agda), and the end theorem they give (Equivalent,
  in Framework/Smallstep.agda). See the design note in
  Compiler/Operational/Smallstep.agda.

-}

module proof.Compiler.Operational.Simulation where

open import Compiler.Observation using (Obs)
open import Compiler.Operational.Smallstep using (Equivalent) public
open import proof.Framework.Simulation Obs public
