{-

  Forward simulations (../../Simulation.agda) between the machines of
  this compiler's languages, which stop with its observations
  (Observation.agda). See the design note in Smallstep.agda.

-}

module proof.Compiler.Operational.Simulation where

open import Compiler.Observation using (Obs)
open import proof.Framework.Simulation Obs public
