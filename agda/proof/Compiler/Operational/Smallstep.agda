{-

  The machines' transition systems (Compiler/Operational/Smallstep.agda)
  with the lemmas about their runs (proof/Framework/Smallstep.agda), at
  this compiler's observations.

-}

module proof.Compiler.Operational.Smallstep where

open import Compiler.Observation using (Obs)
open import Compiler.Operational.Smallstep public
open import proof.Framework.Smallstep Obs public
