{-

  The clocked semantics (Compiler/Functional/Clock.agda) with its lemmas
  (proof/Framework/Clocked.agda), at this compiler's observations.

-}

module proof.Compiler.Functional.Clock where

open import Compiler.Observation using (Obs; o-wrong)
open import Compiler.Functional.Clock public
open import proof.Framework.Clocked Obs o-wrong public
