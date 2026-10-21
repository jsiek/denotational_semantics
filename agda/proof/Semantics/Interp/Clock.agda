{-

  The clocked semantics (Semantics/Interp/Clock.agda) with its lemmas
  (proof/Framework/Clocked.agda), at this compiler's observations.

-}

module proof.Semantics.Interp.Clock where

open import Semantics.Observation using (Obs; o-error)
open import Semantics.Interp.Clock public
open import proof.Framework.Clocked Obs o-error public
