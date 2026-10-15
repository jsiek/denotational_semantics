{-

  The definitions of Framework/GraphModel/ErrorPrelude.agda with the
  lemmas of proof/Framework/GraphModel/Prelude.agda, of the operators
  shared by both graph models (OpsBase) and of the error monad, which
  the proofs about the graph model with errors open.  It only
  re-exports.

-}

module proof.Framework.GraphModel.ErrorPrelude where

open import Framework.GraphModel.ErrorPrelude public
open import proof.Framework.GraphModel.Prelude public
open import proof.Framework.GraphModel.OpsBase public
open import proof.Framework.GraphModel.ErrorMonad public
