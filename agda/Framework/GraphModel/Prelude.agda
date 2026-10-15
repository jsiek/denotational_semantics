{-

  The definitions that every semantics in the graph model opens: sets
  as predicates, DOp signatures, the domain of values, environments, and
  the two operators that the graph model and the graph model with errors
  share most (application ⋆ and the constants ℬ).  It only re-exports,
  so it has no lines of its own (papers/PLDI-2027/loc.py looks through
  it to the modules it re-exports).  The lemmas about them are opened
  together by proof/Framework/GraphModel/Prelude.agda; the graph model
  with errors adds its error monad (ErrorPrelude.agda).

-}

module Framework.GraphModel.Prelude where

open import Framework.GraphModel.SetsAsPredicates public
open import Framework.GraphModel.DOpSig public
open import Framework.GraphModel.Domain public
open import Framework.GraphModel.Ops public using (⋆)
open import Framework.GraphModel.OpsBase public using (ℬ)
open import Framework.GraphModel.Env public using (Env)
