{-

  The denotational: Scott domains column, for the ISWIMμ compiler
  (agda/Mu/). It needs TypeTopology besides the standard library, so it
  is not part of All.agda; check it with

    make check-scott

  which fetches TypeTopology (scott/fetch-typetopology.sh) and runs
  scott/check.sh on this file. See agda/Framework/Scott/.

  This file imports the theorem file, which reaches the audit surface of
  the column and its end theorems, and every module of proof/ that
  belongs to it.

-}

module AllScott where

{- the theorem statements -}
import Mu.Theorems.Scott

{- the language-independent lemmas: dcpos, the solution of the domain
   equation, the domain of values and its operators, the combinators for
   meanings, the stages of the bilimit and calls of approximated closures -}
import proof.Framework.Scott.Sum
import proof.Framework.Scott.Lift
import proof.Framework.Scott.Solve
import proof.Framework.Scott.Domain
import proof.Framework.Scott.Ops
import proof.Framework.Scott.Values
import proof.Framework.Scott.Semantics
import proof.Framework.Scott.Stages
import proof.Framework.Scott.StageCall

{- lemmas shared by the passes -}
import Mu.proof.Semantics.Scott.OptimizeLemmas
import Mu.proof.Semantics.Scott.BackEndLemmas

{- the passes, and the whole compiler -}
import Mu.proof.Correctness.Scott.SimplifyCorrect
import Mu.proof.Correctness.Scott.EncloseCorrect
import Mu.proof.Correctness.Scott.OptimizeCorrect
import Mu.proof.Correctness.Scott.ConcretizeCorrect
import Mu.proof.Correctness.Scott.DelayPreserve
import Mu.proof.Correctness.Scott.DelayPreserveTerms
import Mu.proof.Correctness.Scott.DelayReflect
import Mu.proof.Correctness.Scott.DelayReflectOps
import Mu.proof.Correctness.Scott.DelayReflectTerms
import Mu.proof.Correctness.Scott.DelayCorrect
import Mu.proof.Correctness.Scott.GlobalizeCorrect
import Mu.proof.Correctness.Scott.RCOCorrect
import Mu.proof.Correctness.Scott.LiftLocalsCorrect
import Mu.proof.Correctness.Scott.ExplicateCorrect
import Mu.proof.Correctness.Scott.SelectCorrect
import Mu.proof.Correctness.Scott.CompilerCorrect
