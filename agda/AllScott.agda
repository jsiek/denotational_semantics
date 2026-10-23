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
import Mu.Theorems.ScottDomains

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
import Mu.proof.Semantics.ScottDomains.OptimizeLemmas
import Mu.proof.Semantics.ScottDomains.BackEndLemmas

{- the passes, and the whole compiler -}
import Mu.proof.Correctness.ScottDomains.SimplifyCorrect
import Mu.proof.Correctness.ScottDomains.EncloseCorrect
import Mu.proof.Correctness.ScottDomains.OptimizeCorrect
import Mu.proof.Correctness.ScottDomains.ConcretizeCorrect
import Mu.proof.Correctness.ScottDomains.DelayRel
import Mu.proof.Correctness.ScottDomains.DelayPreserve
import Mu.proof.Correctness.ScottDomains.DelayReflect
import Mu.proof.Correctness.ScottDomains.DelayTerms
import Mu.proof.Correctness.ScottDomains.DelayCorrect
import Mu.proof.Correctness.ScottDomains.GlobalizeCorrect
import Mu.proof.Correctness.ScottDomains.RCOCorrect
import Mu.proof.Correctness.ScottDomains.LiftLocalsCorrect
import Mu.proof.Correctness.ScottDomains.ExplicateCorrect
import Mu.proof.Correctness.ScottDomains.SelectCorrect
import Mu.proof.Correctness.ScottDomains.CompilerCorrect
