{-

  The denotational: Scott domains column, and the adequacy of the
  Scott-domain semantics, for the FPC compiler (agda/FPC/). It needs TypeTopology besides the standard library, so it
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
import FPC.Theorems.CorrectWrtScottDomains
import FPC.Theorems.ScottDomainsAdequateWrtClockedInterpreters

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
import FPC.proof.Semantics.ScottDomains.PruneLemmas
import FPC.proof.Semantics.ScottDomains.BackEndLemmas

{- the passes, and the whole compiler -}
import FPC.proof.Correctness.ScottDomains.SimplifyCorrect
import FPC.proof.Correctness.ScottDomains.CaptureCorrect
import FPC.proof.Correctness.ScottDomains.PruneCorrect
import FPC.proof.Correctness.ScottDomains.ConcretizeCorrect
import FPC.proof.Correctness.ScottDomains.SplitRel
import FPC.proof.Correctness.ScottDomains.SplitPreserve
import FPC.proof.Correctness.ScottDomains.SplitReflect
import FPC.proof.Correctness.ScottDomains.SplitTerms
import FPC.proof.Correctness.ScottDomains.SplitCorrect
import FPC.proof.Correctness.ScottDomains.HoistCorrect
import FPC.proof.Correctness.ScottDomains.RCOCorrect
import FPC.proof.Correctness.ScottDomains.LiftLocalsCorrect
import FPC.proof.Correctness.ScottDomains.ExplicateCorrect
import FPC.proof.Correctness.ScottDomains.SelectCorrect
import FPC.proof.Correctness.ScottDomains.CompilerCorrect

{- adequacy for the clocked interpreters -}
import FPC.proof.Adequacy.ScottDomains.Soundness
import FPC.proof.Adequacy.ScottDomains.LogRel
import FPC.proof.Adequacy.ScottDomains.FPC
import FPC.proof.Adequacy.ScottDomains.X86Soundness
import FPC.proof.Adequacy.ScottDomains.X86LogRel
import FPC.proof.Adequacy.ScottDomains.X86Compiled
import FPC.proof.Adequacy.ScottDomains.X86
import FPC.proof.Adequacy.ScottDomains.EndToEnd
