{-

  The denotational: Scott domains column (a pilot: ISWIM, Clos2 and the
  enclose pass). It needs TypeTopology besides the standard library, so it
  is not part of All.agda; check it with

    make check-scott

  which fetches TypeTopology (scott/fetch-typetopology.sh) and runs
  scott/check.sh on this file. See agda/Framework/Scott/.

  This file imports the theorem file, which reaches the audit surface of
  the column, and every module of proof/ that belongs to it.

-}

module AllScott where

{- the theorem statements -}
import Theorems.Scott

{- the language-independent lemmas: the solution of the domain equation,
   and the domain of values and its operators -}
import proof.Framework.Scott.Solve
import proof.Framework.Scott.Domain
import proof.Framework.Scott.Ops

{- correctness of enclose -}
import proof.Correctness.Scott.EncloseCorrect
