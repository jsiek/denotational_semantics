{-

  The denotational: Scott domains column, for the ISWIMμ compiler
  (agda/Mu/). It needs TypeTopology besides the standard library, so it
  is not part of All.agda; check it with

    make check-scott

  which fetches TypeTopology (scott/fetch-typetopology.sh) and runs
  scott/check.sh on this file. See agda/Framework/Scott/.

-}

module AllScott where

{- the language-independent lemmas: the solution of the domain equation,
   and the domain of values and its operators -}
import proof.Framework.Scott.Solve
import proof.Framework.Scott.Domain
import proof.Framework.Scott.Ops

{- the semantics of the languages -}
import Mu.Semantics.Scott.ISWIM
import Mu.Semantics.Scott.Clos2
import Mu.Semantics.Scott.Clos3
import Mu.Semantics.Scott.Clos4
import Mu.Semantics.Scott.Clos5
