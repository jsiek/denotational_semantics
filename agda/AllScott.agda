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

import proof.Framework.Scott.Solve
