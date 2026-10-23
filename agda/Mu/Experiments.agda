{-

  Experiments on ISWIMμ that are not part of the PLDI 2027 paper's
  development (Mu/All.agda). agda/All.agda imports this file, so that
  `make check` checks them too.

  * mixing semantics: simplify in the graph model and the other passes
    by the clocked interpreters, joined at ISWIMμ by the adequacy of its
    graph semantics for its interpreter (Mu/proof/Adequacy/ISWIM.agda):
    Mu/proof/Mixed/CompilerMixed.agda (the interpreter column's
    compile-const and compile-diverges for main : Int); its
    sizes are printed by `python3 papers/PLDI-2027/loc.py --mixed`.

-}

module Mu.Experiments where

import Mu.proof.Mixed.CompilerMixed
