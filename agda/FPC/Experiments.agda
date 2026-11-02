{-

  Experiments on FPC that are not part of the PLDI 2027 paper's
  development (FPC/All.agda). agda/All.agda imports this file, so that
  `make check` checks them too.

  * mixing semantics: simplify in the graph model and the other passes
    by the clocked interpreters, joined at FPC by the adequacy of its
    graph semantics for its interpreter (FPC/proof/Adequacy/FPC.agda):
    FPC/proof/Mixed/CompilerMixed.agda (the interpreter column's
    compile-const and compile-diverges for main : Int); its
    sizes are printed by `python3 papers/PLDI-2027/loc.py --mixed`.

-}

module FPC.Experiments where

import FPC.proof.Mixed.CompilerMixed
