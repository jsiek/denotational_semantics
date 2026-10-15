{-

  The ISWIMμ pilot: a typed ISWIM with iso-recursive types (ISWIMμ) and
  its closure-conversion passes, proved correct in two of the five
  styles, as a parallel copy of the typed pipeline's
  (agda/All.agda), for papers/PLDI-2027/notes/iswim-mu-design.md.

    ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ --concretize--> Clos3μ
           --delay--> Clos4μ

  agda/Mu/ mirrors agda/: Mu/X.agda corresponds to X.agda (with
  Language/Typed/ as Mu/Language/ and Semantics/<style>/Typed/ as
  Mu/Semantics/<style>/), and the module Mu.X to X. It reuses the
  frameworks of agda/Framework/ unchanged; Mu/Framework/AllUtil.agda
  adds heterogeneous vectors (All), which the lists of types of ISWIMμ's
  contexts and tuples need.

  * graph model: Mu/proof/Correctness/Graph/CompilerCorrect.agda
    (compile₄-same), with delay by the approximant logical relation
    (Mu/proof/Correctness/Graph/DelayRel.agda);
  * CEK machine + simulation: Mu/proof/Correctness/CEK/PipelineSim.agda
    (compile₄-correct);
  * reduction semantics + simulation:
    Mu/proof/Correctness/Reduction/PipelineRed.agda (compile₄-correct).

-}

module Mu.All where

import Mu.proof.Correctness.Graph.CompilerCorrect
import Mu.proof.Correctness.CEK.PipelineSim
import Mu.proof.Correctness.Reduction.PipelineRed
import Mu.proof.Compiler.Examples.RecursionExample
