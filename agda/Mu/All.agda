{-

  The ISWIMμ pilot: a typed ISWIM with iso-recursive types (ISWIMμ) and
  its compiler to the typed assembly language X86μ, proved correct as a
  parallel copy of the typed pipeline's (agda/All.agda), for
  papers/PLDI-2027/notes/iswim-mu-design.md.

    ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ --concretize--> Clos3μ
           --delay--> Clos4μ --globalize--> Clos5μ --rco--> Monμ
           --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  agda/Mu/ mirrors agda/: Mu/X.agda corresponds to X.agda (with
  Language/Typed/ as Mu/Language/ and Semantics/<style>/Typed/ as
  Mu/Semantics/<style>/), and the module Mu.X to X. It reuses the
  frameworks of agda/Framework/ unchanged; Mu/Framework/AllUtil.agda
  (with AllProp.agda) adds heterogeneous vectors (All), which the lists
  of types of ISWIMμ's contexts and tuples need.

  * graph model: Mu/proof/Correctness/Graph/CompilerCorrect.agda
    (compile-x86-same, and compile-x86-int for main : Int), with delay
    by the approximant logical relation
    (Mu/proof/Correctness/Graph/DelayRel.agda);
  * CEK machine + simulation: Mu/proof/Correctness/CEK/PipelineSim.agda
    (compile-x86-correct, and compile-x86-const and
    compile-x86-diverges for main : Int);
  * clocked interpreter + value relations:
    Mu/proof/Correctness/Interp/CompilerFuel.agda (compile-x86-correct);
  * reduction semantics + simulation:
    Mu/proof/Correctness/Reduction/PipelineRed.agda (compile-x86-correct).

-}

module Mu.All where

import Mu.proof.Correctness.Graph.CompilerCorrect
import Mu.proof.Correctness.CEK.PipelineSim
import Mu.proof.Correctness.Interp.CompilerFuel
import Mu.proof.Correctness.Reduction.PipelineRed
import Mu.proof.Adequacy.EndToEnd
import Mu.proof.Semantics.CEK.NoError
import Mu.proof.Semantics.Interp.NoError
import Mu.proof.Semantics.Reduction.NoError
import Mu.proof.Compiler.Examples.RecursionExample
import Mu.proof.Compiler.Examples.RecursionInterp
