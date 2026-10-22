{-

  ISWIMμ: a typed ISWIM with iso-recursive types (no recursion
  construct, no errors) and its compiler to the typed assembly language
  X86μ, proved correct in four styles, in parallel with the typed
  pipeline's proofs (agda/All.agda); the main experiment of the size
  comparison (papers/PLDI-2027/loc.md, and the design note,
  papers/PLDI-2027/notes/iswim-mu-design.md).

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ
           --concretize--> Clos3μ --delay--> Clos4μ --globalize--> Clos5μ --rco--> Monμ
           --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  The public theorem statements are in Mu/Theorems/ (Denotational,
  Simulation, Interpreter, Reduction, Adequacy), each with its type
  written out and defined as the corresponding theorem of Mu/proof/; they
  and the definitions they use (everything in Mu/ outside Mu/proof/) are
  ISWIMμ's audit surface.

  agda/Mu/ mirrors agda/: Mu/X.agda corresponds to X.agda (with
  Language/Typed/ as Mu/Language/ and Semantics/<style>/Typed/ as
  Mu/Semantics/<style>/), and the module Mu.X to X. It reuses the
  frameworks of agda/Framework/ unchanged; Mu/Framework/AllUtil.agda
  (with Mu/proof/Framework/AllProp.agda) adds heterogeneous vectors
  (All), which the lists of types of ISWIMμ's contexts and tuples need.

  * graph model: Mu/proof/Correctness/Graph/CompilerCorrect.agda
    (compile-x86-same, and compile-x86-int for main : Int), with delay
    by the approximant logical relation
    (Mu/proof/Correctness/Graph/DelayRel.agda);
  * CEK machine + simulation: Mu/proof/Correctness/CEK/PipelineSim.agda
    (compile-x86-correct, and compile-x86-const and
    compile-x86-diverges for main : Int);
  * clocked interpreter + value relations:
    Mu/proof/Correctness/Interp/CompilerFuel.agda (compile-x86-correct,
    and compile-x86-const and compile-x86-diverges for main : Int);
  * reduction semantics + simulation:
    Mu/proof/Correctness/Reduction/PipelineRed.agda (likewise);
  * adequacy of the graph model for the clocked interpreters of ISWIMμ
    and X86μ: Mu/proof/Adequacy/EndToEnd.agda (the graph model's
    end-to-end theorem, observed through the interpreters: the
    operational styles' statement for main : Int); an alternative,
    reported separately, against the CEK machines instead:
    Mu/proof/Adequacy/CEK/EndToEnd.agda;
  * mixing semantics (an experiment): simplify in the graph model and
    the other passes by the interpreters, joined at ISWIMμ by the
    adequacy of its graph semantics for its interpreter
    (Mu/proof/Adequacy/ISWIM.agda): Mu/proof/Mixed/CompilerMixed.agda
    (the interpreter column's compile-x86-const and
    compile-x86-diverges for main : Int).

-}

module Mu.All where

import Mu.Theorems.Denotational
import Mu.Theorems.Simulation
import Mu.Theorems.Interpreter
import Mu.Theorems.Reduction
import Mu.Theorems.Adequacy
import Mu.proof.Correctness.Graph.CompilerCorrect
import Mu.proof.Correctness.CEK.PipelineSim
import Mu.proof.Correctness.Interp.CompilerFuel
import Mu.proof.Correctness.Reduction.PipelineRed
import Mu.proof.Adequacy.EndToEnd
import Mu.proof.Adequacy.CEK.EndToEnd
import Mu.proof.Mixed.CompilerMixed
{- a design experiment, in no proof's total: a finite source side cannot
   satisfy the function clause of delay's relation -}
import Mu.proof.Correctness.Graph.DelayDesignFiniteSource
import Mu.proof.Semantics.CEK.NoError
import Mu.proof.Semantics.Interp.NoError
import Mu.proof.Semantics.Reduction.NoError
import Mu.proof.Compiler.Examples.RecursionExample
import Mu.proof.Compiler.Examples.RecursionInterp
