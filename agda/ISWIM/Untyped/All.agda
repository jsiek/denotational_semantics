{-

  The untyped pipeline, preserved: the compiler as it was before cast
  insertion and the typed intermediate languages (PR #56), with its
  correctness proofs in the five styles.

    ISWIM --simplify--> ISWIM --capture--> Clos2 --prune--> Clos2
          --concretize--> Clos3 --split--> Clos4 --hoist--> Clos5
          --rco--> Mon --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  agda/ISWIM/Untyped/ mirrors agda/ISWIM/: ISWIM/Untyped/X.agda corresponds
  to ISWIM/X.agda, and the module ISWIM.Untyped.X to ISWIM.X. What both
  pipelines use stays outside agda/ISWIM/Untyped/: untyped ISWIM and
  simplify with their proofs, and the ISWIM adequacy, in agda/ISWIM/; the
  primitives, the observations and the frameworks (Framework/), which
  FPC uses too, directly in agda/. So do X86 (ISWIM/Language/X86.agda)
  and its machine (ISWIM/Semantics/CEK/X86.agda), which the typed
  pipeline's assurance uses (the erasure of X86ᵀ). The other semantics of
  X86 and its adequacy moved here when the typed pipeline came to end at
  X86ᵀ (PR #58). A path in a comment of a module here, such as
  Semantics/CEK/Clos5.agda, names the module of agda/ISWIM/Untyped/ if
  there is one, and that of agda/ otherwise.

  The statements are ISWIM/Untyped/Theorems/; agda/All.agda imports this file,
  so make check checks it.

-}

module ISWIM.Untyped.All where

{- the public theorem statements, which reach the definitions (the
   languages, passes and semantics of ISWIM/Untyped/) -}

import ISWIM.Untyped.Theorems.Denotational
import ISWIM.Untyped.Theorems.Simulation
import ISWIM.Untyped.Theorems.Interpreter
import ISWIM.Untyped.Theorems.Reduction
import ISWIM.Untyped.Theorems.Adequacy
import ISWIM.Untyped.Theorems.GraphErrors

{- proof/: syntactic facts about the passes and examples of them -}
import ISWIM.Untyped.proof.Compiler.CaptureScope
import ISWIM.Untyped.proof.Compiler.Examples.ExplicateExample
import ISWIM.Untyped.proof.Compiler.Examples.LiftLocalsExample
import ISWIM.Untyped.proof.Compiler.Examples.RCOExample
import ISWIM.Untyped.proof.Compiler.Examples.SelectExample
import ISWIM.Untyped.proof.Compiler.Examples.SimplifyCaptureExample
import ISWIM.Untyped.proof.Compiler.HoistTable
import ISWIM.Untyped.proof.Compiler.PipelineScope

{- proof/: the graph model: the semantics of each language and each pass, and
   the experiment of a direct semantics of Imp -}
import ISWIM.Untyped.proof.Semantics.Graph.Clos2Iswim
import ISWIM.Untyped.proof.Semantics.Graph.Clos3Iswim
import ISWIM.Untyped.proof.Semantics.Graph.Clos4Iswim
import ISWIM.Untyped.proof.Semantics.Graph.Clos5IswimContinuous
import ISWIM.Untyped.proof.Semantics.Graph.ImpDirect
import ISWIM.Untyped.proof.Correctness.Graph.CompilerCorrect
import ISWIM.Untyped.proof.Correctness.Graph.CompilerExample
import ISWIM.Untyped.proof.Correctness.Graph.ConcretizeCorrect
import ISWIM.Untyped.proof.Correctness.Graph.ConcretizeExample
import ISWIM.Untyped.proof.Correctness.Graph.SplitApp
import ISWIM.Untyped.proof.Correctness.Graph.SplitClosedClosureExample
import ISWIM.Untyped.proof.Correctness.Graph.SplitFiniteCommon
import ISWIM.Untyped.proof.Correctness.Graph.SplitFiniteRel
import ISWIM.Untyped.proof.Correctness.Graph.SplitPreserve
import ISWIM.Untyped.proof.Correctness.Graph.SplitReflectFinite
import ISWIM.Untyped.proof.Correctness.Graph.CaptureCorrect
import ISWIM.Untyped.proof.Correctness.Graph.CaptureExample
import ISWIM.Untyped.proof.Correctness.Graph.ExplicateCommon
import ISWIM.Untyped.proof.Correctness.Graph.ExplicateCorrect
import ISWIM.Untyped.proof.Correctness.Graph.ExplicateCorrectK
import ISWIM.Untyped.proof.Correctness.Graph.HoistCorrect
import ISWIM.Untyped.proof.Correctness.Graph.LiftLocalsCommon
import ISWIM.Untyped.proof.Correctness.Graph.LiftLocalsCorrect
import ISWIM.Untyped.proof.Correctness.Graph.LiftLocalsCorrectK
import ISWIM.Untyped.proof.Correctness.Graph.PruneCorrect
import ISWIM.Untyped.proof.Correctness.Graph.PipelineExample
import ISWIM.Untyped.proof.Correctness.Graph.RCOCorrect
import ISWIM.Untyped.proof.Correctness.Graph.SelectCorrect
import ISWIM.Untyped.proof.Semantics.Graph.X86

{- proof/: the CEK machines + simulations (and the experiment of a direct
   backward simulation for split) -}
import ISWIM.Untyped.proof.Semantics.CEK.Backward
import ISWIM.Untyped.proof.Correctness.CEK.CompilerSim
import ISWIM.Untyped.proof.Correctness.CEK.CompilerX86Sim
import ISWIM.Untyped.proof.Correctness.CEK.ConcretizeSim
import ISWIM.Untyped.proof.Correctness.CEK.SplitBackSim
import ISWIM.Untyped.proof.Correctness.CEK.SplitSim
import ISWIM.Untyped.proof.Correctness.CEK.CaptureSim
import ISWIM.Untyped.proof.Correctness.CEK.ExplicateSim
import ISWIM.Untyped.proof.Correctness.CEK.HoistSim
import ISWIM.Untyped.proof.Correctness.CEK.LiftLocalsSim
import ISWIM.Untyped.proof.Correctness.CEK.PruneSim
import ISWIM.Untyped.proof.Correctness.CEK.RCOSim
import ISWIM.Untyped.proof.Correctness.CEK.SelectSim

{- proof/: the clocked interpreters + value relations -}
import ISWIM.Untyped.proof.Correctness.Interp.CompilerFuel
import ISWIM.Untyped.proof.Correctness.Interp.ConcretizeFuel
import ISWIM.Untyped.proof.Correctness.Interp.SplitFuel
import ISWIM.Untyped.proof.Correctness.Interp.CaptureFuel
import ISWIM.Untyped.proof.Correctness.Interp.ExplicateFuel
import ISWIM.Untyped.proof.Correctness.Interp.HoistFuel
import ISWIM.Untyped.proof.Correctness.Interp.LiftLocalsFuel
import ISWIM.Untyped.proof.Correctness.Interp.PruneFuel
import ISWIM.Untyped.proof.Correctness.Interp.RCOFuel
import ISWIM.Untyped.proof.Correctness.Interp.SelectFuel

{- proof/: the reduction semantics + simulations -}
import ISWIM.Untyped.proof.Semantics.Reduction.Clos2
import ISWIM.Untyped.proof.Semantics.Reduction.Clos3
import ISWIM.Untyped.proof.Semantics.Reduction.Clos4
import ISWIM.Untyped.proof.Semantics.Reduction.Clos5
import ISWIM.Untyped.proof.Correctness.Reduction.CompilerRed
import ISWIM.Untyped.proof.Correctness.Reduction.CompilerX86Red
import ISWIM.Untyped.proof.Correctness.Reduction.ConcretizeRed
import ISWIM.Untyped.proof.Correctness.Reduction.SplitRed
import ISWIM.Untyped.proof.Correctness.Reduction.CaptureRed
import ISWIM.Untyped.proof.Correctness.Reduction.HoistRed
import ISWIM.Untyped.proof.Correctness.Reduction.LiftLocalsRed
import ISWIM.Untyped.proof.Correctness.Reduction.PruneRed
import ISWIM.Untyped.proof.Correctness.Reduction.RCORed

{- proof/: the graph model with errors -}
import ISWIM.Untyped.proof.Semantics.GraphErr.Clos2
import ISWIM.Untyped.proof.Semantics.GraphErr.Clos3
import ISWIM.Untyped.proof.Semantics.GraphErr.Clos4
import ISWIM.Untyped.proof.Semantics.GraphErr.Clos5
import ISWIM.Untyped.proof.Correctness.GraphErr.CompilerCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.ConcretizeCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.SplitApp
import ISWIM.Untyped.proof.Correctness.GraphErr.SplitPreserve
import ISWIM.Untyped.proof.Correctness.GraphErr.SplitReflect
import ISWIM.Untyped.proof.Correctness.GraphErr.SplitRel
import ISWIM.Untyped.proof.Correctness.GraphErr.CaptureCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.ExplicateCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.HoistCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.LiftLocalsCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.PruneCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.RCOCorrect
import ISWIM.Untyped.proof.Correctness.GraphErr.SelectCorrect

{- proof/: adequacy of the graph model and of the graph model with errors for
   the Clos5 and X86 machines, and the compiler's programs -}
import ISWIM.Untyped.proof.Adequacy.Clos5
import ISWIM.Untyped.proof.Adequacy.Clos5Common
import ISWIM.Untyped.proof.Adequacy.Clos5LogRel
import ISWIM.Untyped.proof.Adequacy.Clos5Soundness
import ISWIM.Untyped.proof.Adequacy.Clos5WF
import ISWIM.Untyped.proof.Adequacy.CompileWF
import ISWIM.Untyped.proof.Adequacy.EndToEnd
import ISWIM.Untyped.proof.Adequacy.GraphErr.Clos5
import ISWIM.Untyped.proof.Adequacy.GraphErr.Clos5Common
import ISWIM.Untyped.proof.Adequacy.GraphErr.Clos5LogRel
import ISWIM.Untyped.proof.Adequacy.GraphErr.Clos5Soundness
import ISWIM.Untyped.proof.Adequacy.GraphErr.Clos5WF
import ISWIM.Untyped.proof.Adequacy.GraphErr.EndToEnd
import ISWIM.Untyped.proof.Adequacy.GraphErr.X86CompileWF
import ISWIM.Untyped.proof.Adequacy.ISWIMCompile
import ISWIM.Untyped.proof.Adequacy.X86CompileWF
import ISWIM.Untyped.proof.Adequacy.Values
import ISWIM.Untyped.proof.Adequacy.X86
import ISWIM.Untyped.proof.Adequacy.X86Common
import ISWIM.Untyped.proof.Adequacy.X86LogRel
import ISWIM.Untyped.proof.Adequacy.X86Soundness
import ISWIM.Untyped.proof.Adequacy.X86WF
import ISWIM.Untyped.proof.Adequacy.GraphErr.X86
import ISWIM.Untyped.proof.Adequacy.GraphErr.X86Common
import ISWIM.Untyped.proof.Adequacy.GraphErr.X86Consistent
import ISWIM.Untyped.proof.Adequacy.GraphErr.X86LogRel
import ISWIM.Untyped.proof.Adequacy.GraphErr.X86Soundness
import ISWIM.Untyped.proof.Adequacy.GraphErr.X86WF
