{-

  The untyped pipeline, preserved: the compiler as it was before cast
  insertion and the typed intermediate languages (PR #56), with its
  correctness proofs in the five styles.

    ISWIM --simplify--> ISWIM --capture--> Clos2 --prune--> Clos2
          --concretize--> Clos3 --split--> Clos4 --hoist--> Clos5
          --rco--> Mon --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  agda/Untyped/ mirrors agda/: Untyped/X.agda was X.agda, and the module
  Untyped.X was X. What both pipelines use stays in agda/: untyped ISWIM
  and simplify with their proofs, the primitives, the observations, the
  frameworks (Framework/), and the ISWIM adequacy; and so do X86
  (Language/X86.agda) and its machine (Semantics/CEK/X86.agda), which
  the typed pipeline's assurance uses (the erasure of X86ᵀ). The other
  semantics of X86 and its adequacy moved here when the typed pipeline
  came to end at X86ᵀ (PR #58). A path in a comment of a module here, such as
  Semantics/CEK/Clos5.agda, names the module of agda/Untyped/ if there is
  one, and that of agda/ otherwise.

  The statements are Untyped/Theorems/; agda/All.agda imports this file,
  so make check checks it.

-}

module Untyped.All where

{- the public theorem statements, which reach the definitions (the
   languages, passes and semantics of Untyped/) -}

import Untyped.Theorems.Denotational
import Untyped.Theorems.Simulation
import Untyped.Theorems.Interpreter
import Untyped.Theorems.Reduction
import Untyped.Theorems.Adequacy
import Untyped.Theorems.GraphErrors

{- proof/: syntactic facts about the passes and examples of them -}
import Untyped.proof.Compiler.CaptureScope
import Untyped.proof.Compiler.Examples.ExplicateExample
import Untyped.proof.Compiler.Examples.LiftLocalsExample
import Untyped.proof.Compiler.Examples.RCOExample
import Untyped.proof.Compiler.Examples.SelectExample
import Untyped.proof.Compiler.Examples.SimplifyCaptureExample
import Untyped.proof.Compiler.HoistTable
import Untyped.proof.Compiler.PipelineScope

{- proof/: the graph model: the semantics of each language and each pass, and the experiment of a direct semantics of Imp -}
import Untyped.proof.Semantics.Graph.Clos2Iswim
import Untyped.proof.Semantics.Graph.Clos3Iswim
import Untyped.proof.Semantics.Graph.Clos4Iswim
import Untyped.proof.Semantics.Graph.Clos5IswimContinuous
import Untyped.proof.Semantics.Graph.ImpDirect
import Untyped.proof.Correctness.Graph.CompilerCorrect
import Untyped.proof.Correctness.Graph.CompilerExample
import Untyped.proof.Correctness.Graph.ConcretizeCorrect
import Untyped.proof.Correctness.Graph.ConcretizeExample
import Untyped.proof.Correctness.Graph.SplitApp
import Untyped.proof.Correctness.Graph.SplitClosedClosureExample
import Untyped.proof.Correctness.Graph.SplitFiniteCommon
import Untyped.proof.Correctness.Graph.SplitFiniteRel
import Untyped.proof.Correctness.Graph.SplitPreserve
import Untyped.proof.Correctness.Graph.SplitReflectFinite
import Untyped.proof.Correctness.Graph.CaptureCorrect
import Untyped.proof.Correctness.Graph.CaptureExample
import Untyped.proof.Correctness.Graph.ExplicateCommon
import Untyped.proof.Correctness.Graph.ExplicateCorrect
import Untyped.proof.Correctness.Graph.ExplicateCorrectK
import Untyped.proof.Correctness.Graph.HoistCorrect
import Untyped.proof.Correctness.Graph.LiftLocalsCommon
import Untyped.proof.Correctness.Graph.LiftLocalsCorrect
import Untyped.proof.Correctness.Graph.LiftLocalsCorrectK
import Untyped.proof.Correctness.Graph.PruneCorrect
import Untyped.proof.Correctness.Graph.PipelineExample
import Untyped.proof.Correctness.Graph.RCOCorrect
import Untyped.proof.Correctness.Graph.SelectCorrect
import Untyped.proof.Semantics.Graph.X86

{- proof/: the CEK machines + simulations (and the experiment of a direct backward simulation for split) -}
import Untyped.proof.Semantics.CEK.Backward
import Untyped.proof.Correctness.CEK.CompilerSim
import Untyped.proof.Correctness.CEK.CompilerX86Sim
import Untyped.proof.Correctness.CEK.ConcretizeSim
import Untyped.proof.Correctness.CEK.SplitBackSim
import Untyped.proof.Correctness.CEK.SplitSim
import Untyped.proof.Correctness.CEK.CaptureSim
import Untyped.proof.Correctness.CEK.ExplicateSim
import Untyped.proof.Correctness.CEK.HoistSim
import Untyped.proof.Correctness.CEK.LiftLocalsSim
import Untyped.proof.Correctness.CEK.PruneSim
import Untyped.proof.Correctness.CEK.RCOSim
import Untyped.proof.Correctness.CEK.SelectSim

{- proof/: the clocked interpreters + value relations -}
import Untyped.proof.Correctness.Interp.CompilerFuel
import Untyped.proof.Correctness.Interp.ConcretizeFuel
import Untyped.proof.Correctness.Interp.SplitFuel
import Untyped.proof.Correctness.Interp.CaptureFuel
import Untyped.proof.Correctness.Interp.ExplicateFuel
import Untyped.proof.Correctness.Interp.HoistFuel
import Untyped.proof.Correctness.Interp.LiftLocalsFuel
import Untyped.proof.Correctness.Interp.PruneFuel
import Untyped.proof.Correctness.Interp.RCOFuel
import Untyped.proof.Correctness.Interp.SelectFuel

{- proof/: the reduction semantics + simulations -}
import Untyped.proof.Semantics.Reduction.Clos2
import Untyped.proof.Semantics.Reduction.Clos3
import Untyped.proof.Semantics.Reduction.Clos4
import Untyped.proof.Semantics.Reduction.Clos5
import Untyped.proof.Correctness.Reduction.CompilerRed
import Untyped.proof.Correctness.Reduction.CompilerX86Red
import Untyped.proof.Correctness.Reduction.ConcretizeRed
import Untyped.proof.Correctness.Reduction.SplitRed
import Untyped.proof.Correctness.Reduction.CaptureRed
import Untyped.proof.Correctness.Reduction.HoistRed
import Untyped.proof.Correctness.Reduction.LiftLocalsRed
import Untyped.proof.Correctness.Reduction.PruneRed
import Untyped.proof.Correctness.Reduction.RCORed

{- proof/: the graph model with errors -}
import Untyped.proof.Semantics.GraphErr.Clos2
import Untyped.proof.Semantics.GraphErr.Clos3
import Untyped.proof.Semantics.GraphErr.Clos4
import Untyped.proof.Semantics.GraphErr.Clos5
import Untyped.proof.Correctness.GraphErr.CompilerCorrect
import Untyped.proof.Correctness.GraphErr.ConcretizeCorrect
import Untyped.proof.Correctness.GraphErr.SplitApp
import Untyped.proof.Correctness.GraphErr.SplitPreserve
import Untyped.proof.Correctness.GraphErr.SplitReflect
import Untyped.proof.Correctness.GraphErr.SplitRel
import Untyped.proof.Correctness.GraphErr.CaptureCorrect
import Untyped.proof.Correctness.GraphErr.ExplicateCorrect
import Untyped.proof.Correctness.GraphErr.HoistCorrect
import Untyped.proof.Correctness.GraphErr.LiftLocalsCorrect
import Untyped.proof.Correctness.GraphErr.PruneCorrect
import Untyped.proof.Correctness.GraphErr.RCOCorrect
import Untyped.proof.Correctness.GraphErr.SelectCorrect

{- proof/: adequacy of the graph model and of the graph model with errors for the Clos5 and X86 machines, and the compiler's programs -}
import Untyped.proof.Adequacy.Clos5
import Untyped.proof.Adequacy.Clos5Common
import Untyped.proof.Adequacy.Clos5LogRel
import Untyped.proof.Adequacy.Clos5Soundness
import Untyped.proof.Adequacy.Clos5WF
import Untyped.proof.Adequacy.CompileWF
import Untyped.proof.Adequacy.EndToEnd
import Untyped.proof.Adequacy.GraphErr.Clos5
import Untyped.proof.Adequacy.GraphErr.Clos5Common
import Untyped.proof.Adequacy.GraphErr.Clos5LogRel
import Untyped.proof.Adequacy.GraphErr.Clos5Soundness
import Untyped.proof.Adequacy.GraphErr.Clos5WF
import Untyped.proof.Adequacy.GraphErr.EndToEnd
import Untyped.proof.Adequacy.GraphErr.X86CompileWF
import Untyped.proof.Adequacy.ISWIMCompile
import Untyped.proof.Adequacy.X86CompileWF
import Untyped.proof.Adequacy.Values
import Untyped.proof.Adequacy.X86
import Untyped.proof.Adequacy.X86Common
import Untyped.proof.Adequacy.X86LogRel
import Untyped.proof.Adequacy.X86Soundness
import Untyped.proof.Adequacy.X86WF
import Untyped.proof.Adequacy.GraphErr.X86
import Untyped.proof.Adequacy.GraphErr.X86Common
import Untyped.proof.Adequacy.GraphErr.X86Consistent
import Untyped.proof.Adequacy.GraphErr.X86LogRel
import Untyped.proof.Adequacy.GraphErr.X86Soundness
import Untyped.proof.Adequacy.GraphErr.X86WF
