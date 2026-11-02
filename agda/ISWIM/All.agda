{-

  The ISWIM compilers and their correctness proofs, in five styles.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --capture--> Clos2ᵀ
          --prune--> Clos2ᵀ --concretize--> Clos3ᵀ --split--> Clos4ᵀ
          --hoist--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

  The intermediate languages and the target, the typed assembly
  language X86ᵀ (ISWIM/Language/Typed/), are intrinsically typed; the
  source, ISWIM, is untyped. The untyped pipeline that preceded this one
  is preserved in ISWIM/Untyped/ (see ISWIM/Untyped/All.agda), and
  checked too.

  This file is checked from agda/All.agda (make check, from the root of
  the repository). See agda/README.md for the layout: the theorem
  statements (ISWIM/Theorems/) and the definitions they use (everything
  outside the proof/ directories) are the audit surface; ISWIM/proof/
  holds the proofs.

  This file imports the theorem files, which reach the whole audit
  surface, every module of ISWIM/proof/, and the preserved untyped
  pipeline.

-}

module ISWIM.All where

{- ---------------------------------------------------------------------------
   The public theorem statements
   --------------------------------------------------------------------------- -}

import ISWIM.Theorems.Denotational
import ISWIM.Theorems.Simulation
import ISWIM.Theorems.Interpreter
import ISWIM.Theorems.Reduction
import ISWIM.Theorems.GraphErrors
import ISWIM.Theorems.Adequacy

{- assurance (not in the totals, nor in the comparison): erasing X86ᵀ to
   X86 keeps the meaning of every program, in the CEK machines, and the
   code select emits is, without its types, that of select into untyped
   X86 -}
import ISWIM.Theorems.X86Erasure
import ISWIM.proof.Assurance.X86Agree
import ISWIM.proof.Assurance.X86Erasure

{- ---------------------------------------------------------------------------
   The untyped pipeline, preserved
   --------------------------------------------------------------------------- -}

import ISWIM.Untyped.All

{- ---------------------------------------------------------------------------
   ISWIM/proof/: syntactic facts about the passes: simplify, cast insertion on
   closed programs, hoist's references to older definitions, and the
   definitions, labels and frames that select instructions relies on
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Compiler.CastScope
import ISWIM.proof.Compiler.HoistOlder
import ISWIM.proof.Compiler.SelectErase
import ISWIM.proof.Compiler.SimplifyFacts
import ISWIM.proof.Compiler.SimplifyScope

{- ---------------------------------------------------------------------------
   ISWIM/proof/: the plain graph model: the lemmas about the semantics of each
   language and the correctness of each pass
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Correctness.Graph.CastCorrect
import ISWIM.proof.Correctness.Graph.CompilerCorrect
import ISWIM.proof.Correctness.Graph.ConcretizeCorrect
import ISWIM.proof.Correctness.Graph.SplitCorrect
import ISWIM.proof.Correctness.Graph.SplitPreserve
import ISWIM.proof.Correctness.Graph.SplitReflect
import ISWIM.proof.Correctness.Graph.SplitRel
import ISWIM.proof.Correctness.Graph.CaptureCorrect
import ISWIM.proof.Correctness.Graph.ExplicateCorrect
import ISWIM.proof.Correctness.Graph.HoistCorrect
import ISWIM.proof.Correctness.Graph.LiftLocalsCorrect
import ISWIM.proof.Correctness.Graph.PruneCorrect
import ISWIM.proof.Correctness.Graph.RCOCorrect
import ISWIM.proof.Correctness.Graph.SelectCorrect
import ISWIM.proof.Correctness.Graph.SimplifyCorrect
import ISWIM.proof.Semantics.Graph.ISWIM
import ISWIM.proof.Semantics.Graph.ISWIMContinuous
import ISWIM.proof.Semantics.Graph.Typed.CFG
import ISWIM.proof.Semantics.Graph.Typed.Clos2
import ISWIM.proof.Semantics.Graph.Typed.Clos3
import ISWIM.proof.Semantics.Graph.Typed.Clos4
import ISWIM.proof.Semantics.Graph.Typed.Clos5
import ISWIM.proof.Semantics.Graph.Typed.Ops

{- ---------------------------------------------------------------------------
   ISWIM/proof/: the CEK machines + simulations
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Correctness.CEK.CastSim
import ISWIM.proof.Correctness.CEK.CastSimLemmas
import ISWIM.proof.Correctness.CEK.Clos5Common
import ISWIM.proof.Correctness.CEK.Common
import ISWIM.proof.Correctness.CEK.ConcretizeSim
import ISWIM.proof.Correctness.CEK.SplitSim
import ISWIM.proof.Correctness.CEK.CaptureSim
import ISWIM.proof.Correctness.CEK.ExplicateSim
import ISWIM.proof.Correctness.CEK.HoistSim
import ISWIM.proof.Correctness.CEK.LiftLocalsSim
import ISWIM.proof.Correctness.CEK.PruneSim
import ISWIM.proof.Correctness.CEK.PipelineSim
import ISWIM.proof.Correctness.CEK.RCOSim
import ISWIM.proof.Correctness.CEK.SelectSim
import ISWIM.proof.Correctness.CEK.SimplifySim

{- ---------------------------------------------------------------------------
   ISWIM/proof/: the clocked interpreters + value relations
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Correctness.Interp.CastFuel
import ISWIM.proof.Correctness.Interp.CompilerFuel
import ISWIM.proof.Correctness.Interp.ConcretizeFuel
import ISWIM.proof.Correctness.Interp.SplitFuel
import ISWIM.proof.Correctness.Interp.CaptureFuel
import ISWIM.proof.Correctness.Interp.ExplicateFuel
import ISWIM.proof.Correctness.Interp.HoistFuel
import ISWIM.proof.Correctness.Interp.LiftLocalsFuel
import ISWIM.proof.Correctness.Interp.PruneFuel
import ISWIM.proof.Correctness.Interp.RCOFuel
import ISWIM.proof.Correctness.Interp.SelectFuel
import ISWIM.proof.Correctness.Interp.SimplifyFuel
import ISWIM.proof.Semantics.Interp.Typed.Clos5
import ISWIM.proof.Semantics.Interp.Typed.Rel

{- ---------------------------------------------------------------------------
   ISWIM/proof/: the reduction semantics + simulations (explicate control and
   select instructions are the CEK column's)
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Correctness.Reduction.CastRed
import ISWIM.proof.Correctness.Reduction.ConcretizeRed
import ISWIM.proof.Correctness.Reduction.SplitRed
import ISWIM.proof.Correctness.Reduction.CaptureRed
import ISWIM.proof.Correctness.Reduction.HoistRed
import ISWIM.proof.Correctness.Reduction.LiftLocalsRed
import ISWIM.proof.Correctness.Reduction.PruneRed
import ISWIM.proof.Correctness.Reduction.PipelineRed
import ISWIM.proof.Correctness.Reduction.RCORed
import ISWIM.proof.Correctness.Reduction.SimplifyRed
import ISWIM.proof.Semantics.Reduction.Typed.Clos2
import ISWIM.proof.Semantics.Reduction.Typed.Clos3
import ISWIM.proof.Semantics.Reduction.Typed.Clos4
import ISWIM.proof.Semantics.Reduction.Typed.Clos5
import ISWIM.proof.Semantics.Reduction.Typed.ISWIM

{- ---------------------------------------------------------------------------
   ISWIM/proof/: the graph model with errors
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Correctness.GraphErr.CastCorrect
import ISWIM.proof.Correctness.GraphErr.CompilerCorrect
import ISWIM.proof.Correctness.GraphErr.ConcretizeCorrect
import ISWIM.proof.Correctness.GraphErr.SplitCorrect
import ISWIM.proof.Correctness.GraphErr.SplitPreserve
import ISWIM.proof.Correctness.GraphErr.SplitReflect
import ISWIM.proof.Correctness.GraphErr.SplitRel
import ISWIM.proof.Correctness.GraphErr.CaptureCorrect
import ISWIM.proof.Correctness.GraphErr.ExplicateCorrect
import ISWIM.proof.Correctness.GraphErr.HoistCorrect
import ISWIM.proof.Correctness.GraphErr.LiftLocalsCorrect
import ISWIM.proof.Correctness.GraphErr.PruneCorrect
import ISWIM.proof.Correctness.GraphErr.RCOCorrect
import ISWIM.proof.Correctness.GraphErr.SelectCorrect
import ISWIM.proof.Correctness.GraphErr.SimplifyCorrect
import ISWIM.proof.Semantics.GraphErr.ISWIM
import ISWIM.proof.Semantics.GraphErr.Prim
import ISWIM.proof.Semantics.GraphErr.Typed.CFG
import ISWIM.proof.Semantics.GraphErr.Typed.Clos2
import ISWIM.proof.Semantics.GraphErr.Typed.Clos3
import ISWIM.proof.Semantics.GraphErr.Typed.Clos4
import ISWIM.proof.Semantics.GraphErr.Typed.Clos5
import ISWIM.proof.Semantics.GraphErr.Typed.Imp
import ISWIM.proof.Adequacy.GraphErr.X86Mono

{- ---------------------------------------------------------------------------
   ISWIM/proof/: adequacy of the plain graph model (ISWIM, Clos5ᵀ and X86ᵀ
   machines) and of the graph model with errors (ISWIM and X86 machines;
   Clos5ᵀ derived from the CEK column's simulation)
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Adequacy.Clos5
import ISWIM.proof.Adequacy.Clos5Common
import ISWIM.proof.Adequacy.Clos5LogRel
import ISWIM.proof.Adequacy.Clos5Soundness
import ISWIM.proof.Adequacy.Clos5Values
import ISWIM.proof.Adequacy.Common
import ISWIM.proof.Adequacy.EndToEnd
import ISWIM.proof.Adequacy.GraphErr.Agree
import ISWIM.proof.Adequacy.GraphErr.EndToEnd
import ISWIM.proof.Adequacy.GraphErr.ISWIM
import ISWIM.proof.Adequacy.GraphErr.LogRel
import ISWIM.proof.Adequacy.GraphErr.Simplify
import ISWIM.proof.Adequacy.GraphErr.Soundness
import ISWIM.proof.Adequacy.GraphErr.X86
import ISWIM.proof.Adequacy.GraphErr.X86Common
import ISWIM.proof.Adequacy.GraphErr.X86LogRel
import ISWIM.proof.Adequacy.GraphErr.X86Soundness
import ISWIM.proof.Adequacy.ISWIM
import ISWIM.proof.Adequacy.LogRel
import ISWIM.proof.Adequacy.Soundness
import ISWIM.proof.Adequacy.X86
import ISWIM.proof.Adequacy.X86Common
import ISWIM.proof.Adequacy.X86Compiled
import ISWIM.proof.Adequacy.X86LogRel
import ISWIM.proof.Adequacy.X86Soundness

{- ---------------------------------------------------------------------------
   examples (smoke tests)
   --------------------------------------------------------------------------- -}

import ISWIM.proof.Compiler.Examples.CastExample
import ISWIM.proof.Compiler.Examples.PipelineExample
import ISWIM.proof.Compiler.Examples.SimplifyExample
