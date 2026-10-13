{-

  The closure-conversion compiler and its correctness proofs.

    ISWIM --simplify--> ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  Check everything with

    agda --safe agda/All.agda

  (or make check, from the root of the repository, which also greps for
  postulates and pragmas). See README.md for the layout: the theorem
  statements (Theorems/) and the definitions they use (everything outside
  proof/) are the audit surface; proof/ holds the proofs.

  This file imports the theorem files, which reach the whole audit
  surface, and every module of proof/.

-}

module All where

{- ---------------------------------------------------------------------------
   The public theorem statements
   --------------------------------------------------------------------------- -}

import Theorems.Denotational
import Theorems.Simulation
import Theorems.Interpreter
import Theorems.Adequacy
import Theorems.Reduction

{- ---------------------------------------------------------------------------
   proof/: language-independent lemmas: about tuples of the abt extract,
   lists, the syntax of any signature (renaming, scoping, uses), sets and
   environments, the graph model (values, operators, continuity), the
   generic denotational semantics, and the small-step (forward
   simulations) and clocked (clock-for-clock correctness) frameworks
   --------------------------------------------------------------------------- -}

import proof.Framework.abt.ScopedTuple
import proof.Framework.ListUtil
import proof.Framework.Syntax.Uses
import proof.Framework.Syntax.Rename
import proof.Framework.Syntax.Scope
import proof.Framework.Syntax.ScopeRename
import proof.Framework.Syntax.Subst
import proof.Framework.Syntax.ScopeSubst
import proof.Framework.Syntax.SubstRel
import proof.Framework.GraphModel.SetsAsPredicates
import proof.Framework.GraphModel.DOpSig
import proof.Framework.GraphModel.DenotProperties
import proof.Framework.GraphModel.Env
import proof.Framework.GraphModel.Semantics
import proof.Framework.GraphModel.RenameSem
import proof.Framework.GraphModel.Domain
import proof.Framework.GraphModel.Ops
import proof.Framework.GraphModel.Continuity
import proof.Framework.GraphModel.SemanticsUtil
import proof.Framework.Smallstep
import proof.Framework.Simulation
import proof.Framework.Clocked
import proof.Framework.Reduction

{- ---------------------------------------------------------------------------
   proof/: syntactic facts about the passes, used by both operational
   styles: enclose produces well-scoped programs from closed ones, the
   table of globalize, and the compiler produces well-scoped Clos5
   programs (Scoped), the precondition of both operational proofs of
   remove complex operands
   --------------------------------------------------------------------------- -}

import proof.Compiler.SimplifyFacts
import proof.Compiler.EncloseScope
import proof.Compiler.GlobalizeTable
import proof.Compiler.PipelineScope

{- ---------------------------------------------------------------------------
   proof/: the denotational (graph-model) development
   --------------------------------------------------------------------------- -}

{- the monotonicity, consistency and continuity of the primitives and of
   the semantics of each language -}
import proof.Semantics.Graph.Prim
import proof.Semantics.Graph.ISWIM
import proof.Semantics.Graph.Clos2Iswim
import proof.Semantics.Graph.Clos3Iswim
import proof.Semantics.Graph.Clos3IswimContinuous
import proof.Semantics.Graph.Clos4Iswim
import proof.Semantics.Graph.Clos4IswimContinuous
import proof.Semantics.Graph.Clos5IswimContinuous

{- correctness of each pass -}
import proof.Correctness.Graph.SimplifyCorrect
import proof.Correctness.Graph.EncloseCorrect
import proof.Correctness.Graph.OptimizeCorrect
import proof.Correctness.Graph.ConcretizeCorrect
import proof.Correctness.Graph.DelayFiniteCommon
import proof.Correctness.Graph.DelayFiniteRel
import proof.Correctness.Graph.DelayApp
import proof.Correctness.Graph.DelayReflectFinite
import proof.Correctness.Graph.DelayPreserve
import proof.Correctness.Graph.GlobalizeCorrect
import proof.Correctness.Graph.RCOCorrect
import proof.Correctness.Graph.LiftLocalsCommon
import proof.Correctness.Graph.LiftLocalsCorrectK
import proof.Correctness.Graph.ExplicateCommon
import proof.Correctness.Graph.ExplicateCorrectK
import proof.Correctness.Graph.SelectCorrect

{- the end-to-end theorems (ISWIM → Clos5) -}
import proof.Correctness.Graph.CompilerCorrect

{- experiment: a direct semantics of Imp, and lift locals and explicate
   control against it (see papers/PLDI-2027/loc.md) -}
import proof.Semantics.Graph.ImpDirect
import proof.Correctness.Graph.LiftLocalsCorrect
import proof.Correctness.Graph.ExplicateCorrect

{- examples -}
import proof.Correctness.Graph.DelayClosedClosureExample
import proof.Correctness.Graph.ConcretizeExample
import proof.Correctness.Graph.EncloseExample
import proof.Correctness.Graph.PipelineExample
import proof.Correctness.Graph.CompilerExample
import proof.Compiler.Examples.SimplifyExample
import proof.Compiler.Examples.RCOExample
import proof.Compiler.Examples.LiftLocalsExample
import proof.Compiler.Examples.ExplicateExample
import proof.Compiler.Examples.SelectExample

{- ---------------------------------------------------------------------------
   proof/: the CEK machine + simulation development, independent of
   the graph model: forward simulations between small-step machines
   --------------------------------------------------------------------------- -}

{- the lemmas about runs and the forward simulations, at this compiler's
   observations -}
import proof.Semantics.CEK.Smallstep
import proof.Semantics.CEK.Simulation

{- correctness of each pass, and of the compiler into each language -}
import proof.Correctness.CEK.SimplifySim
import proof.Correctness.CEK.EncloseSim
import proof.Correctness.CEK.OptimizeSim
import proof.Correctness.CEK.ConcretizeSim
import proof.Correctness.CEK.DelaySim
import proof.Correctness.CEK.GlobalizeSim
import proof.Correctness.CEK.CompilerSim
import proof.Correctness.CEK.RCOSim
import proof.Correctness.CEK.LiftLocalsSim
import proof.Correctness.CEK.ExplicateSim
import proof.Correctness.CEK.SelectSim
import proof.Correctness.CEK.CompilerX86Sim

{- experiment: a direct backward simulation for delay, without
   determinism, for comparison (see papers/PLDI-2027/loc.md) -}
import proof.Semantics.CEK.Backward
import proof.Correctness.CEK.DelayBackSim

{- ---------------------------------------------------------------------------
   proof/: soundness and adequacy of the graph model for the ISWIM, Clos5
   and X86 machines, which connect the two developments
   --------------------------------------------------------------------------- -}

import proof.Adequacy.Common
import proof.Semantics.Graph.ISWIMContinuous
import proof.Adequacy.Soundness
import proof.Adequacy.LogRel
import proof.Adequacy.ISWIM
import proof.Adequacy.Clos5WF
import proof.Adequacy.CompileWF
import proof.Adequacy.Clos5Common
import proof.Adequacy.Values
import proof.Adequacy.Clos5Soundness
import proof.Adequacy.Clos5LogRel
import proof.Adequacy.Clos5
import proof.Adequacy.X86WF
import proof.Adequacy.X86Common
import proof.Adequacy.X86Soundness
import proof.Adequacy.X86LogRel
import proof.Adequacy.X86CompileWF
import proof.Adequacy.X86
import proof.Adequacy.EndToEnd

{- ---------------------------------------------------------------------------
   proof/: the clocked interpreter + value relations development:
   clock-for-clock proofs between clocked interpreters
   --------------------------------------------------------------------------- -}

{- clock-for-clock correctness, at this compiler's observations -}
import proof.Semantics.Interp.Clock

{- correctness of each pass, and of the compiler into each language -}
import proof.Correctness.Interp.SimplifyFuel
import proof.Correctness.Interp.EncloseFuel
import proof.Correctness.Interp.OptimizeFuel
import proof.Correctness.Interp.ConcretizeFuel
import proof.Correctness.Interp.DelayFuel
import proof.Correctness.Interp.GlobalizeFuel
import proof.Correctness.Interp.RCOFuel
import proof.Correctness.Interp.LiftLocalsFuel
import proof.Correctness.Interp.ExplicateFuel
import proof.Correctness.Interp.SelectFuel
import proof.Correctness.Interp.CompilerFuel

{- ---------------------------------------------------------------------------
   proof/: the reduction semantics + simulation development: forward
   simulations between reduction semantics by substitution, and from the
   Clos5 one to the machine of Imp (explicate control and select
   instructions, between the machines of Imp, CFG and X86, are the CEK
   development's, shared)
   --------------------------------------------------------------------------- -}

{- the values of each reduction semantics -}
import proof.Semantics.Reduction.Clos2
import proof.Semantics.Reduction.Clos3
import proof.Semantics.Reduction.Clos4
import proof.Semantics.Reduction.Clos5

{- correctness of each pass, and of the compiler into each language -}
import proof.Correctness.Reduction.SimplifyRed
import proof.Correctness.Reduction.EncloseRed
import proof.Correctness.Reduction.OptimizeRed
import proof.Correctness.Reduction.ConcretizeRed
import proof.Correctness.Reduction.DelayRed
import proof.Correctness.Reduction.GlobalizeRed
import proof.Correctness.Reduction.CompilerRed
import proof.Correctness.Reduction.RCORed
import proof.Correctness.Reduction.LiftLocalsRed
import proof.Correctness.Reduction.CompilerX86Red
