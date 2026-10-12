{-

  The closure-conversion compiler and its correctness proofs.

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
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

import proof.Compiler.Compile.EncloseScope
import proof.Compiler.Compile.GlobalizeTable
import proof.Compiler.Compile.PipelineScope

{- ---------------------------------------------------------------------------
   proof/: the denotational (graph-model) development
   --------------------------------------------------------------------------- -}

{- the monotonicity, consistency and continuity of the primitives and of
   the semantics of each language -}
import proof.Compiler.Model.Graph.Prim
import proof.Compiler.Model.Graph.Sem.ISWIM
import proof.Compiler.Model.Graph.Sem.Clos2Iswim
import proof.Compiler.Model.Graph.Sem.Clos3Iswim
import proof.Compiler.Model.Graph.Sem.Clos3IswimContinuous
import proof.Compiler.Model.Graph.Sem.Clos4Iswim
import proof.Compiler.Model.Graph.Sem.Clos4IswimContinuous
import proof.Compiler.Model.Graph.Sem.Clos5IswimContinuous

{- correctness of each pass -}
import proof.Compiler.Model.Graph.Correctness.EncloseCorrect
import proof.Compiler.Model.Graph.Correctness.OptimizeCorrect
import proof.Compiler.Model.Graph.Correctness.ConcretizeCorrect
import proof.Compiler.Model.Graph.Correctness.DelayFiniteCommon
import proof.Compiler.Model.Graph.Correctness.DelayFiniteRel
import proof.Compiler.Model.Graph.Correctness.DelayApp
import proof.Compiler.Model.Graph.Correctness.DelayReflectFinite
import proof.Compiler.Model.Graph.Correctness.DelayPreserve
import proof.Compiler.Model.Graph.Correctness.GlobalizeCorrect
import proof.Compiler.Model.Graph.Correctness.RCOCorrect
import proof.Compiler.Model.Graph.Correctness.LiftLocalsCommon
import proof.Compiler.Model.Graph.Correctness.LiftLocalsCorrectK
import proof.Compiler.Model.Graph.Correctness.ExplicateCommon
import proof.Compiler.Model.Graph.Correctness.ExplicateCorrectK
import proof.Compiler.Model.Graph.Correctness.SelectCorrect

{- the end-to-end theorems (ISWIM → Clos5) -}
import proof.Compiler.Model.Graph.Correctness.CompilerCorrect

{- experiment: a direct semantics of Imp, and lift locals and explicate
   control against it (see papers/PLDI-2027/loc.md) -}
import proof.Compiler.Model.Graph.Sem.ImpDirect
import proof.Compiler.Model.Graph.Correctness.LiftLocalsCorrect
import proof.Compiler.Model.Graph.Correctness.ExplicateCorrect

{- examples -}
import proof.Compiler.Model.Graph.Correctness.DelayClosedClosureExample
import proof.Compiler.Model.Graph.Correctness.ConcretizeExample
import proof.Compiler.Model.Graph.Correctness.EncloseExample
import proof.Compiler.Model.Graph.Correctness.PipelineExample
import proof.Compiler.Model.Graph.Correctness.CompilerExample
import proof.Compiler.Compile.Examples.RCOExample
import proof.Compiler.Compile.Examples.LiftLocalsExample
import proof.Compiler.Compile.Examples.ExplicateExample
import proof.Compiler.Compile.Examples.SelectExample

{- ---------------------------------------------------------------------------
   proof/: the CEK machine + simulation development, independent of
   the graph model: forward simulations between small-step machines
   --------------------------------------------------------------------------- -}

{- the lemmas about runs and the forward simulations, at this compiler's
   observations -}
import proof.Compiler.Operational.Smallstep
import proof.Compiler.Operational.Simulation

{- correctness of each pass, and of the compiler into each language -}
import proof.Compiler.Operational.Correctness.EncloseSim
import proof.Compiler.Operational.Correctness.OptimizeSim
import proof.Compiler.Operational.Correctness.ConcretizeSim
import proof.Compiler.Operational.Correctness.DelaySim
import proof.Compiler.Operational.Correctness.GlobalizeSim
import proof.Compiler.Operational.Correctness.CompilerSim
import proof.Compiler.Operational.Correctness.RCOSim
import proof.Compiler.Operational.Correctness.LiftLocalsSim
import proof.Compiler.Operational.Correctness.ExplicateSim
import proof.Compiler.Operational.Correctness.SelectSim

{- experiment: a direct backward simulation for delay, without
   determinism, for comparison (see papers/PLDI-2027/loc.md) -}
import proof.Compiler.Operational.Backward
import proof.Compiler.Operational.Correctness.DelayBackSim

{- ---------------------------------------------------------------------------
   proof/: soundness and adequacy of the graph model for the ISWIM, Clos5
   and X86 machines, which connect the two developments
   --------------------------------------------------------------------------- -}

import proof.Compiler.Operational.Adequacy.Common
import proof.Compiler.Model.Graph.Sem.ISWIMContinuous
import proof.Compiler.Operational.Adequacy.Soundness
import proof.Compiler.Operational.Adequacy.LogRel
import proof.Compiler.Operational.Adequacy.ISWIM
import proof.Compiler.Operational.Adequacy.Clos5WF
import proof.Compiler.Operational.Adequacy.CompileWF
import proof.Compiler.Operational.Adequacy.Clos5Common
import proof.Compiler.Operational.Adequacy.Values
import proof.Compiler.Operational.Adequacy.Clos5Soundness
import proof.Compiler.Operational.Adequacy.Clos5LogRel
import proof.Compiler.Operational.Adequacy.Clos5
import proof.Compiler.Operational.Adequacy.X86WF
import proof.Compiler.Operational.Adequacy.X86Common
import proof.Compiler.Operational.Adequacy.X86Soundness
import proof.Compiler.Operational.Adequacy.X86LogRel
import proof.Compiler.Operational.Adequacy.X86CompileWF
import proof.Compiler.Operational.Adequacy.X86
import proof.Compiler.Operational.Adequacy.EndToEnd

{- ---------------------------------------------------------------------------
   proof/: the clocked interpreter + value relations development:
   clock-for-clock proofs between clocked interpreters
   --------------------------------------------------------------------------- -}

{- clock-for-clock correctness, at this compiler's observations -}
import proof.Compiler.Functional.Clock

{- correctness of each pass, and of the compiler into each language -}
import proof.Compiler.Functional.Correctness.EncloseFuel
import proof.Compiler.Functional.Correctness.OptimizeFuel
import proof.Compiler.Functional.Correctness.ConcretizeFuel
import proof.Compiler.Functional.Correctness.DelayFuel
import proof.Compiler.Functional.Correctness.GlobalizeFuel
import proof.Compiler.Functional.Correctness.RCOFuel
import proof.Compiler.Functional.Correctness.LiftLocalsFuel
import proof.Compiler.Functional.Correctness.ExplicateFuel
import proof.Compiler.Functional.Correctness.SelectFuel
import proof.Compiler.Functional.Correctness.CompilerFuel

{- ---------------------------------------------------------------------------
   proof/: the reduction semantics + simulation development: forward
   simulations between reduction semantics by substitution (and the
   machines of Imp, CFG and X86, shared with the CEK development)
   --------------------------------------------------------------------------- -}

{- the values of each reduction semantics -}
import proof.Compiler.Reduction.Clos2
import proof.Compiler.Reduction.Clos3
import proof.Compiler.Reduction.Clos4
import proof.Compiler.Reduction.Clos5

{- correctness of each pass, and of the compiler into each language -}
import proof.Compiler.Reduction.Correctness.EncloseRed
import proof.Compiler.Reduction.Correctness.OptimizeRed
import proof.Compiler.Reduction.Correctness.ConcretizeRed
import proof.Compiler.Reduction.Correctness.DelayRed
import proof.Compiler.Reduction.Correctness.GlobalizeRed
import proof.Compiler.Reduction.Correctness.CompilerRed
