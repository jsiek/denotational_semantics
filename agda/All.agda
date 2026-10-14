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
import Theorems.GraphErrors
import Theorems.Typed

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
import proof.Framework.Syntax.EnvRel
import proof.Framework.GraphModel.SetsAsPredicates
import proof.Framework.GraphModel.DOpSig
import proof.Framework.GraphModel.DenotProperties
import proof.Framework.GraphModel.Env
import proof.Framework.GraphModel.Semantics
import proof.Framework.GraphModel.RenameSem
import proof.Framework.GraphModel.Domain
import proof.Framework.GraphModel.OpsBase
import proof.Framework.GraphModel.ContinuityBase
import proof.Framework.GraphModel.SemanticsCore
import proof.Framework.GraphModel.SemanticsUses
import proof.Framework.GraphModel.Ops
import proof.Framework.GraphModel.Continuity
import proof.Framework.GraphModel.SemanticsUtil
import proof.Framework.GraphModel.ErrorMonad
import proof.Framework.GraphModel.DomainUtilBase
import proof.Framework.GraphModel.DomainUtil
import proof.Framework.Smallstep
import proof.Framework.Runs
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
import proof.Semantics.Graph.Clos4Iswim
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
import proof.Compiler.Examples.TypedExample
import proof.Compiler.Examples.TypedPipelineExample

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

{- ---------------------------------------------------------------------------
   proof/: the graph model with errors, built from an error monad on
   𝒫 Value (Framework/GraphModel/ErrorMonad.agda): the semantics of every
   language in which an error denotes ω, every pass proved correct in it,
   and its adequacy for the ISWIM, Clos5 and X86 machines
   --------------------------------------------------------------------------- -}

import proof.Semantics.GraphErr.Prim
import proof.Semantics.GraphErr.ISWIM
import proof.Semantics.GraphErr.Clos2
import proof.Semantics.GraphErr.Clos3
import proof.Semantics.GraphErr.Clos4
import proof.Semantics.GraphErr.Clos5
import Semantics.GraphErr.ImpK
import Semantics.GraphErr.CFG
import Semantics.GraphErr.X86
import proof.Framework.GraphModel.Strict
import proof.Framework.GraphModel.Laws
import proof.Correctness.GraphErr.SimplifyCorrect
import proof.Correctness.GraphErr.EncloseCorrect
import proof.Correctness.GraphErr.OptimizeCorrect
import proof.Correctness.GraphErr.ConcretizeCorrect
import proof.Correctness.GraphErr.DelayRel
import proof.Correctness.GraphErr.DelayApp
import proof.Correctness.GraphErr.DelayReflect
import proof.Correctness.GraphErr.DelayPreserve
import proof.Correctness.GraphErr.GlobalizeCorrect
import proof.Correctness.GraphErr.RCOCorrect
import proof.Correctness.GraphErr.LiftLocalsCorrect
import proof.Correctness.GraphErr.ExplicateCorrect
import proof.Correctness.GraphErr.SelectCorrect
import proof.Correctness.GraphErr.CompilerCorrect
import proof.Adequacy.GraphErr.Soundness
import proof.Adequacy.GraphErr.LogRel
import proof.Adequacy.GraphErr.ISWIM
import proof.Adequacy.GraphErr.Simplify
import proof.Adequacy.GraphErr.Clos5WF
import proof.Adequacy.GraphErr.Clos5Common
import proof.Adequacy.GraphErr.Clos5Soundness
import proof.Adequacy.GraphErr.Clos5LogRel
import proof.Adequacy.GraphErr.Clos5
import proof.Adequacy.GraphErr.X86WF
import proof.Adequacy.GraphErr.X86Common
import proof.Adequacy.GraphErr.X86Consistent
import proof.Adequacy.GraphErr.X86Soundness
import proof.Adequacy.GraphErr.X86LogRel
import proof.Adequacy.GraphErr.X86
import proof.Adequacy.GraphErr.EndToEnd

{- the typed pilot (see papers/PLDI-2027/loc.md): cast insertion into the
   statically typed ISWIMᵀ–Clos4ᵀ, the typed closure-conversion passes,
   and their proofs on the CEK machines and in the graph model with
   errors; the statements are Theorems/Typed.agda -}
import proof.Correctness.Typed.CEK.CastSim
import proof.Correctness.Typed.CEK.EncloseSim
import proof.Correctness.Typed.CEK.OptimizeSim
import proof.Correctness.Typed.CEK.ConcretizeSim
import proof.Correctness.Typed.CEK.DelaySim
import proof.Correctness.Typed.CEK.CompilerSim
import proof.Correctness.Typed.GraphErr.CastCorrect
import proof.Correctness.Typed.GraphErr.EncloseCorrect
import proof.Correctness.Typed.GraphErr.OptimizeCorrect
import proof.Correctness.Typed.GraphErr.ConcretizeCorrect
import proof.Correctness.Typed.GraphErr.DelayCorrect
import proof.Correctness.Typed.GraphErr.CompilerCorrect

{- the typed pipeline, phase 1: the typed compiler to X86
   (Compiler/Typed/Pipeline.agda), cast insertion on closed programs, and
   the specifications of each column's statements (phase 2) -}
import Compiler.Typed.Pipeline
import proof.Compiler.Typed.CastScope
import proof.Compiler.Typed.GlobalizeOlder
import proof.Spec.Typed.Denotational
import proof.Spec.Typed.Simulation
import proof.Spec.Typed.Interpreter
import proof.Spec.Typed.Reduction
import proof.Spec.Typed.GraphErrors
import proof.Spec.Typed.Adequacy

{- the typed pipeline, phase 2, CEK machines + simulations: the machines
   of Clos5ᵀ, Impᵀ and CFGᵀ (also used by the reduction column and
   adequacy) -}
import Semantics.CEK.Typed.Clos5
import Semantics.CEK.Typed.Imp
import Semantics.CEK.Typed.CFG
import proof.Compiler.Typed.SelectFacts
import Theorems.Typed.Simulation

{- the typed pipeline, phase 2, clocked interpreters + value relations:
   the statements -}
import Theorems.Typed.Interpreter

{- the typed pipeline, phase 2, the plain graph model and its adequacy:
   the statements are Theorems/Typed/{Denotational,Adequacy}.agda -}
import Theorems.Typed.Denotational
import Theorems.Typed.Adequacy

{- the typed pipeline, phase 2, the graph model with errors -}
import proof.Correctness.Typed.GraphErr.GlobalizeCorrect
import proof.Correctness.Typed.GraphErr.RCOCorrect
import proof.Correctness.Typed.GraphErr.LiftLocalsCorrect
import proof.Correctness.Typed.GraphErr.ExplicateCorrect
import proof.Correctness.Typed.GraphErr.SelectCheck
import proof.Semantics.GraphErr.Typed.CFG
