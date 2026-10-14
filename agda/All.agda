{-

  The compiler and its correctness proofs, in five styles.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86

  The intermediate languages (Language/Typed/) are intrinsically typed;
  the source, ISWIM, and the target, X86, are untyped. The untyped
  pipeline that preceded this one is preserved in Untyped/ (see
  Untyped/All.agda), and checked too.

  Check everything with

    agda --safe agda/All.agda

  (or make check, from the root of the repository, which also greps for
  postulates and pragmas). See README.md for the layout: the theorem
  statements (Theorems/) and the definitions they use (everything outside
  proof/) are the audit surface; proof/ holds the proofs.

  This file imports the theorem files, which reach the whole audit
  surface, every module of proof/, and the preserved untyped pipeline.

-}

module All where

{- ---------------------------------------------------------------------------
   The public theorem statements
   --------------------------------------------------------------------------- -}

import Theorems.Denotational
import Theorems.Simulation
import Theorems.Interpreter
import Theorems.Reduction
import Theorems.GraphErrors
import Theorems.Adequacy

{- a pilot: the typed assembly language X86ᵀ as the target (not in the main
   theorems) -}
import Theorems.TAL

{- an assurance (not in the totals): erasing X86ᵀ to X86 keeps the meaning
   of every program, in the CEK machines -}
import Theorems.X86Erasure

{- ---------------------------------------------------------------------------
   The untyped pipeline, preserved
   --------------------------------------------------------------------------- -}

import Untyped.All

{- ---------------------------------------------------------------------------
   proof/: language-independent lemmas: about tuples of the abt extract,
   lists, the syntax of any signature (renaming, scoping, uses,
   substitution), sets and environments, the graph model (values,
   operators, continuity, the error monad, intrinsically typed syntax),
   and the small-step, reduction and clocked frameworks
   --------------------------------------------------------------------------- -}

import proof.Framework.Both
import proof.Framework.Clocked
import proof.Framework.GraphModel.Continuity
import proof.Framework.GraphModel.ContinuityBase
import proof.Framework.GraphModel.DOpSig
import proof.Framework.GraphModel.DenotProperties
import proof.Framework.GraphModel.Domain
import proof.Framework.GraphModel.DomainUtil
import proof.Framework.GraphModel.DomainUtilBase
import proof.Framework.GraphModel.Env
import proof.Framework.GraphModel.ErrorMonad
import proof.Framework.GraphModel.Laws
import proof.Framework.GraphModel.Ops
import proof.Framework.GraphModel.OpsBase
import proof.Framework.GraphModel.RenameSem
import proof.Framework.GraphModel.Semantics
import proof.Framework.GraphModel.SemanticsCore
import proof.Framework.GraphModel.SemanticsUses
import proof.Framework.GraphModel.SemanticsUtil
import proof.Framework.GraphModel.SetsAsPredicates
import proof.Framework.GraphModel.Strict
import proof.Framework.GraphModel.TypedBinders
import proof.Framework.GraphModel.TypedGraph
import proof.Framework.GraphModel.TypedGuard
import proof.Framework.GraphModel.TypedOk
import proof.Framework.GraphModel.TypedOkBase
import proof.Framework.ListUtil
import proof.Framework.Lookup
import proof.Framework.Reduction
import proof.Framework.ReductionVec
import proof.Framework.Runs
import proof.Framework.Simulation
import proof.Framework.Smallstep
import proof.Framework.Syntax.EnvRel
import proof.Framework.Syntax.Rename
import proof.Framework.Syntax.Scope
import proof.Framework.Syntax.ScopeRename
import proof.Framework.Syntax.ScopeSubst
import proof.Framework.Syntax.Subst
import proof.Framework.Syntax.SubstRel
import proof.Framework.Syntax.Uses
import proof.Framework.VecProj
import proof.Framework.VecSelect
import proof.Framework.abt.ScopedTuple

{- ---------------------------------------------------------------------------
   proof/: syntactic facts about the passes: simplify, cast insertion on
   closed programs, globalize's references to older definitions, and the
   definitions, labels and frames that select instructions relies on
   --------------------------------------------------------------------------- -}

import proof.Compiler.CastScope
import proof.Compiler.GlobalizeOlder
import proof.Compiler.SelectFacts
import proof.Compiler.SimplifyFacts
import proof.Compiler.SimplifyScope

{- ---------------------------------------------------------------------------
   proof/: the plain graph model: the lemmas about the semantics of each
   language and the correctness of each pass
   --------------------------------------------------------------------------- -}

import proof.Correctness.Graph.CastCorrect
import proof.Correctness.Graph.CompilerCorrect
import proof.Correctness.Graph.ConcretizeCorrect
import proof.Correctness.Graph.DelayCorrect
import proof.Correctness.Graph.DelayPreserve
import proof.Correctness.Graph.DelayReflect
import proof.Correctness.Graph.DelayRel
import proof.Correctness.Graph.EncloseCorrect
import proof.Correctness.Graph.ExplicateCorrect
import proof.Correctness.Graph.GlobalizeCorrect
import proof.Correctness.Graph.LiftLocalsCorrect
import proof.Correctness.Graph.OptimizeCorrect
import proof.Correctness.Graph.RCOCorrect
import proof.Correctness.Graph.SelectCorrect
import proof.Correctness.Graph.SimplifyCorrect
import proof.Semantics.Graph.ISWIM
import proof.Semantics.Graph.ISWIMContinuous
import proof.Semantics.Graph.Prim
import proof.Semantics.Graph.Typed.CFG
import proof.Semantics.Graph.Typed.Clos2
import proof.Semantics.Graph.Typed.Clos3
import proof.Semantics.Graph.Typed.Clos4
import proof.Semantics.Graph.Typed.Clos5
import proof.Semantics.Graph.Typed.Ops
import proof.Semantics.Graph.X86

{- ---------------------------------------------------------------------------
   proof/: the CEK machines + simulations
   --------------------------------------------------------------------------- -}

import proof.Correctness.CEK.CastSim
import proof.Correctness.CEK.CastSimLemmas
import proof.Correctness.CEK.Clos5Common
import proof.Correctness.CEK.Common
import proof.Correctness.CEK.ConcretizeSim
import proof.Correctness.CEK.DelaySim
import proof.Correctness.CEK.EncloseSim
import proof.Correctness.CEK.ExplicateSim
import proof.Correctness.CEK.GlobalizeSim
import proof.Correctness.CEK.LiftLocalsSim
import proof.Correctness.CEK.OptimizeSim
import proof.Correctness.CEK.PipelineSim
import proof.Correctness.CEK.RCOSim
import proof.Correctness.CEK.SelectSim
import proof.Correctness.CEK.SimplifySim
import proof.Semantics.CEK.Simulation
import proof.Semantics.CEK.Smallstep

{- ---------------------------------------------------------------------------
   proof/: the clocked interpreters + value relations
   --------------------------------------------------------------------------- -}

import proof.Correctness.Interp.CastFuel
import proof.Correctness.Interp.CompilerFuel
import proof.Correctness.Interp.ConcretizeFuel
import proof.Correctness.Interp.DelayFuel
import proof.Correctness.Interp.EncloseFuel
import proof.Correctness.Interp.ExplicateFuel
import proof.Correctness.Interp.GlobalizeFuel
import proof.Correctness.Interp.LiftLocalsFuel
import proof.Correctness.Interp.OptimizeFuel
import proof.Correctness.Interp.RCOFuel
import proof.Correctness.Interp.SelectFuel
import proof.Correctness.Interp.SimplifyFuel
import proof.Semantics.Interp.Clock
import proof.Semantics.Interp.Typed.Clos5
import proof.Semantics.Interp.Typed.Rel

{- ---------------------------------------------------------------------------
   proof/: the reduction semantics + simulations (explicate control and
   select instructions are the CEK column's)
   --------------------------------------------------------------------------- -}

import proof.Correctness.Reduction.CastRed
import proof.Correctness.Reduction.ConcretizeRed
import proof.Correctness.Reduction.DelayRed
import proof.Correctness.Reduction.EncloseRed
import proof.Correctness.Reduction.GlobalizeRed
import proof.Correctness.Reduction.LiftLocalsRed
import proof.Correctness.Reduction.OptimizeRed
import proof.Correctness.Reduction.PipelineRed
import proof.Correctness.Reduction.RCORed
import proof.Correctness.Reduction.SimplifyRed
import proof.Semantics.Reduction.Typed.Clos2
import proof.Semantics.Reduction.Typed.Clos3
import proof.Semantics.Reduction.Typed.Clos4
import proof.Semantics.Reduction.Typed.Clos5
import proof.Semantics.Reduction.Typed.ISWIM

{- ---------------------------------------------------------------------------
   proof/: the graph model with errors
   --------------------------------------------------------------------------- -}

import proof.Correctness.GraphErr.CastCorrect
import proof.Correctness.GraphErr.CompilerCorrect
import proof.Correctness.GraphErr.ConcretizeCorrect
import proof.Correctness.GraphErr.DelayCorrect
import proof.Correctness.GraphErr.DelayPreserve
import proof.Correctness.GraphErr.DelayReflect
import proof.Correctness.GraphErr.DelayRel
import proof.Correctness.GraphErr.EncloseCorrect
import proof.Correctness.GraphErr.ExplicateCorrect
import proof.Correctness.GraphErr.GlobalizeCorrect
import proof.Correctness.GraphErr.LiftLocalsCorrect
import proof.Correctness.GraphErr.OptimizeCorrect
import proof.Correctness.GraphErr.RCOCorrect
import proof.Correctness.GraphErr.SelectCheck
import proof.Correctness.GraphErr.SelectCheckOk
import proof.Correctness.GraphErr.SelectCorrect
import proof.Correctness.GraphErr.SelectPreserve
import proof.Correctness.GraphErr.SelectReflect
import proof.Correctness.GraphErr.SelectRel
import proof.Correctness.GraphErr.SelectX86
import proof.Correctness.GraphErr.SimplifyCorrect
import proof.Semantics.GraphErr.ISWIM
import proof.Semantics.GraphErr.Prim
import proof.Semantics.GraphErr.Typed.CFG
import proof.Semantics.GraphErr.Typed.Clos2
import proof.Semantics.GraphErr.Typed.Clos3
import proof.Semantics.GraphErr.Typed.Clos4
import proof.Semantics.GraphErr.Typed.Clos5
import proof.Semantics.GraphErr.Typed.Imp

{- ---------------------------------------------------------------------------
   proof/: adequacy of the plain graph model (ISWIM, Clos5ᵀ and X86
   machines) and of the graph model with errors (ISWIM and X86 machines;
   Clos5ᵀ derived from the CEK column's simulation)
   --------------------------------------------------------------------------- -}

import proof.Adequacy.Clos5
import proof.Adequacy.Clos5Common
import proof.Adequacy.Clos5LogRel
import proof.Adequacy.Clos5Soundness
import proof.Adequacy.Common
import proof.Adequacy.EndToEnd
import proof.Adequacy.GraphErr.Agree
import proof.Adequacy.GraphErr.EndToEnd
import proof.Adequacy.GraphErr.ISWIM
import proof.Adequacy.GraphErr.LogRel
import proof.Adequacy.GraphErr.Simplify
import proof.Adequacy.GraphErr.Soundness
import proof.Adequacy.GraphErr.X86
import proof.Adequacy.GraphErr.X86Common
import proof.Adequacy.GraphErr.X86Consistent
import proof.Adequacy.GraphErr.X86LogRel
import proof.Adequacy.GraphErr.X86Soundness
import proof.Adequacy.GraphErr.X86WF
import proof.Adequacy.ISWIM
import proof.Adequacy.LogRel
import proof.Adequacy.Soundness
import proof.Adequacy.Values
import proof.Adequacy.X86
import proof.Adequacy.X86Common
import proof.Adequacy.X86CompileWF
import proof.Adequacy.X86LogRel
import proof.Adequacy.X86Refs
import proof.Adequacy.X86Soundness
import proof.Adequacy.X86WF

{- ---------------------------------------------------------------------------
   examples (smoke tests)
   --------------------------------------------------------------------------- -}

import proof.Compiler.Examples.CastExample
import proof.Compiler.Examples.PipelineExample
import proof.Compiler.Examples.SimplifyExample
