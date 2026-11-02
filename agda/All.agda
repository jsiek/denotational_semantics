{-

  Everything that make check checks: the FPC compiler of the PLDI 2027
  paper (FPC/, see FPC/All.agda and FPC/README.md), the ISWIM compilers
  (ISWIM/, see ISWIM/All.agda), and the modules they share (the
  language-independent frameworks, Framework/ and proof/Framework/, and
  the primitives, observations and framework instances directly under
  agda/).

  Check everything with

    agda --safe agda/All.agda

  (or make check, from the root of the repository, which also greps for
  postulates and pragmas). See README.md for the layout. The
  Scott-domain column of FPC needs TypeTopology and is checked from
  AllScott.agda instead (make check-scott).

-}

module All where

{- ---------------------------------------------------------------------------
   The ISWIM compilers: the typed pipeline and the untyped one that
   preceded it
   --------------------------------------------------------------------------- -}

import ISWIM.All

{- ---------------------------------------------------------------------------
   The FPC compiler (the compiler of the PLDI 2027 paper): FPC, a typed
   λ-calculus with iso-recursive types, and its compiler to X86μ, in four
   of the five styles (Scott domains: AllScott.agda), with its theorem
   statements in FPC/Theorems/ (see
   FPC/All.agda and FPC/README.md), and the experiments on it that are not
   part of the paper (FPC/Experiments.agda)
   --------------------------------------------------------------------------- -}

import FPC.All
import FPC.Experiments

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
import proof.Framework.GraphModel.ErrorPrelude
import proof.Framework.GraphModel.Laws
import proof.Framework.GraphModel.Ops
import proof.Framework.GraphModel.OpsBase
import proof.Framework.GraphModel.Prelude
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
import proof.Framework.VecUtil
import proof.Framework.abt.ScopedTuple

{- ---------------------------------------------------------------------------
   proof/: the lemmas of the shared modules: the meaning of the primitives
   in the graph model, and the instances of the small-step and clocked
   frameworks at the compilers' observations
   --------------------------------------------------------------------------- -}

import proof.Semantics.Graph.Prim
import proof.Semantics.CEK.Simulation
import proof.Semantics.CEK.Smallstep
import proof.Semantics.Interp.Clock
