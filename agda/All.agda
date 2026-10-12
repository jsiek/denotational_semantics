{-

  The closure-conversion compiler and its correctness proofs.

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  Check everything with

    agda --safe agda/All.agda

  (or make check, from the root of the repository).

-}

module All where

{- the parts of the abt library that we use -}
import Framework.abt.Sig
import Framework.abt.Var
import Framework.abt.ScopedTuple
import Framework.abt.GSubst
import Framework.abt.AbstractBindingTree
import Framework.abt.Fold2

{- language-independent infrastructure: lemmas about the syntax of any
   signature, list lookups, the graph model (values, operators,
   continuity), and the frameworks of the small-step and clocked styles -}
import Framework.Syntax.Uses
import Framework.Syntax.Rename
import Framework.Syntax.Scope
import proof.Framework.Syntax.ScopeRename
import Framework.ListUtil
import proof.Framework.GraphModel.RenameSem
import Framework.GraphModel.Domain
import Framework.GraphModel.Ops
import proof.Framework.GraphModel.Continuity
import proof.Framework.GraphModel.SemanticsUtil
import Framework.Iff
import Framework.Smallstep
import proof.Framework.Simulation
import Framework.Clocked

{- the languages -}
import Compiler.Lang.ISWIM
import Compiler.Lang.Clos2
import Compiler.Lang.Clos3
import Compiler.Lang.Clos4
import Compiler.Lang.Clos5
import Compiler.Lang.Mon
import Compiler.Lang.Imp
import Compiler.Lang.CFG
import Compiler.Lang.X86

{- the passes -}
import Compiler.Compile.Enclose
import Compiler.Compile.Optimize
import Compiler.Compile.Concretize
import Compiler.Compile.Delay
import Compiler.Compile.Globalize
import Compiler.Compile.RCO
import Compiler.Compile.LiftLocals
import Compiler.Compile.Explicate
import Compiler.Compile.Select
import Compiler.Compile.Pipeline

{- syntactic facts about the passes, used by both operational styles -}
import Compiler.Compile.EncloseScope
import proof.Compiler.Compile.GlobalizeTable
{- the compiler produces well-scoped Clos5 programs (Scoped), the
   precondition of both operational proofs of remove complex operands -}
import Compiler.Compile.PipelineScope

{- observations and the end-theorem shape, shared by both operational styles -}
import Compiler.Observation

{- the graph-model meaning of the primitives, and the semantics of each
   language -}
import Compiler.Model.Graph.Prim
import Compiler.Model.Graph.Sem.ISWIM
import Compiler.Model.Graph.Sem.Clos2Iswim
import Compiler.Model.Graph.Sem.Clos3Iswim
import proof.Compiler.Model.Graph.Sem.ISWIMContinuous
import proof.Compiler.Model.Graph.Sem.Clos3IswimContinuous
import Compiler.Model.Graph.Sem.Clos4Iswim
import proof.Compiler.Model.Graph.Sem.Clos4IswimContinuous
import Compiler.Model.Graph.Sem.Clos5Iswim
import proof.Compiler.Model.Graph.Sem.Clos5IswimContinuous
import Compiler.Model.Graph.Sem.Imp
import Compiler.Model.Graph.Sem.CFG
import Compiler.Model.Graph.Sem.X86
import Compiler.Model.Graph.Sem.ImpK
import proof.Compiler.Model.Graph.Sem.ImpDirect

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
{- the same two passes against the direct semantics of Imp -}
import proof.Compiler.Model.Graph.Correctness.LiftLocalsCorrect
import proof.Compiler.Model.Graph.Correctness.ExplicateCorrect

{- the end-to-end theorems (ISWIM → Clos5) -}
import proof.Compiler.Model.Graph.Correctness.CompilerCorrect

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
   The operational (CompCert-style) development, independent of the graph
   model above: small-step machines and forward simulations.
   --------------------------------------------------------------------------- -}

{- the framework (transition systems, forward simulations), at this
   compiler's observations -}
import Compiler.Operational.Smallstep
import proof.Compiler.Operational.Simulation

{- the machines -}
import Compiler.Operational.Machine.ISWIM
import Compiler.Operational.Machine.Clos2
import Compiler.Operational.Machine.Clos3
import Compiler.Operational.Machine.Clos4
import Compiler.Operational.Machine.Clos5
import Compiler.Operational.Machine.Imp
import Compiler.Operational.Machine.CFG
import Compiler.Operational.Machine.X86

{- correctness of each pass -}
import proof.Compiler.Operational.Correctness.EncloseSim
import proof.Compiler.Operational.Correctness.OptimizeSim
import proof.Compiler.Operational.Correctness.ConcretizeSim
import proof.Compiler.Operational.Correctness.DelaySim
import proof.Compiler.Operational.Correctness.GlobalizeSim
{- the whole compiler, by composing the simulations of the passes -}
import proof.Compiler.Operational.Correctness.CompilerSim
{- remove complex operands (Clos5 → Clos5), and the compiler into monadic
   normal form -}
import proof.Compiler.Operational.Correctness.RCOSim
{- lift locals (monadic Clos5 → Imp), and the compiler into Imp -}
import proof.Compiler.Operational.Correctness.LiftLocalsSim
{- explicate control (Imp → CFG), and the compiler into CFG -}
import proof.Compiler.Operational.Correctness.ExplicateSim
import proof.Compiler.Operational.Correctness.SelectSim

{- soundness and adequacy of the graph model for the ISWIM machine, which
   connect the two developments -}
import proof.Compiler.Operational.Adequacy.Common
import proof.Compiler.Operational.Adequacy.Soundness
import proof.Compiler.Operational.Adequacy.LogRel
import proof.Compiler.Operational.Adequacy.ISWIM

{- the same for the Clos5 machine, for well-formed programs (which the
   compiler produces), and the compiler's correctness in the graph model
   observed through the ISWIM and Clos5 machines -}
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

{- experiment: a direct backward simulation for delay, without determinism,
   for comparison (see papers/PLDI-2027/loc.md) -}
import proof.Compiler.Operational.Backward
import proof.Compiler.Operational.Correctness.DelayBackSim

{- ---------------------------------------------------------------------------
   The CakeML-style (functional big-step, clocked) development: a clocked
   interpreter per language and clock-for-clock proofs of the passes.
   It shares with the CompCert-style development only the neutral modules
   above (observations, list lookups, scoping, renaming and table lemmas).
   --------------------------------------------------------------------------- -}

{- results, clocks, the end-theorem shape, clock-for-clock correctness,
   at this compiler's observations -}
import Compiler.Functional.Clock

{- the interpreters -}
import Compiler.Functional.Interp.ISWIM
import Compiler.Functional.Interp.Clos2
import Compiler.Functional.Interp.Clos3
import Compiler.Functional.Interp.Clos4
import Compiler.Functional.Interp.Clos5
import Compiler.Functional.Interp.Imp
import Compiler.Functional.Interp.CFG
import Compiler.Functional.Interp.X86

{- correctness of each pass -}
import proof.Compiler.Functional.Correctness.EncloseFuel
import proof.Compiler.Functional.Correctness.OptimizeFuel
import proof.Compiler.Functional.Correctness.ConcretizeFuel
import proof.Compiler.Functional.Correctness.DelayFuel
import proof.Compiler.Functional.Correctness.GlobalizeFuel
import proof.Compiler.Functional.Correctness.RCOFuel
import proof.Compiler.Functional.Correctness.LiftLocalsFuel
import proof.Compiler.Functional.Correctness.ExplicateFuel
import proof.Compiler.Functional.Correctness.SelectFuel

{- correctness of the whole compiler -}
import proof.Compiler.Functional.Correctness.CompilerFuel
