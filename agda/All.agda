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
import abt.Sig
import abt.Var
import abt.ScopedTuple
import abt.GSubst
import abt.AbstractBindingTree
import abt.Fold2

{- the languages -}
import Compiler.Lang.ISWIM
import Compiler.Lang.Clos2
import Compiler.Lang.Clos3
import Compiler.Lang.Clos4
import Compiler.Lang.Clos5
import Compiler.Lang.Uses
import Compiler.Lang.Rename

{- the passes -}
import Compiler.Compile.Enclose
import Compiler.Compile.Optimize
import Compiler.Compile.Concretize
import Compiler.Compile.Delay
import Compiler.Compile.Globalize

{- the graph model and the semantics of each language -}
import Compiler.Model.Graph.Domain.ISWIM.Domain
import Compiler.Model.Graph.Domain.ISWIM.Ops
import Compiler.Model.Graph.Domain.ISWIM.Continuity
import Compiler.Model.Graph.Sem.ISWIM
import Compiler.Model.Graph.Sem.Clos2Iswim
import Compiler.Model.Graph.Sem.Clos3Iswim
import Compiler.Model.Graph.Sem.Continuous
import Compiler.Model.Graph.Sem.ISWIMContinuous
import Compiler.Model.Graph.Sem.Clos3IswimContinuous
import Compiler.Model.Graph.Sem.Clos4Iswim
import Compiler.Model.Graph.Sem.Clos4IswimContinuous
import Compiler.Model.Graph.Sem.Clos5Iswim
import Compiler.Model.Graph.Sem.RenameSem

{- correctness of each pass -}
import Compiler.Model.Graph.Correctness.EncloseCorrect
import Compiler.Model.Graph.Correctness.OptimizeCorrect
import Compiler.Model.Graph.Correctness.ConcretizeCorrect
import Compiler.Model.Graph.Correctness.DelayFiniteCommon
import Compiler.Model.Graph.Correctness.DelayFiniteRel
import Compiler.Model.Graph.Correctness.DelayApp
import Compiler.Model.Graph.Correctness.DelayReflectFinite
import Compiler.Model.Graph.Correctness.DelayPreserve
import Compiler.Model.Graph.Correctness.GlobalizeCorrect

{- the end-to-end theorems (ISWIM → Clos5) -}
import Compiler.Model.Graph.Correctness.CompilerCorrect

{- examples -}
import Compiler.Model.Graph.Correctness.DelayClosedClosureExample
import Compiler.Model.Graph.Correctness.ConcretizeExample
import Compiler.Model.Graph.Correctness.EncloseExample
import Compiler.Model.Graph.Correctness.PipelineExample
import Compiler.Model.Graph.Correctness.CompilerExample

{- ---------------------------------------------------------------------------
   The operational (CompCert-style) development, independent of the graph
   model above: small-step machines and forward simulations.
   --------------------------------------------------------------------------- -}

{- shared by any operational semantics: observations, end-theorem shape -}
import Compiler.Operational.Observation

{- the generic framework: transition systems, forward simulations -}
import Compiler.Operational.Smallstep
import Compiler.Operational.Simulation

{- the machines -}
import Compiler.Operational.Machine.Common
import Compiler.Operational.Machine.ISWIM
import Compiler.Operational.Machine.Clos2
import Compiler.Operational.Machine.Clos3
import Compiler.Operational.Machine.Clos4
import Compiler.Operational.Machine.Clos5

{- correctness of each pass -}
import Compiler.Operational.Correctness.EncloseSim
import Compiler.Operational.Correctness.OptimizeSim
import Compiler.Operational.Correctness.ConcretizeSim
import Compiler.Operational.Correctness.DelaySim
import Compiler.Operational.Correctness.GlobalizeSim
{- the whole compiler, by composing the simulations of the passes -}
import Compiler.Operational.Correctness.CompilerSim

{- soundness and adequacy of the graph model for the ISWIM machine, which
   connect the two developments -}
import Compiler.Operational.Adequacy.Common
import Compiler.Operational.Adequacy.Soundness
import Compiler.Operational.Adequacy.LogRel
import Compiler.Operational.Adequacy.ISWIM

{- the same for the Clos5 machine, for well-formed programs (which the
   compiler produces), and the compiler's correctness in the graph model
   observed through the ISWIM and Clos5 machines -}
import Compiler.Operational.Adequacy.Scope
import Compiler.Operational.Adequacy.Clos5WF
import Compiler.Operational.Adequacy.CompileWF
import Compiler.Operational.Adequacy.Clos5Common
import Compiler.Operational.Adequacy.Clos5Continuous
import Compiler.Operational.Adequacy.Clos5Soundness
import Compiler.Operational.Adequacy.Clos5LogRel
import Compiler.Operational.Adequacy.Clos5
import Compiler.Operational.Adequacy.EndToEnd

{- experiment: a direct backward simulation for delay, without determinism,
   for comparison (see papers/PLDI-2027/loc.md) -}
import Compiler.Operational.Backward
import Compiler.Operational.Correctness.DelayBackSim

{- ---------------------------------------------------------------------------
   The CakeML-style (functional big-step, clocked) development: a clocked
   interpreter per language and clock-for-clock proofs of the passes.
   It shares only the observations with the CompCert-style development.
   --------------------------------------------------------------------------- -}

{- results, clocks, the end-theorem shape, clock-for-clock correctness -}
import Compiler.Functional.Clock

{- the interpreters -}
import Compiler.Functional.Interp.ISWIM
import Compiler.Functional.Interp.Clos2
import Compiler.Functional.Interp.Clos3
import Compiler.Functional.Interp.Clos4
import Compiler.Functional.Interp.Clos5

{- correctness of each pass -}
import Compiler.Functional.Correctness.EncloseFuel
import Compiler.Functional.Correctness.GlobalizeFuel
import Compiler.Functional.Correctness.ConcretizeFuel
