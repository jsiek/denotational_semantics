{-

  The closure-conversion compiler and its correctness proofs.

    ISWIM --annotate--> Clos1 --enclose--> Clos2 --optimize--> Clos2
          --concretize--> Clos3 --delay--> Clos4 --globalize--> Clos5

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
import Compiler.Lang.Clos1
import Compiler.Lang.Clos2
import Compiler.Lang.Clos3
import Compiler.Lang.Clos4
import Compiler.Lang.Clos5
import Compiler.Lang.Uses
import Compiler.Lang.Rename

{- the passes -}
import Compiler.Compile.Annotate
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
import Compiler.Model.Graph.Sem.Clos1Iswim
import Compiler.Model.Graph.Sem.Clos2Iswim
import Compiler.Model.Graph.Sem.Clos3Iswim
import Compiler.Model.Graph.Sem.Clos3IswimConsistent
import Compiler.Model.Graph.Sem.Clos3IswimContinuous
import Compiler.Model.Graph.Sem.Clos4Iswim
import Compiler.Model.Graph.Sem.Clos4IswimContinuous
import Compiler.Model.Graph.Sem.Clos5Iswim
import Compiler.Model.Graph.Sem.RenameSem

{- correctness of each pass -}
import Compiler.Model.Graph.Correctness.AnnotateCorrect
import Compiler.Model.Graph.Correctness.EncloseCorrect
import Compiler.Model.Graph.Correctness.OptimizeCorrect
import Compiler.Model.Graph.Correctness.ConcretizeCorrect
import Compiler.Model.Graph.Correctness.DelayFiniteCommon
import Compiler.Model.Graph.Correctness.DelayFiniteRel
import Compiler.Model.Graph.Correctness.DelayApp
import Compiler.Model.Graph.Correctness.DelayReflectFinite
import Compiler.Model.Graph.Correctness.DelayPreserveFinite
import Compiler.Model.Graph.Correctness.GlobalizeCorrect

{- the end-to-end theorems: CompilerCorrect (ISWIM → Clos5), built from
   PipelineCorrect (Clos1 → Clos4) and AnnotateCorrect (ISWIM → Clos4) -}
import Compiler.Model.Graph.Correctness.PipelineCorrect
import Compiler.Model.Graph.Correctness.CompilerCorrect

{- examples -}
import Compiler.Model.Graph.Correctness.DelayClosedClosureExample
import Compiler.Model.Graph.Correctness.ConcretizeExample
import Compiler.Model.Graph.Correctness.PipelineExample
import Compiler.Model.Graph.Correctness.AnnotateExample
import Compiler.Model.Graph.Correctness.CompilerExample
