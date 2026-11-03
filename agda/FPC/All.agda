{-

  FPC, Plotkin's Fixed Point Calculus, with iso-recursive types (no
  recursion construct, no errors) and its compiler to the typed assembly
  language X86μ (the paper's Instrμ), proved correct in five styles: the
  development of the PLDI 2027 paper. FPC/README.md is the road map from
  the paper to this code.

    FPC --simplify--> FPC --capture--> Closμ --prune--> Closμ
           --concretize--> EnvClosμ --split--> PairClosμ
           --hoist--> GlobalFunμ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

  The paper counts eight passes, because it groups capture, prune and
  concretize as one pass, enclose.

  The theorem statements are in FPC/Theorems/, one file per style, each
  theorem with its type written out and defined as the corresponding
  theorem of FPC/proof/; they and the definitions they use (modules
  outside FPC/proof/) are FPC's audit surface.

  * graph model: FPC/Theorems/CorrectWrtGraphModel.agda (Theorem 4.1 and Lemma 4.6),
    proved in FPC/proof/Correctness/GraphModel/, with split by the
    approximant logical relation (SplitRel.agda);
  * abstract machines + simulation: FPC/Theorems/CorrectWrtAbstractMachines.agda
    (Proposition F.2), FPC/proof/Correctness/AbstractMachines/;
  * clocked interpreters + value relations:
    FPC/Theorems/CorrectWrtClockedInterpreters.agda (Proposition F.1),
    FPC/proof/Correctness/ClockedInterpreters/;
  * reduction semantics + simulation:
    FPC/Theorems/CorrectWrtReductionSemantics.agda (Proposition F.3),
    FPC/proof/Correctness/ReductionSemantics/;
  * Scott domains: FPC/Theorems/CorrectWrtScottDomains.agda (Theorem 4.2),
    FPC/proof/Correctness/ScottDomains/; it needs TypeTopology, so it is
    checked from agda/AllScott.agda (make check-scott), not from here,
    as is the Scott-domain half of Proposition 5.1
    (FPC/Theorems/ScottDomainsAdequateWrtClockedInterpreters.agda, FPC/proof/Adequacy/ScottDomains/);
  * adequacy of the graph model for the clocked interpreters of FPC
    and X86μ: FPC/Theorems/GraphModelAdequateWrtClockedInterpreters.agda (Proposition 5.1),
    FPC/proof/Adequacy/; the same against the
    abstract machines instead: FPC/Theorems/GraphModelAdequateWrtAbstractMachines.agda,
    FPC/proof/Adequacy/AbstractMachines/; and another, against FPC's
    reduction semantics: FPC/Theorems/GraphModelAdequateWrtReductionSemantics.agda,
    FPC/proof/Adequacy/ReductionSemantics/;
  * the two Agda checks of the paper's §4.2 ("Design alternatives: which sides to relate"):
    a finite source side cannot satisfy the function clause of split's
    relation (FPC/proof/Correctness/GraphModel/SplitDesignFiniteSource.agda),
    and split's relation on target sets of bounded depth is the
    relation on their finite sublists
    (FPC/proof/Correctness/GraphModel/SplitDesignBoundedSets.agda).

  The experiment of mixing semantics is not part of the paper; it is
  checked from FPC/Experiments.agda.

  The example programs of FPC/Examples.agda run on FPC's clocked
  interpreter, and FPC/README.md lists which interpreter clause each
  one exercises.

  agda/FPC/ mirrors agda/ISWIM/: FPC/X.agda corresponds to ISWIM/X.agda
  (with ISWIM/Language/Typed/ as FPC/Language/ and
  ISWIM/Semantics/<style>/Typed/ as FPC/Semantics/<style>/), and the
  module FPC.X to ISWIM.X. It reuses the
  frameworks of agda/Framework/ unchanged; FPC/Framework/AllUtil.agda
  (with FPC/proof/Framework/AllProp.agda) adds heterogeneous vectors
  (All), which the lists of types of FPC's contexts and tuples need.

-}

module FPC.All where

import FPC.Theorems.CorrectWrtGraphModel
import FPC.Theorems.CorrectWrtAbstractMachines
import FPC.Theorems.CorrectWrtClockedInterpreters
import FPC.Theorems.CorrectWrtReductionSemantics
import FPC.Theorems.GraphModelAdequateWrtClockedInterpreters
import FPC.Theorems.GraphModelAdequateWrtAbstractMachines
import FPC.Theorems.GraphModelAdequateWrtReductionSemantics
import FPC.proof.Correctness.GraphModel.CompilerCorrect
import FPC.proof.Correctness.AbstractMachines.PipelineSim
import FPC.proof.Correctness.ClockedInterpreters.CompilerFuel
import FPC.proof.Correctness.ReductionSemantics.PipelineRed
import FPC.proof.Adequacy.EndToEnd
import FPC.proof.Adequacy.AbstractMachines.EndToEnd
import FPC.proof.Adequacy.ReductionSemantics.EndToEnd
{- the Agda checks of §4.2, in no proof's total -}
import FPC.proof.Correctness.GraphModel.SplitDesignFiniteSource
import FPC.proof.Correctness.GraphModel.SplitDesignBoundedSets
import FPC.proof.Semantics.AbstractMachines.NoError
import FPC.proof.Semantics.ClockedInterpreters.NoError
import FPC.proof.Semantics.ReductionSemantics.NoError
import FPC.Examples
import FPC.proof.Compiler.Examples.RecursionExample
import FPC.proof.Compiler.Examples.RecursionInterp
