{-

  FPC, Plotkin's Fixed Point Calculus, with iso-recursive types (no
  recursion construct, no errors) and its compiler to the typed assembly
  language X86μ (the paper's Instrμ), proved correct in five styles: the
  development of the PLDI 2027 paper. Mu/README.md is the road map from
  the paper to this code.

    FPC --simplify--> FPC --capture--> Closμ --prune--> Closμ
           --concretize--> EnvClosμ --split--> PairClosμ
           --hoist--> GlobalFunμ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

  The paper counts eight passes, because it groups capture, prune and
  concretize as one pass, enclose.

  The theorem statements are in Mu/Theorems/, one file per style, each
  theorem with its type written out and defined as the corresponding
  theorem of Mu/proof/; they and the definitions they use (modules
  outside Mu/proof/) are FPC's audit surface.

  * graph model: Mu/Theorems/CorrectWrtGraphModel.agda (Theorem 4.1 and Lemma 4.6),
    proved in Mu/proof/Correctness/GraphModel/, with split by the
    approximant logical relation (SplitRel.agda);
  * abstract machines + simulation: Mu/Theorems/CorrectWrtAbstractMachines.agda
    (Proposition F.2), Mu/proof/Correctness/AbstractMachines/;
  * clocked interpreters + value relations:
    Mu/Theorems/CorrectWrtClockedInterpreters.agda (Proposition F.1),
    Mu/proof/Correctness/ClockedInterpreters/;
  * reduction semantics + simulation:
    Mu/Theorems/CorrectWrtReductionSemantics.agda (Proposition F.3),
    Mu/proof/Correctness/ReductionSemantics/;
  * Scott domains: Mu/Theorems/CorrectWrtScottDomains.agda (Theorem 4.2),
    Mu/proof/Correctness/ScottDomains/; it needs TypeTopology, so it is
    checked from agda/AllScott.agda (make check-scott), not from here,
    as is the Scott-domain half of Proposition 5.1
    (Mu/Theorems/ScottDomainsAdequateWrtClockedInterpreters.agda, Mu/proof/Adequacy/ScottDomains/);
  * adequacy of the graph model for the clocked interpreters of FPC
    and X86μ: Mu/Theorems/GraphModelAdequateWrtClockedInterpreters.agda (Proposition 5.1),
    Mu/proof/Adequacy/; the same against the
    abstract machines instead: Mu/Theorems/GraphModelAdequateWrtAbstractMachines.agda,
    Mu/proof/Adequacy/AbstractMachines/; and another, against FPC's
    reduction semantics: Mu/Theorems/GraphModelAdequateWrtReductionSemantics.agda,
    Mu/proof/Adequacy/ReductionSemantics/;
  * the two Agda checks of the paper's §4.2 ("Design alternatives: which sides to relate"):
    a finite source side cannot satisfy the function clause of split's
    relation (Mu/proof/Correctness/GraphModel/SplitDesignFiniteSource.agda),
    and split's relation on target sets of bounded depth is the
    relation on their finite sublists
    (Mu/proof/Correctness/GraphModel/SplitDesignBoundedSets.agda).

  The experiment of mixing semantics is not part of the paper; it is
  checked from Mu/Experiments.agda.

  agda/Mu/ mirrors agda/: Mu/X.agda corresponds to X.agda (with
  Language/Typed/ as Mu/Language/ and Semantics/<style>/Typed/ as
  Mu/Semantics/<style>/), and the module Mu.X to X. It reuses the
  frameworks of agda/Framework/ unchanged; Mu/Framework/AllUtil.agda
  (with Mu/proof/Framework/AllProp.agda) adds heterogeneous vectors
  (All), which the lists of types of FPC's contexts and tuples need.

-}

module Mu.All where

import Mu.Theorems.CorrectWrtGraphModel
import Mu.Theorems.CorrectWrtAbstractMachines
import Mu.Theorems.CorrectWrtClockedInterpreters
import Mu.Theorems.CorrectWrtReductionSemantics
import Mu.Theorems.GraphModelAdequateWrtClockedInterpreters
import Mu.Theorems.GraphModelAdequateWrtAbstractMachines
import Mu.Theorems.GraphModelAdequateWrtReductionSemantics
import Mu.proof.Correctness.GraphModel.CompilerCorrect
import Mu.proof.Correctness.AbstractMachines.PipelineSim
import Mu.proof.Correctness.ClockedInterpreters.CompilerFuel
import Mu.proof.Correctness.ReductionSemantics.PipelineRed
import Mu.proof.Adequacy.EndToEnd
import Mu.proof.Adequacy.AbstractMachines.EndToEnd
import Mu.proof.Adequacy.ReductionSemantics.EndToEnd
{- the Agda checks of §4.2, in no proof's total -}
import Mu.proof.Correctness.GraphModel.SplitDesignFiniteSource
import Mu.proof.Correctness.GraphModel.SplitDesignBoundedSets
import Mu.proof.Semantics.AbstractMachines.NoError
import Mu.proof.Semantics.ClockedInterpreters.NoError
import Mu.proof.Semantics.ReductionSemantics.NoError
import Mu.proof.Compiler.Examples.RecursionExample
import Mu.proof.Compiler.Examples.RecursionInterp
