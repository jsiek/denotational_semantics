{-

  ISWIMμ: a typed ISWIM with iso-recursive types (no recursion
  construct, no errors) and its compiler to the typed assembly language
  X86μ, proved correct in five styles: the development of the PLDI 2027
  paper. Mu/README.md is the road map from the paper to this code.

    ISWIMμ --simplify--> ISWIMμ --capture--> Closμ --prune--> Closμ
           --concretize--> EnvClosμ --delay--> PairClosμ
           --globalize--> GlobalFunμ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

  The theorem statements are in Mu/Theorems/, one file per style, each
  theorem with its type written out and defined as the corresponding
  theorem of Mu/proof/; they and the definitions they use (modules
  outside Mu/proof/) are ISWIMμ's audit surface.

  * graph model: Mu/Theorems/GraphModel.agda (Theorems 4.1 and 4.4),
    proved in Mu/proof/Correctness/GraphModel/, with delay by the
    approximant logical relation (DelayRel.agda);
  * abstract machines + simulation: Mu/Theorems/AbstractMachines.agda
    (Theorem F.2), Mu/proof/Correctness/AbstractMachines/;
  * clocked interpreters + value relations:
    Mu/Theorems/ClockedInterpreters.agda (Theorem F.1),
    Mu/proof/Correctness/ClockedInterpreters/;
  * reduction semantics + simulation:
    Mu/Theorems/ReductionSemantics.agda (Theorem F.3),
    Mu/proof/Correctness/ReductionSemantics/;
  * Scott domains: Mu/Theorems/ScottDomains.agda (Theorem F.4),
    Mu/proof/Correctness/ScottDomains/; it needs TypeTopology, so it is
    checked from agda/AllScott.agda (make check-scott), not from here;
  * adequacy of the graph model for the clocked interpreters of ISWIMμ
    and X86μ: Mu/Theorems/Adequacy.agda (Theorem 4.5),
    Mu/proof/Adequacy/; an alternative, reported separately, against the
    abstract machines instead: Mu/proof/Adequacy/AbstractMachines/;
  * the two Agda checks of the paper's §4.2 ("Which sides to relate"):
    a finite source side cannot satisfy the function clause of delay's
    relation (Mu/proof/Correctness/GraphModel/DelayDesignFiniteSource.agda),
    and delay's relation on target sets of bounded depth is the
    relation on their finite sublists
    (Mu/proof/Correctness/GraphModel/DelayDesignBoundedSets.agda).

  The experiment of mixing semantics is not part of the paper; it is
  checked from Mu/Experiments.agda.

  agda/Mu/ mirrors agda/: Mu/X.agda corresponds to X.agda (with
  Language/Typed/ as Mu/Language/ and Semantics/<style>/Typed/ as
  Mu/Semantics/<style>/), and the module Mu.X to X. It reuses the
  frameworks of agda/Framework/ unchanged; Mu/Framework/AllUtil.agda
  (with Mu/proof/Framework/AllProp.agda) adds heterogeneous vectors
  (All), which the lists of types of ISWIMμ's contexts and tuples need.

-}

module Mu.All where

import Mu.Theorems.GraphModel
import Mu.Theorems.AbstractMachines
import Mu.Theorems.ClockedInterpreters
import Mu.Theorems.ReductionSemantics
import Mu.Theorems.Adequacy
import Mu.proof.Correctness.GraphModel.CompilerCorrect
import Mu.proof.Correctness.AbstractMachines.PipelineSim
import Mu.proof.Correctness.ClockedInterpreters.CompilerFuel
import Mu.proof.Correctness.ReductionSemantics.PipelineRed
import Mu.proof.Adequacy.EndToEnd
import Mu.proof.Adequacy.AbstractMachines.EndToEnd
{- the Agda checks of §4.2, in no proof's total -}
import Mu.proof.Correctness.GraphModel.DelayDesignFiniteSource
import Mu.proof.Correctness.GraphModel.DelayDesignBoundedSets
import Mu.proof.Semantics.AbstractMachines.NoError
import Mu.proof.Semantics.ClockedInterpreters.NoError
import Mu.proof.Semantics.ReductionSemantics.NoError
import Mu.proof.Compiler.Examples.RecursionExample
import Mu.proof.Compiler.Examples.RecursionInterp
