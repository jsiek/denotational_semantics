{-

  The closure-conversion passes of the pilot (Mu/Compiler/Pipeline.agda)
  are correct on the machines: the ISWIMμ machine on a closed program M
  and the Clos4μ machine on compile₄ M are Equivalent, by composing the
  passes, as compile₄-correct of the typed pipeline
  (proof/Correctness/CEK/PipelineSim.agda).

-}

module Mu.proof.Correctness.CEK.PipelineSim where

open import Mu.Language.ISWIM using (Tm)
open import Mu.Compiler.Pipeline using (compile₄)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import Mu.proof.Correctness.CEK.EncloseSim using (enclose-correct)
open import Mu.proof.Correctness.CEK.OptimizeSim using (optimize-correct)
open import Mu.proof.Correctness.CEK.ConcretizeSim using (concretize-correct)
open import Mu.proof.Correctness.CEK.DelaySim using (delay-correct)
import Mu.Semantics.CEK.ISWIM as ISWIMμₘ
import Mu.Semantics.CEK.Clos4 as Clos4μₘ

open import Data.List using ([])

compile₄-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (Clos4μₘ.sem (compile₄ M))
compile₄-correct M =
  equiv-trans (enclose-correct M) (equiv-trans (optimize-correct _) (equiv-trans (concretize-correct _) (delay-correct _)))
