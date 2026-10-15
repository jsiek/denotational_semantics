{-

  The closure-conversion passes of the pilot (Mu/Compiler/Pipeline.agda)
  are correct on the reduction semantics: the ISWIMμ reduction semantics
  of a closed program M and the Clos4μ one of compile₄ M are
  Equivalent, by composing the passes
  (Mu/proof/Correctness/Reduction/*Red.agda), as compile-correct of the
  typed pipeline (proof/Correctness/Reduction/PipelineRed.agda).

-}

module Mu.proof.Correctness.Reduction.PipelineRed where

open import Mu.Language.ISWIM using (Tm)
open import Mu.Compiler.Pipeline using (compile₄)
open import Semantics.Observation using (Obs)
open import Semantics.Reduction.Smallstep using (Equivalent)
open import proof.Framework.Simulation Obs using (equiv-trans)
open import Mu.proof.Correctness.Reduction.EncloseRed using (enclose-correct)
open import Mu.proof.Correctness.Reduction.OptimizeRed using (optimize-correct)
open import Mu.proof.Correctness.Reduction.ConcretizeRed using (concretize-correct)
open import Mu.proof.Correctness.Reduction.DelayRed using (delay-correct)
import Mu.Semantics.Reduction.ISWIM as S
import Mu.Semantics.Reduction.Clos4 as T

open import Data.List using ([])

compile₄-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (compile₄ M))
compile₄-correct M =
  equiv-trans (enclose-correct M) (equiv-trans (optimize-correct _) (equiv-trans (concretize-correct _) (delay-correct _)))
