{-

  The passes of the pilot (Mu/Compiler/Pipeline.agda) are correct by
  clocked interpreters: each pass is proved clock for clock, and the end
  theorems compose (equiv-trans), as in the typed pipeline
  (proof/Correctness/Interp/CompilerFuel.agda). A program is a closed
  term of any type.

-}

module Mu.proof.Correctness.Interp.CompilerFuel where

open import Mu.Language.ISWIM using (Tm)
open import Mu.Compiler.Pipeline using (compile₄)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import proof.Semantics.Interp.Clock using (Equivalent; equiv-trans)
open import Mu.proof.Correctness.Interp.EncloseFuel using (enclose-correct)
open import Mu.proof.Correctness.Interp.OptimizeFuel using (optimize-correct)
open import Mu.proof.Correctness.Interp.ConcretizeFuel using (concretize-correct)
open import Mu.proof.Correctness.Interp.DelayFuel using (delay-correct)
import Mu.Semantics.Interp.ISWIM as ISWIMμᵢ
import Mu.Semantics.Interp.Clos4 as Clos4μᵢ

open import Data.List using ([])

compile₄-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Clos4μᵢ.sem (compile₄ M))
compile₄-correct M =
  equiv-trans (enclose-correct M) (equiv-trans (optimize-correct M₁)
    (equiv-trans (concretize-correct (optimize-program M₁)) (delay-correct (concretize-program (optimize-program M₁)))))
  where M₁ = enclose M
