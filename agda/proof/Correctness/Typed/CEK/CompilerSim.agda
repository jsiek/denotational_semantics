{-

  The typed pilot's compiler (Compiler/Typed/Pipeline.agda) is correct
  on the machines: the ISWIM machine on a well-scoped closed program and
  the Clos4ᵀ machine on its compilation are Equivalent, by composing the
  four passes.

-}

module proof.Correctness.Typed.CEK.CompilerSim where

open import Language.ISWIM using (AST; Op; sig)
open import Framework.Syntax.Scope Op sig using (WS)
open import Compiler.Typed.Pipeline using (compileᵀ)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos4 as Clos4ᵀₘ
open import proof.Correctness.Typed.CEK.CastSim using (cast-correct)
open import proof.Correctness.Typed.CEK.EncloseSim using (enclose-correct)
open import proof.Correctness.Typed.CEK.ConcretizeSim using (concretize-correct)
open import proof.Correctness.Typed.CEK.DelaySim using (delay-correct)

compile-correct : ∀ (M : AST) (w : WS 0 M) → Equivalent (ISWIMₘ.sem M) (Clos4ᵀₘ.sem (compileᵀ M w))
compile-correct M w =
  equiv-trans (cast-correct M w) (equiv-trans (enclose-correct _)
    (equiv-trans (concretize-correct _) (delay-correct _)))
