{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) is correct on
  the reduction semantics, for closed programs: each pass is Equivalent
  (Mu/proof/Correctness/ReductionSemantics/*Red.agda) and equivalence composes,
  as for the typed pipeline (proof/Correctness/Reduction/PipelineRed.agda).
  Monμ runs as its embedding ⌜ P ⌝ₚ in GlobalFunμ; Impμ, CFGμ and X86μ have
  no binders and keep their machines, with the CEK column's proofs of
  explicate control and select instructions. A program may have any
  type; for a main of type Int, ISWIMμ and X86μ stop with the same
  constant, or both diverge.

-}

module Mu.proof.Correctness.ReductionSemantics.PipelineRed where

open import Framework.Primitives using (Int)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Semantics.Observation using (Obs; o-const; _⇔_)
open import Semantics.Reduction.Smallstep using (Equivalent; Terminates; Diverges)
open import proof.Framework.Simulation Obs using (equiv-trans)
open import Mu.proof.Correctness.ReductionSemantics.SimplifyRed using (simplify-correct)
open import Mu.proof.Correctness.ReductionSemantics.EncloseRed using (enclose-correct)
open import Mu.proof.Correctness.ReductionSemantics.OptimizeRed using (optimize-correct)
open import Mu.proof.Correctness.ReductionSemantics.ConcretizeRed using (concretize-correct)
open import Mu.proof.Correctness.ReductionSemantics.DelayRed using (delay-correct)
open import Mu.proof.Correctness.ReductionSemantics.GlobalizeRed using (globalize-correct)
open import Mu.proof.Correctness.ReductionSemantics.RCORed using (rco-correct)
open import Mu.proof.Correctness.ReductionSemantics.LiftLocalsRed using (lift-locals-correct)
open import Mu.proof.Correctness.AbstractMachines.ExplicateSim using (explicate-correct)
open import Mu.proof.Correctness.AbstractMachines.SelectSim using (select-correct)
import Mu.Semantics.ReductionSemantics.ISWIM as S
import Mu.Semantics.ReductionSemantics.GlobalFun as GlobalFunᵣ
import Mu.Semantics.AbstractMachines.Imp as Impμₘ
import Mu.Semantics.AbstractMachines.CFG as CFGμₘ
import Mu.Semantics.AbstractMachines.X86 as X86μₘ

open import Data.Integer using (ℤ)
open import Data.List using ([])

compile-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (GlobalFunᵣ.sem (compile M))
compile-correct M =
  equiv-trans (simplify-correct M) (equiv-trans (enclose-correct _) (equiv-trans (optimize-correct _)
    (equiv-trans (concretize-correct _) (equiv-trans (delay-correct _) (globalize-correct _)))))

compile-mon-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (GlobalFunᵣ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct M = equiv-trans (compile-correct M) (rco-correct _)

compile-imp-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (Impμₘ.sem (compile-imp M))
compile-imp-correct M = equiv-trans (compile-mon-correct M) (lift-locals-correct _)

compile-cfg-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (CFGμₘ.sem (compile-cfg M))
compile-cfg-correct M = equiv-trans (compile-imp-correct M) (explicate-correct _)

compile-x86-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (X86μₘ.sem (compile-x86 M))
compile-x86-correct M = equiv-trans (compile-cfg-correct M) (select-correct _)

{- in particular, for a main of type Int -}

compile-x86-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (S.sem M) (o-const Int k) ⇔ Terminates (X86μₘ.sem (compile-x86 M)) (o-const Int k)
compile-x86-const M k = Equivalent.terminates (compile-x86-correct M) (o-const Int k)

compile-x86-diverges : ∀ (M : Tm [] (base Int)) → Diverges (S.sem M) ⇔ Diverges (X86μₘ.sem (compile-x86 M))
compile-x86-diverges M = Equivalent.diverges (compile-x86-correct M)
