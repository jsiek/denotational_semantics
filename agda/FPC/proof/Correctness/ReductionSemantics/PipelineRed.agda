{-

  The FPC compiler (FPC/Compiler/Pipeline.agda) is correct on
  the reduction semantics, for closed programs: each pass is Equivalent
  (FPC/proof/Correctness/ReductionSemantics/*Red.agda) and equivalence composes,
  as for the typed pipeline
  (ISWIM/proof/Correctness/Reduction/PipelineRed.agda). Monμ runs as its
  embedding ⌜ P ⌝ₚ in GlobalFunμ; Impμ, CFGμ and X86μ have no binders and keep
  their machines, with the CEK column's proofs of explicate control and select
  instructions. A program may have any type; for a main of type Int, FPC and
  X86μ stop with the same constant, or both diverge.

-}

module FPC.proof.Correctness.ReductionSemantics.PipelineRed where

open import Framework.Primitives using (Int)
open import FPC.Language.Type using (base)
open import FPC.Language.FPC using (Tm)
open import FPC.Language.Mon using (⌜_⌝ₚ)
open import FPC.Compiler.Pipeline using (compile-to-GlobalFun; compile-to-Mon;
  compile-to-Imp; compile-to-CFG; compile)
open import Semantics.Observation using (Obs; o-const; _⇔_)
open import Semantics.Reduction.Smallstep using (Equivalent; Terminates;
  Diverges)
open import proof.Framework.Simulation Obs using (equiv-trans)
open import FPC.proof.Correctness.ReductionSemantics.SimplifyRed using
  (simplify-correct)
open import FPC.proof.Correctness.ReductionSemantics.CaptureRed using
  (capture-correct)
open import FPC.proof.Correctness.ReductionSemantics.PruneRed using
  (prune-correct)
open import FPC.proof.Correctness.ReductionSemantics.ConcretizeRed using
  (concretize-correct)
open import FPC.proof.Correctness.ReductionSemantics.SplitRed using
  (split-correct)
open import FPC.proof.Correctness.ReductionSemantics.HoistRed using
  (hoist-correct)
open import FPC.proof.Correctness.ReductionSemantics.RCORed using (rco-correct)
open import FPC.proof.Correctness.ReductionSemantics.LiftLocalsRed using
  (lift-locals-correct)
open import FPC.proof.Correctness.AbstractMachines.ExplicateSim using
  (explicate-correct)
open import FPC.proof.Correctness.AbstractMachines.SelectSim using
  (select-correct)
import FPC.Semantics.ReductionSemantics.FPC as S
import FPC.Semantics.ReductionSemantics.GlobalFun as GlobalFunᵣ
import FPC.Semantics.AbstractMachines.Imp as Impμₘ
import FPC.Semantics.AbstractMachines.CFG as CFGμₘ
import FPC.Semantics.AbstractMachines.X86 as X86μₘ

open import Data.Integer using (ℤ)
open import Data.List using ([])

compile-to-GlobalFun-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (S.sem M) (GlobalFunᵣ.sem (compile-to-GlobalFun M))
compile-to-GlobalFun-correct M =
  equiv-trans (simplify-correct M)
    (equiv-trans (capture-correct _) (equiv-trans (prune-correct _)
    (equiv-trans (concretize-correct _)
        (equiv-trans (split-correct _) (hoist-correct _)))))

compile-to-Mon-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (S.sem M) (GlobalFunᵣ.sem ⌜ compile-to-Mon M ⌝ₚ)
compile-to-Mon-correct M =
  equiv-trans (compile-to-GlobalFun-correct M) (rco-correct _)

compile-to-Imp-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (S.sem M) (Impμₘ.sem (compile-to-Imp M))
compile-to-Imp-correct M =
  equiv-trans (compile-to-Mon-correct M) (lift-locals-correct _)

compile-to-CFG-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (S.sem M) (CFGμₘ.sem (compile-to-CFG M))
compile-to-CFG-correct M =
  equiv-trans (compile-to-Imp-correct M) (explicate-correct _)

compile-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (S.sem M) (X86μₘ.sem (compile M))
compile-correct M = equiv-trans (compile-to-CFG-correct M) (select-correct _)

{- in particular, for a main of type Int -}

compile-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (S.sem M) (o-const Int k)
    ⇔ Terminates (X86μₘ.sem (compile M)) (o-const Int k)
compile-const M k = Equivalent.terminates (compile-correct M) (o-const Int k)

compile-diverges : ∀ (M : Tm [] (base Int))
  → Diverges (S.sem M) ⇔ Diverges (X86μₘ.sem (compile M))
compile-diverges M = Equivalent.diverges (compile-correct M)
