{-

  The compiler of the pilot (Mu/Compiler/Pipeline.agda) is correct on
  the reduction semantics, for closed programs: each pass is Equivalent
  (Mu/proof/Correctness/Reduction/*Red.agda) and equivalence composes,
  as for the typed pipeline (proof/Correctness/Reduction/PipelineRed.agda).
  Monμ runs as its embedding ⌜ P ⌝ₚ in Clos5μ; Impμ, CFGμ and X86μ have
  no binders and keep their machines, with the CEK column's proofs of
  explicate control and select instructions. A program may have any
  type; for a main of type Int, ISWIMμ and X86μ stop with the same
  constant, or both diverge.

-}

module Mu.proof.Correctness.Reduction.PipelineRed where

open import Framework.Primitives using (Int)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Semantics.Observation using (Obs; o-const; _⇔_)
open import Semantics.Reduction.Smallstep using (Equivalent; Terminates; Diverges)
open import proof.Framework.Simulation Obs using (equiv-trans)
open import Mu.proof.Correctness.Reduction.SimplifyRed using (simplify-correct)
open import Mu.proof.Correctness.Reduction.EncloseRed using (enclose-correct)
open import Mu.proof.Correctness.Reduction.OptimizeRed using (optimize-correct)
open import Mu.proof.Correctness.Reduction.ConcretizeRed using (concretize-correct)
open import Mu.proof.Correctness.Reduction.DelayRed using (delay-correct)
open import Mu.proof.Correctness.Reduction.GlobalizeRed using (globalize-correct)
open import Mu.proof.Correctness.Reduction.RCORed using (rco-correct)
open import Mu.proof.Correctness.Reduction.LiftLocalsRed using (lift-locals-correct)
open import Mu.proof.Correctness.CEK.ExplicateSim using (explicate-correct)
open import Mu.proof.Correctness.CEK.SelectSim using (select-correct)
import Mu.Semantics.Reduction.ISWIM as S
import Mu.Semantics.Reduction.Clos4 as Clos4ᵣ
import Mu.Semantics.Reduction.Clos5 as Clos5ᵣ
import Mu.Semantics.CEK.Imp as Impμₘ
import Mu.Semantics.CEK.CFG as CFGμₘ
import Mu.Semantics.CEK.X86 as X86μₘ

open import Data.Integer using (ℤ)
open import Data.List using ([])

compile₄-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (Clos4ᵣ.sem (compile₄ M))
compile₄-correct M =
  equiv-trans (simplify-correct M)
    (equiv-trans (enclose-correct _) (equiv-trans (optimize-correct _) (equiv-trans (concretize-correct _) (delay-correct _))))

compile-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (Clos5ᵣ.sem (compile M))
compile-correct M = equiv-trans (compile₄-correct M) (globalize-correct _)

compile-mon-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (Clos5ᵣ.sem ⌜ compile-mon M ⌝ₚ)
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
