{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) is correct on
  the machines: the ISWIMμ machine on a closed program M and the machine
  of each later language on its compilation are Equivalent, by
  composing the passes, as for the typed pipeline
  (proof/Correctness/CEK/PipelineSim.agda). A program may have any
  type; for a main of type Int, the machines of ISWIMμ and X86μ stop
  with the same constant, or both diverge (nothing stops with an error).

-}

module Mu.proof.Correctness.CEK.PipelineSim where

open import Framework.Primitives using (Int)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import Mu.proof.Correctness.CEK.SimplifySim using (simplify-correct)
open import Mu.proof.Correctness.CEK.EncloseSim using (enclose-correct)
open import Mu.proof.Correctness.CEK.OptimizeSim using (optimize-correct)
open import Mu.proof.Correctness.CEK.ConcretizeSim using (concretize-correct)
open import Mu.proof.Correctness.CEK.DelaySim using (delay-correct)
open import Mu.proof.Correctness.CEK.GlobalizeSim using (globalize-correct)
open import Mu.proof.Correctness.CEK.RCOSim using (rco-correct)
open import Mu.proof.Correctness.CEK.LiftLocalsSim using (lift-locals-correct)
open import Mu.proof.Correctness.CEK.ExplicateSim using (explicate-correct)
open import Mu.proof.Correctness.CEK.SelectSim using (select-correct)
import Mu.Semantics.CEK.ISWIM as ISWIMμₘ
import Mu.Semantics.CEK.Clos4 as Clos4μₘ
import Mu.Semantics.CEK.Clos5 as Clos5μₘ
import Mu.Semantics.CEK.Imp as Impμₘ
import Mu.Semantics.CEK.CFG as CFGμₘ
import Mu.Semantics.CEK.X86 as X86μₘ

open import Semantics.Observation using (o-const; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Data.Integer using (ℤ)
open import Data.List using ([])

compile₄-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (Clos4μₘ.sem (compile₄ M))
compile₄-correct M =
  equiv-trans (simplify-correct M)
    (equiv-trans (enclose-correct _) (equiv-trans (optimize-correct _) (equiv-trans (concretize-correct _) (delay-correct _))))

compile-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (Clos5μₘ.sem (compile M))
compile-correct M = equiv-trans (compile₄-correct M) (globalize-correct _)

compile-mon-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (Clos5μₘ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct M = equiv-trans (compile-correct M) (rco-correct _)

compile-imp-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (Impμₘ.sem (compile-imp M))
compile-imp-correct M = equiv-trans (compile-mon-correct M) (lift-locals-correct _)

compile-cfg-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (CFGμₘ.sem (compile-cfg M))
compile-cfg-correct M = equiv-trans (compile-imp-correct M) (explicate-correct _)

compile-x86-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (X86μₘ.sem (compile-x86 M))
compile-x86-correct M = equiv-trans (compile-cfg-correct M) (select-correct _)

{- in particular, for a main of type Int -}

compile-x86-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμₘ.sem M) (o-const Int k) ⇔ Terminates (X86μₘ.sem (compile-x86 M)) (o-const Int k)
compile-x86-const M k = Equivalent.terminates (compile-x86-correct M) (o-const Int k)

compile-x86-diverges : ∀ (M : Tm [] (base Int)) → Diverges (ISWIMμₘ.sem M) ⇔ Diverges (X86μₘ.sem (compile-x86 M))
compile-x86-diverges M = Equivalent.diverges (compile-x86-correct M)
