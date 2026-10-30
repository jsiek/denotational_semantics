{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) is correct on
  the machines: the ISWIMμ machine on a closed program M and the machine
  of each later language on its compilation are Equivalent, by
  composing the passes, as for the typed pipeline
  (proof/Correctness/CEK/PipelineSim.agda). A program may have any
  type; for a main of type Int, the machines of ISWIMμ and X86μ stop
  with the same constant, or both diverge (nothing stops with an error).

-}

module Mu.proof.Correctness.AbstractMachines.PipelineSim where

open import Framework.Primitives using (Int)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Pipeline using (compile-to-PairClos; compile-to-GlobalFun; compile-to-Mon; compile-to-Imp; compile-to-CFG; compile)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import Mu.proof.Correctness.AbstractMachines.SimplifySim using (simplify-correct)
open import Mu.proof.Correctness.AbstractMachines.CaptureSim using (capture-correct)
open import Mu.proof.Correctness.AbstractMachines.PruneSim using (prune-correct)
open import Mu.proof.Correctness.AbstractMachines.ConcretizeSim using (concretize-correct)
open import Mu.proof.Correctness.AbstractMachines.SplitSim using (split-correct)
open import Mu.proof.Correctness.AbstractMachines.HoistSim using (hoist-correct)
open import Mu.proof.Correctness.AbstractMachines.RCOSim using (rco-correct)
open import Mu.proof.Correctness.AbstractMachines.LiftLocalsSim using (lift-locals-correct)
open import Mu.proof.Correctness.AbstractMachines.ExplicateSim using (explicate-correct)
open import Mu.proof.Correctness.AbstractMachines.SelectSim using (select-correct)
import Mu.Semantics.AbstractMachines.ISWIM as ISWIMμₘ
import Mu.Semantics.AbstractMachines.PairClos as PairClosμₘ
import Mu.Semantics.AbstractMachines.GlobalFun as GlobalFunμₘ
import Mu.Semantics.AbstractMachines.Imp as Impμₘ
import Mu.Semantics.AbstractMachines.CFG as CFGμₘ
import Mu.Semantics.AbstractMachines.X86 as X86μₘ

open import Semantics.Observation using (o-const; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Data.Integer using (ℤ)
open import Data.List using ([])

compile-to-PairClos-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (PairClosμₘ.sem (compile-to-PairClos M))
compile-to-PairClos-correct M =
  equiv-trans (simplify-correct M)
    (equiv-trans (capture-correct _) (equiv-trans (prune-correct _) (equiv-trans (concretize-correct _) (split-correct _))))

compile-to-GlobalFun-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (GlobalFunμₘ.sem (compile-to-GlobalFun M))
compile-to-GlobalFun-correct M = equiv-trans (compile-to-PairClos-correct M) (hoist-correct _)

compile-to-Mon-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (GlobalFunμₘ.sem ⌜ compile-to-Mon M ⌝ₚ)
compile-to-Mon-correct M = equiv-trans (compile-to-GlobalFun-correct M) (rco-correct _)

compile-to-Imp-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (Impμₘ.sem (compile-to-Imp M))
compile-to-Imp-correct M = equiv-trans (compile-to-Mon-correct M) (lift-locals-correct _)

compile-to-CFG-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (CFGμₘ.sem (compile-to-CFG M))
compile-to-CFG-correct M = equiv-trans (compile-to-Imp-correct M) (explicate-correct _)

compile-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμₘ.sem M) (X86μₘ.sem (compile M))
compile-correct M = equiv-trans (compile-to-CFG-correct M) (select-correct _)

{- in particular, for a main of type Int -}

compile-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμₘ.sem M) (o-const Int k) ⇔ Terminates (X86μₘ.sem (compile M)) (o-const Int k)
compile-const M k = Equivalent.terminates (compile-correct M) (o-const Int k)

compile-diverges : ∀ (M : Tm [] (base Int)) → Diverges (ISWIMμₘ.sem M) ⇔ Diverges (X86μₘ.sem (compile M))
compile-diverges M = Equivalent.diverges (compile-correct M)
