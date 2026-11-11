{-

  The FPC compiler (FPC/Compiler/Pipeline.agda) is correct on
  the machines: the FPC machine on a closed program M and the machine
  of each later language on its compilation are Equivalent, by
  composing the passes, as for the typed pipeline
  (ISWIM/proof/Correctness/CEK/PipelineSim.agda). A program may have any
  type; for a main of type Int, the machines of FPC and X86μ stop
  with the same constant, or both diverge (nothing stops with an error).

-}

module FPC.proof.Correctness.AbstractMachines.PipelineSim where

open import Framework.Primitives using (Int)
open import FPC.Language.Type using (base)
open import FPC.Language.FPC using (Tm)
open import FPC.Language.Mon using (⌜_⌝ₚ)
open import FPC.Compiler.Pipeline using (compile-to-PairClos;
  compile-to-GlobalFun; compile-to-Mon; compile-to-Imp; compile-to-CFG; compile)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import FPC.proof.Correctness.AbstractMachines.SimplifySim using
  (simplify-correct)
open import FPC.proof.Correctness.AbstractMachines.CaptureSim using
  (capture-correct)
open import FPC.proof.Correctness.AbstractMachines.PruneSim using
  (prune-correct)
open import FPC.proof.Correctness.AbstractMachines.ConcretizeSim using
  (concretize-correct)
open import FPC.proof.Correctness.AbstractMachines.SplitSim using
  (split-correct)
open import FPC.proof.Correctness.AbstractMachines.HoistSim using
  (hoist-correct)
open import FPC.proof.Correctness.AbstractMachines.RCOSim using (rco-correct)
open import FPC.proof.Correctness.AbstractMachines.LiftLocalsSim using
  (lift-locals-correct)
open import FPC.proof.Correctness.AbstractMachines.ExplicateSim using
  (explicate-correct)
open import FPC.proof.Correctness.AbstractMachines.SelectSim using
  (select-correct)
import FPC.Semantics.AbstractMachines.FPC as FPCₘ
import FPC.Semantics.AbstractMachines.PairClos as PairClosμₘ
import FPC.Semantics.AbstractMachines.GlobalFun as GlobalFunμₘ
import FPC.Semantics.AbstractMachines.Imp as Impμₘ
import FPC.Semantics.AbstractMachines.CFG as CFGμₘ
import FPC.Semantics.AbstractMachines.X86 as X86μₘ

open import Semantics.Observation using (o-const; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Data.Integer using (ℤ)
open import Data.List using ([])

compile-to-PairClos-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCₘ.sem M) (PairClosμₘ.sem (compile-to-PairClos M))
compile-to-PairClos-correct M =
  equiv-trans (simplify-correct M)
    (equiv-trans (capture-correct _)
        (equiv-trans (prune-correct _)
          (equiv-trans (concretize-correct _) (split-correct _))))

compile-to-GlobalFun-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCₘ.sem M) (GlobalFunμₘ.sem (compile-to-GlobalFun M))
compile-to-GlobalFun-correct M =
  equiv-trans (compile-to-PairClos-correct M) (hoist-correct _)

compile-to-Mon-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCₘ.sem M) (GlobalFunμₘ.sem ⌜ compile-to-Mon M ⌝ₚ)
compile-to-Mon-correct M =
  equiv-trans (compile-to-GlobalFun-correct M) (rco-correct _)

compile-to-Imp-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCₘ.sem M) (Impμₘ.sem (compile-to-Imp M))
compile-to-Imp-correct M =
  equiv-trans (compile-to-Mon-correct M) (lift-locals-correct _)

compile-to-CFG-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCₘ.sem M) (CFGμₘ.sem (compile-to-CFG M))
compile-to-CFG-correct M =
  equiv-trans (compile-to-Imp-correct M) (explicate-correct _)

compile-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCₘ.sem M) (X86μₘ.sem (compile M))
compile-correct M = equiv-trans (compile-to-CFG-correct M) (select-correct _)

{- in particular, for a main of type Int -}

compile-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (FPCₘ.sem M) (o-const Int k)
    ⇔ Terminates (X86μₘ.sem (compile M)) (o-const Int k)
compile-const M k = Equivalent.terminates (compile-correct M) (o-const Int k)

compile-diverges : ∀ (M : Tm [] (base Int))
  → Diverges (FPCₘ.sem M) ⇔ Diverges (X86μₘ.sem (compile M))
compile-diverges M = Equivalent.diverges (compile-correct M)
