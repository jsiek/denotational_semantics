{-

  The correctness of the ISWIMμ compiler (Mu/Compiler/Pipeline.agda), by
  reduction semantics and simulations: the public statements. The
  proofs (forward simulations) are in Mu/proof/Correctness/Reduction/
  (explicate control and select instructions: the CEK proofs,
  Mu/proof/Correctness/CEK/, shared); each theorem here is one of them,
  with its type written out.

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ
           --concretize--> Clos3μ --delay--> Clos4μ --globalize--> Clos5μ
           --rco--> Monμ --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  Each language with binders has a reduction semantics by substitution
  (here Lᵣ.sem for language L, Mu/Semantics/Reduction/). Monμ runs as
  its embedding ⌜ P ⌝ₚ (Mu/Language/Mon.agda) in Clos5μ. Impμ, CFGμ and
  X86μ have no binders and keep their machines (here Lₘ.sem,
  Mu/Semantics/CEK/). A semantics terminates with an observation
  (Semantics/Observation.agda) or diverges. Two semantics are Equivalent
  (Framework/Smallstep.agda) when each terminates with o exactly when the
  other does, and one diverges exactly when the other does.

  To read them: the languages (Mu/Language/), the passes (Mu/Compiler/),
  the semantics and the observations.

-}

module Mu.Theorems.Reduction where

open import Framework.Primitives using (Int)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Reduction.Smallstep using (Terminates; Diverges; Equivalent)

open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.Clos2 as Clos2μ
import Mu.Language.Clos3 as Clos3μ
import Mu.Language.Clos4 as Clos4μ
import Mu.Language.Clos5 as Clos5μ
import Mu.Language.Mon as Monμ
open Monμ using (⌜_⌝ₚ)
import Mu.Language.Imp as Impμ
import Mu.Language.CFG as CFGμ

open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Delay using (delay-program)
open import Mu.Compiler.Globalize using (globalize)
open import Mu.Compiler.RCO using (rco-program)
open import Mu.Compiler.LiftLocals using (lift-program)
open import Mu.Compiler.Explicate using (explicate)
open import Mu.Compiler.Select using (select)
open import Mu.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

import Mu.Semantics.Reduction.ISWIM as ISWIMμᵣ
import Mu.Semantics.Reduction.Clos2 as Clos2μᵣ
import Mu.Semantics.Reduction.Clos3 as Clos3μᵣ
import Mu.Semantics.Reduction.Clos4 as Clos4μᵣ
import Mu.Semantics.Reduction.Clos5 as Clos5μᵣ
import Mu.Semantics.CEK.Imp as Impμₘ
import Mu.Semantics.CEK.CFG as CFGμₘ
import Mu.Semantics.CEK.X86 as X86μₘ

import Mu.proof.Correctness.Reduction.SimplifyRed as SimplifyRed
import Mu.proof.Correctness.Reduction.EncloseRed as EncloseRed
import Mu.proof.Correctness.Reduction.OptimizeRed as OptimizeRed
import Mu.proof.Correctness.Reduction.ConcretizeRed as ConcretizeRed
import Mu.proof.Correctness.Reduction.DelayRed as DelayRed
import Mu.proof.Correctness.Reduction.GlobalizeRed as GlobalizeRed
import Mu.proof.Correctness.Reduction.RCORed as RCORed
import Mu.proof.Correctness.Reduction.LiftLocalsRed as LiftLocalsRed
import Mu.proof.Correctness.CEK.ExplicateSim as ExplicateSim
import Mu.proof.Correctness.CEK.SelectSim as SelectSim
import Mu.proof.Correctness.Reduction.PipelineRed as PipelineRed

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Each pass ------------------------------------------------------------------}

simplify-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (ISWIMμᵣ.sem (simplify M))
simplify-correct = SimplifyRed.simplify-correct

enclose-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (Clos2μᵣ.sem (enclose M))
enclose-correct = EncloseRed.enclose-correct

optimize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → Equivalent (Clos2μᵣ.sem M) (Clos2μᵣ.sem (optimize-program M))
optimize-correct = OptimizeRed.optimize-correct

concretize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → Equivalent (Clos2μᵣ.sem M) (Clos3μᵣ.sem (concretize-program M))
concretize-correct = ConcretizeRed.concretize-correct

delay-correct : ∀ {A} (M : Clos3μ.Tm [] A) → Equivalent (Clos3μᵣ.sem M) (Clos4μᵣ.sem (delay-program M))
delay-correct = DelayRed.delay-correct

globalize-correct : ∀ {A} (M : Clos4μ.Tm [] A) → Equivalent (Clos4μᵣ.sem M) (Clos5μᵣ.sem (globalize M))
globalize-correct = GlobalizeRed.globalize-correct

rco-correct : ∀ {A} (P : Clos5μ.Program A) → Equivalent (Clos5μᵣ.sem P) (Clos5μᵣ.sem ⌜ rco-program P ⌝ₚ)
rco-correct = RCORed.rco-correct

lift-locals-correct : ∀ {A} (P : Monμ.Program A) → Equivalent (Clos5μᵣ.sem ⌜ P ⌝ₚ) (Impμₘ.sem (lift-program P))
lift-locals-correct = LiftLocalsRed.lift-locals-correct

explicate-correct : ∀ {A} (P : Impμ.Program A) → Equivalent (Impμₘ.sem P) (CFGμₘ.sem (explicate P))
explicate-correct = ExplicateSim.explicate-correct

select-correct : ∀ {A} (P : CFGμ.Program A) → Equivalent (CFGμₘ.sem P) (X86μₘ.sem (select P))
select-correct = SelectSim.select-correct

{- The whole compiler, for closed programs of any type ----------------------}

compile-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (Clos5μᵣ.sem (compile M))
compile-correct = PipelineRed.compile-correct

compile-mon-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (Clos5μᵣ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct = PipelineRed.compile-mon-correct

compile-imp-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (Impμₘ.sem (compile-imp M))
compile-imp-correct = PipelineRed.compile-imp-correct

compile-cfg-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (CFGμₘ.sem (compile-cfg M))
compile-cfg-correct = PipelineRed.compile-cfg-correct

compile-x86-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (X86μₘ.sem (compile-x86 M))
compile-x86-correct = PipelineRed.compile-x86-correct

{- The end-to-end theorem, for a main program of type Int: ISWIMμ and
   X86μ stop with the same constant, or both diverge -}

compile-x86-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμᵣ.sem M) (o-const Int k) ⇔ Terminates (X86μₘ.sem (compile-x86 M)) (o-const Int k)
compile-x86-const = PipelineRed.compile-x86-const

compile-x86-diverges : ∀ (M : ISWIMμ.Tm [] (base Int))
  → Diverges (ISWIMμᵣ.sem M) ⇔ Diverges (X86μₘ.sem (compile-x86 M))
compile-x86-diverges = PipelineRed.compile-x86-diverges
