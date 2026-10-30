{-

  The correctness of the compiler (Compiler/Pipeline.agda), by CEK machines and
  simulations: the public statements. The proofs (forward simulations)
  are in proof/Correctness/CEK/; each theorem here is one of them,
  with its type written out, so that it can be read without opening
  proof/.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --capture--> Clos2ᵀ
          --prune--> Clos2ᵀ --concretize--> Clos3ᵀ --split--> Clos4ᵀ
          --hoist--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

  Each language has a small-step machine (here Lₘ.sem for language L):
  untyped ISWIM (Semantics/CEK/ISWIM.agda), and the typed ones
  (Semantics/CEK/Typed/), down to the typed assembly language X86ᵀ.
  Monᵀ has no machine: a Monᵀ program runs as its embedding ⌜ P ⌝ₚ
  (Language/Typed/Mon.agda) on the Clos5ᵀ machine. A machine terminates
  with an observation (Semantics/Observation.agda) or diverges. Two
  machines are Equivalent (Framework/Smallstep.agda) when each
  terminates with o exactly when the other does (o-error, an error,
  included), and one diverges exactly when the other does.

  To read them: the languages (Language/, Language/Typed/), the passes
  (Compiler/), the machines, the observations, and the
  precondition Closed (Compiler/CaptureScope.agda), for the untyped
  source only.

-}

module Theorems.Simulation where

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges; Equivalent)

import Language.ISWIM as ISWIM
open import Language.Typed.Type using (Any)
open import Data.List using ([])
import Language.Typed.ISWIM as ISWIMᵀ
import Language.Typed.Clos2 as Clos2ᵀ
import Language.Typed.Clos3 as Clos3ᵀ
import Language.Typed.Clos4 as Clos4ᵀ
import Language.Typed.Clos5 as Clos5ᵀ
import Language.Typed.Mon as Monᵀ
open Monᵀ using (⌜_⌝ₚ)
import Language.Typed.Imp as Impᵀ
import Language.Typed.CFG as CFGᵀ

open import Compiler.Simplify using (simplify)
open import Compiler.Cast using (cast-closed)
open import Compiler.Capture using (capture)
open import Compiler.Prune using (prune-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Split using (split-program)
open import Compiler.Hoist using (hoist)
open import Compiler.RCO using (rco-program)
open import Compiler.LiftLocals using (lift-program)
open import Compiler.Explicate using (explicate)
open import Compiler.Select using (select)
open import Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import Compiler.CaptureScope using (Closed)

import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.ISWIM as ISWIMᵀₘ
import Semantics.CEK.Typed.Clos2 as Clos2ᵀₘ
import Semantics.CEK.Typed.Clos3 as Clos3ᵀₘ
import Semantics.CEK.Typed.Clos4 as Clos4ᵀₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
import Semantics.CEK.Typed.Imp as Impᵀₘ
import Semantics.CEK.Typed.CFG as CFGᵀₘ
import Semantics.CEK.Typed.X86 as X86ᵀₘ

import proof.Correctness.CEK.SimplifySim as SimplifySim
import proof.Correctness.CEK.CaptureSim as CaptureSim
import proof.Correctness.CEK.PruneSim as PruneSim
import proof.Correctness.CEK.ConcretizeSim as ConcretizeSim
import proof.Correctness.CEK.SplitSim as SplitSim
import proof.Correctness.CEK.HoistSim as HoistSim
import proof.Correctness.CEK.RCOSim as RCOSim
import proof.Correctness.CEK.LiftLocalsSim as LiftLocalsSim
import proof.Correctness.CEK.ExplicateSim as ExplicateSim
import proof.Correctness.CEK.SelectSim as SelectSim
import proof.Correctness.CEK.PipelineSim as PipelineSim

{- Each pass ------------------------------------------------------------------}

{- simplify, for closed programs -}
simplify-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (ISWIMₘ.sem (simplify M))
simplify-correct = SimplifySim.simplify-correct

{- cast insertion, for closed programs -}
cast-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (ISWIMᵀₘ.sem (cast-closed M))
cast-correct = PipelineSim.cast-correct

capture-correct : ∀ (M : ISWIMᵀ.Tm 0 Any) → Equivalent (ISWIMᵀₘ.sem M) (Clos2ᵀₘ.sem (capture M))
capture-correct = CaptureSim.capture-correct

prune-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀₘ.sem M) (Clos2ᵀₘ.sem (prune-program M))
prune-correct = PruneSim.prune-correct

concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀₘ.sem M) (Clos3ᵀₘ.sem (concretize-program M))
concretize-correct = ConcretizeSim.concretize-correct

split-correct : ∀ (M : Clos3ᵀ.Tm [] Any) → Equivalent (Clos3ᵀₘ.sem M) (Clos4ᵀₘ.sem (split-program M))
split-correct = SplitSim.split-correct

hoist-correct : ∀ (M : Clos4ᵀ.Tm [] Any) → Equivalent (Clos4ᵀₘ.sem M) (Clos5ᵀₘ.sem (hoist M))
hoist-correct = HoistSim.hoist-correct

rco-correct : ∀ (P : Clos5ᵀ.Program) → Equivalent (Clos5ᵀₘ.sem P) (Clos5ᵀₘ.sem ⌜ rco-program P ⌝ₚ)
rco-correct = RCOSim.rco-correct

lift-locals-correct : ∀ (P : Monᵀ.Program) → Equivalent (Clos5ᵀₘ.sem ⌜ P ⌝ₚ) (Impᵀₘ.sem (lift-program P))
lift-locals-correct = LiftLocalsSim.lift-locals-correct

explicate-correct : ∀ (P : Impᵀ.Program) → Equivalent (Impᵀₘ.sem P) (CFGᵀₘ.sem (explicate P))
explicate-correct = ExplicateSim.explicate-correct

{- X86ᵀ's only trapped error is chk's, project's check -}
select-correct : ∀ (P : CFGᵀ.Program) → Equivalent (CFGᵀₘ.sem P) (X86ᵀₘ.sem (select P))
select-correct = SelectSim.select-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (Clos5ᵀₘ.sem (compile M))
compile-correct = PipelineSim.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (Clos5ᵀₘ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct = PipelineSim.compile-mon-correct

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (Impᵀₘ.sem (compile-imp M))
compile-imp-correct = PipelineSim.compile-imp-correct

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (CFGᵀₘ.sem (compile-cfg M))
compile-cfg-correct = PipelineSim.compile-cfg-correct

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (X86ᵀₘ.sem (compile-x86 M))
compile-x86-correct = PipelineSim.compile-x86-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, errors exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
compile-const = PipelineSim.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
compile-converges = PipelineSim.compile-converges

compile-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) o-error
compile-error = PipelineSim.compile-error

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (Clos5ᵀₘ.sem (compile M))
compile-diverges = PipelineSim.compile-diverges
