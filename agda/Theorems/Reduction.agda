{-

  The correctness of the compiler (Compiler/Pipeline.agda), by reduction semantics and
  simulations: the public statements. The proofs (forward simulations)
  are in proof/Correctness/Reduction/; each theorem here is one of
  them, with its type written out, so that it can be read without
  opening proof/.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86

  Each language with binders has a reduction semantics by substitution
  (here Lᵣ.sem for language L): untyped ISWIM
  (Semantics/Reduction/ISWIM.agda) and the typed ones
  (Semantics/Reduction/Typed/). Monᵀ runs as its embedding ⌜ P ⌝ₚ
  (Language/Typed/Mon.agda) in Clos5ᵀ. Impᵀ, CFGᵀ and X86 have no
  binders and keep their machines (here Lₘ.sem, Semantics/CEK/Typed/ and
  Semantics/CEK/X86.agda). A semantics terminates with an observation
  (Semantics/Observation.agda) or diverges. Two semantics are Equivalent
  (Framework/Smallstep.agda) when each terminates with o exactly when the
  other does (o-error, an error, included), and one diverges exactly
  when the other does.

  To read them: the languages (Language/, Language/Typed/), the passes
  (Compiler/), the semantics, the observations, and the
  precondition Closed (Compiler/EncloseScope.agda), for the untyped
  source only.

-}

module Theorems.Reduction where

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.Reduction.Smallstep using (Terminates; Diverges; Equivalent)

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
open import Compiler.Enclose using (enclose)
open import Compiler.Optimize using (optimize-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Delay using (delay-program)
open import Compiler.Globalize using (globalize)
open import Compiler.RCO using (rco-program)
open import Compiler.LiftLocals using (lift-program)
open import Compiler.Explicate using (explicate)
open import Compiler.Select using (select)
open import Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import Compiler.EncloseScope using (Closed)

import Semantics.Reduction.ISWIM as ISWIMᵣ
import Semantics.Reduction.Typed.ISWIM as ISWIMᵀᵣ
import Semantics.Reduction.Typed.Clos2 as Clos2ᵀᵣ
import Semantics.Reduction.Typed.Clos3 as Clos3ᵀᵣ
import Semantics.Reduction.Typed.Clos4 as Clos4ᵀᵣ
import Semantics.Reduction.Typed.Clos5 as Clos5ᵀᵣ
import Semantics.CEK.Typed.Imp as Impᵀₘ
import Semantics.CEK.Typed.CFG as CFGᵀₘ
import Semantics.CEK.X86 as X86ₘ

import proof.Correctness.Reduction.SimplifyRed as SimplifyRed
import proof.Correctness.Reduction.CastRed as CastRed
import proof.Correctness.Reduction.EncloseRed as EncloseRed
import proof.Correctness.Reduction.OptimizeRed as OptimizeRed
import proof.Correctness.Reduction.ConcretizeRed as ConcretizeRed
import proof.Correctness.Reduction.DelayRed as DelayRed
import proof.Correctness.Reduction.GlobalizeRed as GlobalizeRed
import proof.Correctness.Reduction.RCORed as RCORed
import proof.Correctness.Reduction.LiftLocalsRed as LiftLocalsRed
import proof.Correctness.CEK.ExplicateSim as ExplicateSim
import proof.Correctness.CEK.SelectSim as SelectSim
import proof.Correctness.Reduction.PipelineRed as PipelineRed

{- Each pass ------------------------------------------------------------------}

{- simplify, for closed programs -}
simplify-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (ISWIMᵣ.sem (simplify M))
simplify-correct = SimplifyRed.simplify-correct

{- cast insertion, for closed programs -}
cast-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (ISWIMᵀᵣ.sem (cast-closed M))
cast-correct = CastRed.cast-correct

enclose-correct : ∀ (M : ISWIMᵀ.Tm 0 Any) → Equivalent (ISWIMᵀᵣ.sem M) (Clos2ᵀᵣ.sem (enclose M))
enclose-correct = EncloseRed.enclose-correct

optimize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵣ.sem M) (Clos2ᵀᵣ.sem (optimize-program M))
optimize-correct = OptimizeRed.optimize-correct

concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵣ.sem M) (Clos3ᵀᵣ.sem (concretize-program M))
concretize-correct = ConcretizeRed.concretize-correct

delay-correct : ∀ (M : Clos3ᵀ.Tm [] Any) → Equivalent (Clos3ᵀᵣ.sem M) (Clos4ᵀᵣ.sem (delay-program M))
delay-correct = DelayRed.delay-correct

globalize-correct : ∀ (M : Clos4ᵀ.Tm [] Any) → Equivalent (Clos4ᵀᵣ.sem M) (Clos5ᵀᵣ.sem (globalize M))
globalize-correct = GlobalizeRed.globalize-correct

rco-correct : ∀ (P : Clos5ᵀ.Program) → Equivalent (Clos5ᵀᵣ.sem P) (Clos5ᵀᵣ.sem ⌜ rco-program P ⌝ₚ)
rco-correct = RCORed.rco-correct

lift-locals-correct : ∀ (P : Monᵀ.Program) → Equivalent (Clos5ᵀᵣ.sem ⌜ P ⌝ₚ) (Impᵀₘ.sem (lift-program P))
lift-locals-correct = LiftLocalsRed.lift-locals-correct

{- explicate control and select instructions, between the machines of
   Impᵀ, CFGᵀ and X86 (the proofs of the CEK machine + simulation column) -}
explicate-correct : ∀ (P : Impᵀ.Program) → Equivalent (Impᵀₘ.sem P) (CFGᵀₘ.sem (explicate P))
explicate-correct = ExplicateSim.explicate-correct

{- X86 keeps its own trapped errors; select's code never reaches them -}
select-correct : ∀ (P : CFGᵀ.Program) → Equivalent (CFGᵀₘ.sem P) (X86ₘ.sem (select P))
select-correct = SelectSim.select-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (Clos5ᵀᵣ.sem (compile M))
compile-correct = PipelineRed.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (Clos5ᵀᵣ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct = PipelineRed.compile-mon-correct

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (Impᵀₘ.sem (compile-imp M))
compile-imp-correct = PipelineRed.compile-imp-correct

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (CFGᵀₘ.sem (compile-cfg M))
compile-cfg-correct = PipelineRed.compile-cfg-correct

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (X86ₘ.sem (compile-x86 M))
compile-x86-correct = PipelineRed.compile-x86-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, errors exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMᵣ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵀᵣ.sem (compile M)) (o-const B k)
compile-const = PipelineRed.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMᵣ.sem M)) ⇔ Converges (Terminates (Clos5ᵀᵣ.sem (compile M)))
compile-converges = PipelineRed.compile-converges

compile-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMᵣ.sem M) o-error ⇔ Terminates (Clos5ᵀᵣ.sem (compile M)) o-error
compile-error = PipelineRed.compile-error

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMᵣ.sem M) ⇔ Diverges (Clos5ᵀᵣ.sem (compile M))
compile-diverges = PipelineRed.compile-diverges
