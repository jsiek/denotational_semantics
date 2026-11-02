{-

  The correctness of the compiler, by reduction semantics and
  simulations: the public statements.
  The proofs (forward simulations) are in
  proof/Correctness/Reduction/; each theorem here is one of
  them, with its type written out, so that it can be read without opening
  proof/.

    ISWIM --simplify--> ISWIM --capture--> Clos2 --prune--> Clos2 --concretize--> Clos3
          --split--> Clos4 --hoist--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  Each language with binders has a reduction semantics by substitution
  (Semantics/Reduction/, here Lᵣ.sem for language L), which terminates
  with an observation (Semantics/Observation.agda) or diverges; Imp, CFG
  and X86 have no binders and keep their machines
  (Semantics/CEK/, here Lₘ.sem). Two semantics are
  Equivalent (Framework/Smallstep.agda) when each terminates with o
  exactly when the other does (o-error, an error, included), and one
  diverges exactly when the other does.

  To read them: the languages (Language/), the passes
  (Compiler/), the semantics, the observations, and the
  preconditions: Closed (Compiler/CaptureScope.agda), WS
  (Framework/Syntax/Scope.agda), Scoped
  (Compiler/PipelineScope.agda) and MonProgram
  (Language/Mon.agda).

-}

module Untyped.Theorems.Reduction where

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.Reduction.Smallstep using (Terminates; Diverges; Equivalent)

import Language.ISWIM as ISWIM
import Untyped.Language.Clos2 as Clos2
import Untyped.Language.Clos3 as Clos3
import Untyped.Language.Clos4 as Clos4
import Untyped.Language.Clos5 as Clos5
open import Untyped.Language.Mon using (MonProgram)
import Untyped.Language.Imp as Imp
import Untyped.Language.CFG as CFG

open import Compiler.Simplify using (simplify)
open import Untyped.Compiler.Capture using (capture)
open import Untyped.Compiler.Prune using (prune-program)
open import Untyped.Compiler.Concretize using (concretize-program)
open import Untyped.Compiler.Split using (split)
open import Untyped.Compiler.Hoist using (hoist)
open import Untyped.Compiler.RCO using (rco-program)
open import Untyped.Compiler.LiftLocals using (lift-program)
open import Untyped.Compiler.Explicate using (explicate)
open import Untyped.Compiler.Select using (select)
open import Untyped.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import Compiler.CaptureScope using (Closed)
open import Framework.Syntax.Scope Clos2.Op Clos2.sig using (WS)
open import Untyped.Compiler.PipelineScope using (Scoped)

import Semantics.Reduction.ISWIM as ISWIMᵣ
import Untyped.Semantics.Reduction.Clos2 as Clos2ᵣ
import Untyped.Semantics.Reduction.Clos3 as Clos3ᵣ
import Untyped.Semantics.Reduction.Clos4 as Clos4ᵣ
import Untyped.Semantics.Reduction.Clos5 as Clos5ᵣ
import Untyped.Semantics.CEK.Imp as Impₘ
import Untyped.Semantics.CEK.CFG as CFGₘ
import Semantics.CEK.X86 as X86ₘ

import proof.Correctness.Reduction.SimplifyRed as SimplifyRed
import Untyped.proof.Correctness.Reduction.CaptureRed as CaptureRed
import Untyped.proof.Correctness.Reduction.PruneRed as PruneRed
import Untyped.proof.Correctness.Reduction.ConcretizeRed as ConcretizeRed
import Untyped.proof.Correctness.Reduction.SplitRed as SplitRed
import Untyped.proof.Correctness.Reduction.HoistRed as HoistRed
import Untyped.proof.Correctness.Reduction.CompilerRed as CompilerRed
import Untyped.proof.Correctness.Reduction.RCORed as RCORed
import Untyped.proof.Correctness.Reduction.LiftLocalsRed as LiftLocalsRed
import Untyped.proof.Correctness.CEK.ExplicateSim as ExplicateSim
import Untyped.proof.Correctness.CEK.SelectSim as SelectSim
import Untyped.proof.Correctness.Reduction.CompilerX86Red as CompilerX86Red

{- Each pass ------------------------------------------------------------------}

{- simplify (ISWIM → ISWIM, the first pass), for closed programs -}
simplify-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (ISWIMᵣ.sem (simplify M))
simplify-correct = SimplifyRed.simplify-correct

{- capture, for closed programs -}
capture-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Clos2ᵣ.sem (capture M))
capture-correct = CaptureRed.capture-correct

{- prune, for well-scoped programs (which capture produces) -}
prune-correct : ∀ (M : Clos2.AST) → WS 0 M
  → Equivalent (Clos2ᵣ.sem M) (Clos2ᵣ.sem (prune-program M))
prune-correct = PruneRed.prune-correct

{- concretize, for well-scoped programs (which prune produces) -}
concretize-correct : ∀ (M : Clos2.AST) → WS 0 M
  → Equivalent (Clos2ᵣ.sem M) (Clos3ᵣ.sem (concretize-program M))
concretize-correct = ConcretizeRed.concretize-correct

split-correct : ∀ (M : Clos3.AST) → Equivalent (Clos3ᵣ.sem M) (Clos4ᵣ.sem (split M))
split-correct = SplitRed.split-correct

hoist-correct : ∀ (M : Clos4.AST) → Equivalent (Clos4ᵣ.sem M) (Clos5ᵣ.sem (hoist M))
hoist-correct = HoistRed.hoist-correct

{- remove complex operands, for well-scoped programs (which the compiler
   produces) -}
rco-correct : ∀ (P : Clos5.Program) → Scoped P
  → Equivalent (Clos5ᵣ.sem P) (Clos5ᵣ.sem (rco-program P))
rco-correct = RCORed.rco-correct

{- lift locals, for programs in monadic normal form (which rco produces) -}
lift-locals-correct : ∀ (P : Clos5.Program) (mp : MonProgram P)
  → Equivalent (Clos5ᵣ.sem P) (Impₘ.sem (lift-program P mp))
lift-locals-correct = LiftLocalsRed.lift-correct

{- explicate control and select instructions, between the machines of Imp,
   CFG and X86 (the proofs of the CEK machine + simulation development) -}
explicate-correct : ∀ (P : Imp.Program) → Equivalent (Impₘ.sem P) (CFGₘ.sem (explicate P))
explicate-correct = ExplicateSim.explicate-correct

select-correct : ∀ (P : CFG.Program) → Equivalent (CFGₘ.sem P) (X86ₘ.sem (select P))
select-correct = SelectSim.select-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Clos5ᵣ.sem (compile M))
compile-correct = CompilerRed.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Clos5ᵣ.sem (compile-mon M))
compile-mon-correct = RCORed.compile-mon-correct

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Impₘ.sem (compile-imp M))
compile-imp-correct = LiftLocalsRed.compile-imp-correct

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (CFGₘ.sem (compile-cfg M))
compile-cfg-correct = CompilerX86Red.compile-cfg-correct

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (X86ₘ.sem (compile-x86 M))
compile-x86-correct = CompilerX86Red.compile-x86-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, errors exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMᵣ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵣ.sem (compile M)) (o-const B k)
compile-const = CompilerRed.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMᵣ.sem M)) ⇔ Converges (Terminates (Clos5ᵣ.sem (compile M)))
compile-converges = CompilerRed.compile-converges

compile-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMᵣ.sem M) o-error ⇔ Terminates (Clos5ᵣ.sem (compile M)) o-error
compile-error = CompilerRed.compile-error

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMᵣ.sem M) ⇔ Diverges (Clos5ᵣ.sem (compile M))
compile-diverges = CompilerRed.compile-diverges
