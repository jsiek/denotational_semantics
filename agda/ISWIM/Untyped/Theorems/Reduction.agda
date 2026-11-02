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
  preconditions: Closed (ISWIM/Compiler/CaptureScope.agda), WS
  (Framework/Syntax/Scope.agda), Scoped
  (Compiler/PipelineScope.agda) and MonProgram
  (Language/Mon.agda).

-}

module ISWIM.Untyped.Theorems.Reduction where

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.Reduction.Smallstep using (Terminates; Diverges; Equivalent)

import ISWIM.Language.ISWIM as ISWIM
import ISWIM.Untyped.Language.Clos2 as Clos2
import ISWIM.Untyped.Language.Clos3 as Clos3
import ISWIM.Untyped.Language.Clos4 as Clos4
import ISWIM.Untyped.Language.Clos5 as Clos5
open import ISWIM.Untyped.Language.Mon using (MonProgram)
import ISWIM.Untyped.Language.Imp as Imp
import ISWIM.Untyped.Language.CFG as CFG

open import ISWIM.Compiler.Simplify using (simplify)
open import ISWIM.Untyped.Compiler.Capture using (capture)
open import ISWIM.Untyped.Compiler.Prune using (prune-program)
open import ISWIM.Untyped.Compiler.Concretize using (concretize-program)
open import ISWIM.Untyped.Compiler.Split using (split)
open import ISWIM.Untyped.Compiler.Hoist using (hoist)
open import ISWIM.Untyped.Compiler.RCO using (rco-program)
open import ISWIM.Untyped.Compiler.LiftLocals using (lift-program)
open import ISWIM.Untyped.Compiler.Explicate using (explicate)
open import ISWIM.Untyped.Compiler.Select using (select)
open import ISWIM.Untyped.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import ISWIM.Compiler.CaptureScope using (Closed)
open import Framework.Syntax.Scope Clos2.Op Clos2.sig using (WS)
open import ISWIM.Untyped.Compiler.PipelineScope using (Scoped)

import ISWIM.Semantics.Reduction.ISWIM as ISWIMᵣ
import ISWIM.Untyped.Semantics.Reduction.Clos2 as Clos2ᵣ
import ISWIM.Untyped.Semantics.Reduction.Clos3 as Clos3ᵣ
import ISWIM.Untyped.Semantics.Reduction.Clos4 as Clos4ᵣ
import ISWIM.Untyped.Semantics.Reduction.Clos5 as Clos5ᵣ
import ISWIM.Untyped.Semantics.CEK.Imp as Impₘ
import ISWIM.Untyped.Semantics.CEK.CFG as CFGₘ
import ISWIM.Semantics.CEK.X86 as X86ₘ

import ISWIM.proof.Correctness.Reduction.SimplifyRed as SimplifyRed
import ISWIM.Untyped.proof.Correctness.Reduction.CaptureRed as CaptureRed
import ISWIM.Untyped.proof.Correctness.Reduction.PruneRed as PruneRed
import ISWIM.Untyped.proof.Correctness.Reduction.ConcretizeRed as ConcretizeRed
import ISWIM.Untyped.proof.Correctness.Reduction.SplitRed as SplitRed
import ISWIM.Untyped.proof.Correctness.Reduction.HoistRed as HoistRed
import ISWIM.Untyped.proof.Correctness.Reduction.CompilerRed as CompilerRed
import ISWIM.Untyped.proof.Correctness.Reduction.RCORed as RCORed
import ISWIM.Untyped.proof.Correctness.Reduction.LiftLocalsRed as LiftLocalsRed
import ISWIM.Untyped.proof.Correctness.CEK.ExplicateSim as ExplicateSim
import ISWIM.Untyped.proof.Correctness.CEK.SelectSim as SelectSim
import ISWIM.Untyped.proof.Correctness.Reduction.CompilerX86Red as CompilerX86Red

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
