{-

  The correctness of the compiler, by CEK machines and simulations: the
  public statements.
  The proofs (forward simulations) are in
  proof/Correctness/CEK/; each theorem here is one of
  them, with its type written out, so that it can be read without opening
  proof/.

    ISWIM --simplify--> ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  Each language has a small-step machine (Semantics/CEK/,
  here Lₘ.sem for language L), which terminates with an observation
  (Semantics/Observation.agda) or diverges. Two machines are Equivalent
  (Framework/Smallstep.agda) when each terminates with o exactly when the
  other does (o-wrong, going wrong, included), and one diverges exactly
  when the other does.

  To read them: the languages (Language/), the passes
  (Compiler/), the machines, the observations, and the
  preconditions: Closed (Compiler/EncloseScope.agda), WS
  (Framework/Syntax/Scope.agda), Scoped (Compiler/PipelineScope.agda)
  and MonProgram (Language/Mon.agda).

-}

module Theorems.Simulation where

open import Semantics.Observation using (o-const; o-wrong; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges; Equivalent)

import Language.ISWIM as ISWIM
import Language.Clos2 as Clos2
import Language.Clos3 as Clos3
import Language.Clos4 as Clos4
import Language.Clos5 as Clos5
open import Language.Mon using (MonProgram)
import Language.Imp as Imp
import Language.CFG as CFG

open import Compiler.Simplify using (simplify)
open import Compiler.Enclose using (enclose)
open import Compiler.Optimize using (optimize-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Delay using (delay)
open import Compiler.Globalize using (globalize)
open import Compiler.RCO using (rco-program)
open import Compiler.LiftLocals using (lift-program)
open import Compiler.Explicate using (explicate)
open import Compiler.Select using (select)
open import Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import Compiler.EncloseScope using (Closed)
open import Framework.Syntax.Scope Clos2.Op Clos2.sig using (WS)
open import Compiler.PipelineScope using (Scoped)

import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Clos2 as Clos2ₘ
import Semantics.CEK.Clos3 as Clos3ₘ
import Semantics.CEK.Clos4 as Clos4ₘ
import Semantics.CEK.Clos5 as Clos5ₘ
import Semantics.CEK.Imp as Impₘ
import Semantics.CEK.CFG as CFGₘ
import Semantics.CEK.X86 as X86ₘ

import proof.Correctness.CEK.SimplifySim as SimplifySim
import proof.Correctness.CEK.EncloseSim as EncloseSim
import proof.Correctness.CEK.OptimizeSim as OptimizeSim
import proof.Correctness.CEK.ConcretizeSim as ConcretizeSim
import proof.Correctness.CEK.DelaySim as DelaySim
import proof.Correctness.CEK.GlobalizeSim as GlobalizeSim
import proof.Correctness.CEK.RCOSim as RCOSim
import proof.Correctness.CEK.LiftLocalsSim as LiftLocalsSim
import proof.Correctness.CEK.ExplicateSim as ExplicateSim
import proof.Correctness.CEK.SelectSim as SelectSim
import proof.Correctness.CEK.CompilerSim as CompilerSim
import proof.Correctness.CEK.CompilerX86Sim as CompilerX86Sim

{- Each pass ------------------------------------------------------------------}

{- simplify, for closed programs -}
simplify-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (ISWIMₘ.sem (simplify M))
simplify-correct = SimplifySim.simplify-correct

{- enclose, for closed programs -}
enclose-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (Clos2ₘ.sem (enclose M))
enclose-correct = EncloseSim.enclose-correct

{- optimize, for well-scoped programs (which enclose produces) -}
optimize-correct : ∀ (M : Clos2.AST) → WS 0 M
  → Equivalent (Clos2ₘ.sem M) (Clos2ₘ.sem (optimize-program M))
optimize-correct = OptimizeSim.optimize-correct

concretize-correct : ∀ (M : Clos2.AST)
  → Equivalent (Clos2ₘ.sem M) (Clos3ₘ.sem (concretize-program M))
concretize-correct = ConcretizeSim.concretize-correct

delay-correct : ∀ (M : Clos3.AST) → Equivalent (Clos3ₘ.sem M) (Clos4ₘ.sem (delay M))
delay-correct = DelaySim.delay-correct

globalize-correct : ∀ (M : Clos4.AST) → Equivalent (Clos4ₘ.sem M) (Clos5ₘ.sem (globalize M))
globalize-correct = GlobalizeSim.globalize-correct

{- remove complex operands, for well-scoped programs (which the compiler
   produces) -}
rco-correct : ∀ (P : Clos5.Program) → Scoped P
  → Equivalent (Clos5ₘ.sem P) (Clos5ₘ.sem (rco-program P))
rco-correct = RCOSim.rco-correct

{- lift locals, for programs in monadic normal form (which rco produces) -}
lift-locals-correct : ∀ (P : Clos5.Program) (mp : MonProgram P)
  → Equivalent (Clos5ₘ.sem P) (Impₘ.sem (lift-program P mp))
lift-locals-correct = LiftLocalsSim.lift-correct

explicate-correct : ∀ (P : Imp.Program) → Equivalent (Impₘ.sem P) (CFGₘ.sem (explicate P))
explicate-correct = ExplicateSim.explicate-correct

select-correct : ∀ (P : CFG.Program) → Equivalent (CFGₘ.sem P) (X86ₘ.sem (select P))
select-correct = SelectSim.select-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (Clos5ₘ.sem (compile M))
compile-correct = CompilerSim.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (Clos5ₘ.sem (compile-mon M))
compile-mon-correct = RCOSim.compile-mon-correct

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (Impₘ.sem (compile-imp M))
compile-imp-correct = LiftLocalsSim.compile-imp-correct

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (CFGₘ.sem (compile-cfg M))
compile-cfg-correct = CompilerX86Sim.compile-cfg-correct

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMₘ.sem M) (X86ₘ.sem (compile-x86 M))
compile-x86-correct = CompilerX86Sim.compile-x86-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, goes wrong exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (Clos5ₘ.sem (compile M)) (o-const B k)
compile-const = CompilerSim.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (Clos5ₘ.sem (compile M)))
compile-converges = CompilerSim.compile-converges

compile-wrong : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-wrong ⇔ Terminates (Clos5ₘ.sem (compile M)) o-wrong
compile-wrong = CompilerSim.compile-wrong

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (Clos5ₘ.sem (compile M))
compile-diverges = CompilerSim.compile-diverges
