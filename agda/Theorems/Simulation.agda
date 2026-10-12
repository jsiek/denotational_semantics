{-

  The correctness of the compiler, by CEK machines and simulations: the
  public statements.
  The proofs (forward simulations) are in
  proof/Compiler/Operational/Correctness/; each theorem here is one of
  them, with its type written out, so that it can be read without opening
  proof/.

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  Each language has a small-step machine (Compiler/Operational/Machine/,
  here Lₘ.sem for language L), which terminates with an observation
  (Compiler/Observation.agda) or diverges. Two machines are Equivalent
  (Framework/Smallstep.agda) when each terminates with o exactly when the
  other does (o-wrong, going wrong, included), and one diverges exactly
  when the other does.

  To read them: the languages (Compiler/Lang/), the passes
  (Compiler/Compile/), the machines, the observations, and the
  preconditions: Closed (Compiler/Compile/EncloseScope.agda), WS
  (Framework/Syntax/Scope.agda), Scoped (Compiler/Compile/PipelineScope.agda)
  and MonProgram (Compiler/Lang/Mon.agda).

-}

module Theorems.Simulation where

open import Compiler.Observation using (o-const; o-wrong; Converges; _⇔_)
open import Compiler.Operational.Smallstep using (Terminates; Diverges; Equivalent)

import Compiler.Lang.ISWIM as ISWIM
import Compiler.Lang.Clos2 as Clos2
import Compiler.Lang.Clos3 as Clos3
import Compiler.Lang.Clos4 as Clos4
import Compiler.Lang.Clos5 as Clos5
open import Compiler.Lang.Mon using (MonProgram)
import Compiler.Lang.Imp as Imp
import Compiler.Lang.CFG as CFG

open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Compile.Optimize using (optimize-program)
open import Compiler.Compile.Concretize using (concretize-program)
open import Compiler.Compile.Delay using (delay)
open import Compiler.Compile.Globalize using (globalize)
open import Compiler.Compile.RCO using (rco-program)
open import Compiler.Compile.LiftLocals using (lift-program)
open import Compiler.Compile.Explicate using (explicate)
open import Compiler.Compile.Select using (select)
open import Compiler.Compile.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import Compiler.Compile.EncloseScope using (Closed)
open import Framework.Syntax.Scope Clos2.Op Clos2.sig using (WS)
open import Compiler.Compile.PipelineScope using (Scoped)

import Compiler.Operational.Machine.ISWIM as ISWIMₘ
import Compiler.Operational.Machine.Clos2 as Clos2ₘ
import Compiler.Operational.Machine.Clos3 as Clos3ₘ
import Compiler.Operational.Machine.Clos4 as Clos4ₘ
import Compiler.Operational.Machine.Clos5 as Clos5ₘ
import Compiler.Operational.Machine.Imp as Impₘ
import Compiler.Operational.Machine.CFG as CFGₘ
import Compiler.Operational.Machine.X86 as X86ₘ

import proof.Compiler.Operational.Correctness.EncloseSim as EncloseSim
import proof.Compiler.Operational.Correctness.OptimizeSim as OptimizeSim
import proof.Compiler.Operational.Correctness.ConcretizeSim as ConcretizeSim
import proof.Compiler.Operational.Correctness.DelaySim as DelaySim
import proof.Compiler.Operational.Correctness.GlobalizeSim as GlobalizeSim
import proof.Compiler.Operational.Correctness.RCOSim as RCOSim
import proof.Compiler.Operational.Correctness.LiftLocalsSim as LiftLocalsSim
import proof.Compiler.Operational.Correctness.ExplicateSim as ExplicateSim
import proof.Compiler.Operational.Correctness.SelectSim as SelectSim
import proof.Compiler.Operational.Correctness.CompilerSim as CompilerSim
import proof.Compiler.Operational.Correctness.CompilerX86Sim as CompilerX86Sim

{- Each pass ------------------------------------------------------------------}

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
