{-

  The correctness of the compiler, by clocked interpreters and value
  relations: the public statements.
  The proofs (clock for clock) are in
  proof/Compiler/Functional/Correctness/; each theorem here is one of
  them, with its type written out, so that it can be read without opening
  proof/.

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  Each language has an interpreter with a clock
  (Compiler/Functional/Interp/, here Lᵢ.sem for language L): a program
  terminates with an observation (Compiler/Observation.agda) when, for
  some clock, it returns a value observed as o or goes wrong (o-wrong),
  and diverges when it times out for every clock. Two programs are
  Equivalent (Framework/Clocked.agda) when each terminates with o exactly
  when the other does, and one diverges exactly when the other does.

  To read them: the languages (Compiler/Lang/), the passes
  (Compiler/Compile/), the interpreters, the observations, and the
  preconditions: Closed (Compiler/Compile/EncloseScope.agda), WS
  (Framework/Syntax/Scope.agda), Scoped (Compiler/Compile/PipelineScope.agda)
  and MonProgram (Compiler/Lang/Mon.agda).

-}

module Theorems.Interpreter where

open import Compiler.Observation using (o-const; o-wrong; Converges; _⇔_)
open import Compiler.Functional.Clock using (Terminates; Diverges; Equivalent)

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

import Compiler.Functional.Interp.ISWIM as ISWIMᵢ
import Compiler.Functional.Interp.Clos2 as Clos2ᵢ
import Compiler.Functional.Interp.Clos3 as Clos3ᵢ
import Compiler.Functional.Interp.Clos4 as Clos4ᵢ
import Compiler.Functional.Interp.Clos5 as Clos5ᵢ
import Compiler.Functional.Interp.Imp as Impᵢ
import Compiler.Functional.Interp.CFG as CFGᵢ
import Compiler.Functional.Interp.X86 as X86ᵢ

import proof.Compiler.Functional.Correctness.EncloseFuel as EncloseFuel
import proof.Compiler.Functional.Correctness.OptimizeFuel as OptimizeFuel
import proof.Compiler.Functional.Correctness.ConcretizeFuel as ConcretizeFuel
import proof.Compiler.Functional.Correctness.DelayFuel as DelayFuel
import proof.Compiler.Functional.Correctness.GlobalizeFuel as GlobalizeFuel
import proof.Compiler.Functional.Correctness.RCOFuel as RCOFuel
import proof.Compiler.Functional.Correctness.LiftLocalsFuel as LiftLocalsFuel
import proof.Compiler.Functional.Correctness.ExplicateFuel as ExplicateFuel
import proof.Compiler.Functional.Correctness.SelectFuel as SelectFuel
import proof.Compiler.Functional.Correctness.CompilerFuel as CompilerFuel

{- Each pass ------------------------------------------------------------------}

{- enclose, for closed programs -}
enclose-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Clos2ᵢ.sem (enclose M))
enclose-correct = EncloseFuel.enclose-correct

{- optimize, for well-scoped programs (which enclose produces) -}
optimize-correct : ∀ (M : Clos2.AST) → WS 0 M
  → Equivalent (Clos2ᵢ.sem M) (Clos2ᵢ.sem (optimize-program M))
optimize-correct = OptimizeFuel.optimize-correct

concretize-correct : ∀ (M : Clos2.AST)
  → Equivalent (Clos2ᵢ.sem M) (Clos3ᵢ.sem (concretize-program M))
concretize-correct = ConcretizeFuel.concretize-correct

delay-correct : ∀ (M : Clos3.AST) → Equivalent (Clos3ᵢ.sem M) (Clos4ᵢ.sem (delay M))
delay-correct = DelayFuel.delay-correct

globalize-correct : ∀ (M : Clos4.AST) → Equivalent (Clos4ᵢ.sem M) (Clos5ᵢ.sem (globalize M))
globalize-correct = GlobalizeFuel.globalize-correct

{- remove complex operands, for well-scoped programs (which the compiler
   produces) -}
rco-correct : ∀ (P : Clos5.Program) → Scoped P
  → Equivalent (Clos5ᵢ.sem P) (Clos5ᵢ.sem (rco-program P))
rco-correct = RCOFuel.rco-correct

{- lift locals, for programs in monadic normal form (which rco produces) -}
lift-locals-correct : ∀ (P : Clos5.Program) (mp : MonProgram P)
  → Equivalent (Clos5ᵢ.sem P) (Impᵢ.sem (lift-program P mp))
lift-locals-correct = LiftLocalsFuel.lift-correct

explicate-correct : ∀ (P : Imp.Program) → Equivalent (Impᵢ.sem P) (CFGᵢ.sem (explicate P))
explicate-correct = ExplicateFuel.explicate-correct

select-correct : ∀ (P : CFG.Program) → Equivalent (CFGᵢ.sem P) (X86ᵢ.sem (select P))
select-correct = SelectFuel.select-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Clos5ᵢ.sem (compile M))
compile-correct = CompilerFuel.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Clos5ᵢ.sem (compile-mon M))
compile-mon-correct = RCOFuel.compile-mon-correct

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Impᵢ.sem (compile-imp M))
compile-imp-correct = LiftLocalsFuel.compile-imp-correct

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (CFGᵢ.sem (compile-cfg M))
compile-cfg-correct = ExplicateFuel.compile-cfg-correct

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (X86ᵢ.sem (compile-x86 M))
compile-x86-correct = SelectFuel.compile-x86-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, goes wrong exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMᵢ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵢ.sem (compile M)) (o-const B k)
compile-const = CompilerFuel.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMᵢ.sem M)) ⇔ Converges (Terminates (Clos5ᵢ.sem (compile M)))
compile-converges = CompilerFuel.compile-converges

compile-wrong : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMᵢ.sem M) o-wrong ⇔ Terminates (Clos5ᵢ.sem (compile M)) o-wrong
compile-wrong = CompilerFuel.compile-wrong

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMᵢ.sem M) ⇔ Diverges (Clos5ᵢ.sem (compile M))
compile-diverges = CompilerFuel.compile-diverges
