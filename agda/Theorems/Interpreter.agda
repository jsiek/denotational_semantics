{-

  The correctness of the compiler, by clocked interpreters and value
  relations: the public statements.
  The proofs (clock for clock) are in
  proof/Correctness/Interp/; each theorem here is one of
  them, with its type written out, so that it can be read without opening
  proof/.

    ISWIM --simplify--> ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  Each language has an interpreter with a clock
  (Semantics/Interp/, here Lᵢ.sem for language L): a program
  terminates with an observation (Semantics/Observation.agda) when, for
  some clock, it returns a value observed as o or errors (o-error),
  and diverges when it times out for every clock. Two programs are
  Equivalent (Framework/Clocked.agda) when each terminates with o exactly
  when the other does, and one diverges exactly when the other does.

  To read them: the languages (Language/), the passes
  (Compiler/), the interpreters, the observations, and the
  preconditions: Closed (Compiler/EncloseScope.agda), WS
  (Framework/Syntax/Scope.agda), Scoped (Compiler/PipelineScope.agda)
  and MonProgram (Language/Mon.agda).

-}

module Theorems.Interpreter where

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges; Equivalent)

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

import Semantics.Interp.ISWIM as ISWIMᵢ
import Semantics.Interp.Clos2 as Clos2ᵢ
import Semantics.Interp.Clos3 as Clos3ᵢ
import Semantics.Interp.Clos4 as Clos4ᵢ
import Semantics.Interp.Clos5 as Clos5ᵢ
import Semantics.Interp.Imp as Impᵢ
import Semantics.Interp.CFG as CFGᵢ
import Semantics.Interp.X86 as X86ᵢ

import proof.Correctness.Interp.SimplifyFuel as SimplifyFuel
import proof.Correctness.Interp.EncloseFuel as EncloseFuel
import proof.Correctness.Interp.OptimizeFuel as OptimizeFuel
import proof.Correctness.Interp.ConcretizeFuel as ConcretizeFuel
import proof.Correctness.Interp.DelayFuel as DelayFuel
import proof.Correctness.Interp.GlobalizeFuel as GlobalizeFuel
import proof.Correctness.Interp.RCOFuel as RCOFuel
import proof.Correctness.Interp.LiftLocalsFuel as LiftLocalsFuel
import proof.Correctness.Interp.ExplicateFuel as ExplicateFuel
import proof.Correctness.Interp.SelectFuel as SelectFuel
import proof.Correctness.Interp.CompilerFuel as CompilerFuel

{- Each pass ------------------------------------------------------------------}

{- simplify, for closed programs. Not clock for clock: simplify removes
   calls, so the simplified program needs no more clock than the original,
   which may need more (the proof relates the two at the same clock in one
   direction, and at some larger clock in the other) -}
simplify-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (ISWIMᵢ.sem (simplify M))
simplify-correct = SimplifyFuel.simplify-correct

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
   does, errors exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMᵢ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵢ.sem (compile M)) (o-const B k)
compile-const = CompilerFuel.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMᵢ.sem M)) ⇔ Converges (Terminates (Clos5ᵢ.sem (compile M)))
compile-converges = CompilerFuel.compile-converges

compile-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMᵢ.sem M) o-error ⇔ Terminates (Clos5ᵢ.sem (compile M)) o-error
compile-error = CompilerFuel.compile-error

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMᵢ.sem M) ⇔ Diverges (Clos5ᵢ.sem (compile M))
compile-diverges = CompilerFuel.compile-diverges
