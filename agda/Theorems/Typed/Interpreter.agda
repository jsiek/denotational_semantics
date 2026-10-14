{-

  The correctness of the typed compiler (Compiler/Typed/Pipeline.agda),
  by clocked interpreters and value relations: the public statements.
  The proofs (clock for clock) are in proof/Correctness/Interp/Typed/;
  each theorem here is one of them, with its type written out.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86

  Each language has an interpreter with a clock (Semantics/Interp/ for
  ISWIM and X86, Semantics/Interp/Typed/ for the typed languages; here
  Lᵢ.sem for language L). A typed interpreter is a total function of
  typed terms to typed values, which errs only where a project fails.
  Monᵀ runs as its embedding ⌜ P ⌝ₚ into Clos5ᵀ. A program terminates
  with an observation (Semantics/Observation.agda) when, for some clock,
  it returns a value observed as o or errors (o-error), and diverges
  when it times out for every clock. Two programs are Equivalent
  (Framework/Clocked.agda) when each terminates with o exactly when the
  other does, and one diverges exactly when the other does.

  To read them: the languages (Language/, Language/Typed/), the passes
  (Compiler/, Compiler/Typed/), the interpreters, the observations, and
  the precondition Closed (Compiler/EncloseScope.agda).

-}

module Theorems.Typed.Interpreter where

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges; Equivalent)

import Language.ISWIM as ISWIM
open import Language.Typed.Type using (Any)
import Language.Typed.ISWIM as ISWIMᵀ
import Language.Typed.Clos2 as Clos2ᵀ
import Language.Typed.Clos3 as Clos3ᵀ
import Language.Typed.Clos4 as Clos4ᵀ
import Language.Typed.Clos5 as Clos5ᵀ
import Language.Typed.Mon as Monᵀ
open Monᵀ using (⌜_⌝ₚ)
import Language.Typed.Imp as Impᵀ
import Language.Typed.CFG as CFGᵀ
open import Data.List using ([])

open import Compiler.Simplify using (simplify)
open import Compiler.Typed.Cast using (cast-closed)
open import Compiler.Typed.Enclose using (enclose)
open import Compiler.Typed.Optimize using (optimize-program)
open import Compiler.Typed.Concretize using (concretize-program)
open import Compiler.Typed.Delay using (delay-program)
open import Compiler.Typed.Globalize using (globalize)
open import Compiler.Typed.RCO using (rco-program)
open import Compiler.Typed.LiftLocals using (lift-program)
open import Compiler.Typed.Explicate using (explicate)
open import Compiler.Typed.Select using (select)
open import Compiler.Typed.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Compiler.EncloseScope using (Closed)

import Semantics.Interp.ISWIM as ISWIMᵢ
import Semantics.Interp.Typed.ISWIM as ISWIMᵀᵢ
import Semantics.Interp.Typed.Clos2 as Clos2ᵀᵢ
import Semantics.Interp.Typed.Clos3 as Clos3ᵀᵢ
import Semantics.Interp.Typed.Clos4 as Clos4ᵀᵢ
import Semantics.Interp.Typed.Clos5 as Clos5ᵀᵢ
import Semantics.Interp.Typed.Imp as Impᵀᵢ
import Semantics.Interp.Typed.CFG as CFGᵀᵢ
import Semantics.Interp.X86 as X86ᵢ

import proof.Correctness.Interp.SimplifyFuel as SimplifyFuel
import proof.Correctness.Interp.Typed.CastFuel as CastFuel
import proof.Correctness.Interp.Typed.EncloseFuel as EncloseFuel
import proof.Correctness.Interp.Typed.OptimizeFuel as OptimizeFuel
import proof.Correctness.Interp.Typed.ConcretizeFuel as ConcretizeFuel
import proof.Correctness.Interp.Typed.DelayFuel as DelayFuel
import proof.Correctness.Interp.Typed.GlobalizeFuel as GlobalizeFuel
import proof.Correctness.Interp.Typed.RCOFuel as RCOFuel
import proof.Correctness.Interp.Typed.LiftLocalsFuel as LiftLocalsFuel
import proof.Correctness.Interp.Typed.ExplicateFuel as ExplicateFuel
import proof.Correctness.Interp.Typed.SelectFuel as SelectFuel
import proof.Correctness.Interp.Typed.CompilerFuel as CompilerFuel

{- Each pass ------------------------------------------------------------------}

{- simplify, for closed programs (unchanged; clock-monotone) -}
simplify-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (ISWIMᵢ.sem (simplify M))
simplify-correct = SimplifyFuel.simplify-correct

cast-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵢ.sem M) (ISWIMᵀᵢ.sem (cast-closed M))
cast-correct = CastFuel.cast-correct

enclose-correct : ∀ (M : ISWIMᵀ.Tm 0 Any) → Equivalent (ISWIMᵀᵢ.sem M) (Clos2ᵀᵢ.sem (enclose M))
enclose-correct = EncloseFuel.enclose-correct

optimize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵢ.sem M) (Clos2ᵀᵢ.sem (optimize-program M))
optimize-correct = OptimizeFuel.optimize-correct

concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵢ.sem M) (Clos3ᵀᵢ.sem (concretize-program M))
concretize-correct = ConcretizeFuel.concretize-correct

delay-correct : ∀ (M : Clos3ᵀ.Tm [] Any) → Equivalent (Clos3ᵀᵢ.sem M) (Clos4ᵀᵢ.sem (delay-program M))
delay-correct = DelayFuel.delay-correct

globalize-correct : ∀ (M : Clos4ᵀ.Tm [] Any) → Equivalent (Clos4ᵀᵢ.sem M) (Clos5ᵀᵢ.sem (globalize M))
globalize-correct = GlobalizeFuel.globalize-correct

rco-correct : ∀ (P : Clos5ᵀ.Program) → Equivalent (Clos5ᵀᵢ.sem P) (Clos5ᵀᵢ.sem ⌜ rco-program P ⌝ₚ)
rco-correct = RCOFuel.rco-correct

lift-locals-correct : ∀ (P : Monᵀ.Program) → Equivalent (Clos5ᵀᵢ.sem ⌜ P ⌝ₚ) (Impᵀᵢ.sem (lift-program P))
lift-locals-correct = LiftLocalsFuel.lift-locals-correct

explicate-correct : ∀ (P : Impᵀ.Program) → Equivalent (Impᵀᵢ.sem P) (CFGᵀᵢ.sem (explicate P))
explicate-correct = ExplicateFuel.explicate-correct

{- X86's own errors are unreachable: the X86 program gives the erased
   result of the CFGᵀ one -}
select-correct : ∀ (P : CFGᵀ.Program) → Equivalent (CFGᵀᵢ.sem P) (X86ᵢ.sem (select P))
select-correct = SelectFuel.select-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Clos5ᵀᵢ.sem (compile M))
compile-correct = CompilerFuel.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Clos5ᵀᵢ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct = CompilerFuel.compile-mon-correct

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Impᵀᵢ.sem (compile-imp M))
compile-imp-correct = CompilerFuel.compile-imp-correct

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (CFGᵀᵢ.sem (compile-cfg M))
compile-cfg-correct = CompilerFuel.compile-cfg-correct

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵢ.sem M) (X86ᵢ.sem (compile-x86 M))
compile-x86-correct = CompilerFuel.compile-x86-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, errors exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMᵢ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵀᵢ.sem (compile M)) (o-const B k)
compile-const = CompilerFuel.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMᵢ.sem M)) ⇔ Converges (Terminates (Clos5ᵀᵢ.sem (compile M)))
compile-converges = CompilerFuel.compile-converges

compile-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMᵢ.sem M) o-error ⇔ Terminates (Clos5ᵀᵢ.sem (compile M)) o-error
compile-error = CompilerFuel.compile-error

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMᵢ.sem M) ⇔ Diverges (Clos5ᵀᵢ.sem (compile M))
compile-diverges = CompilerFuel.compile-diverges
