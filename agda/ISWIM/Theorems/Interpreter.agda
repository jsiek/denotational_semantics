{-

  The correctness of the compiler (ISWIM/Compiler/Pipeline.agda),
  by clocked interpreters and value relations: the public statements.
  The proofs (clock for clock) are in ISWIM/proof/Correctness/Interp/;
  each theorem here is one of them, with its type written out.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --capture--> Clos2ᵀ
          --prune--> Clos2ᵀ --concretize--> Clos3ᵀ --split--> Clos4ᵀ
          --hoist--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

  Each language has an interpreter with a clock (ISWIM/Semantics/Interp/ for
  ISWIM, ISWIM/Semantics/Interp/Typed/ for the typed languages, X86ᵀ among
  them; here Lᵢ.sem for language L). A typed interpreter is a total
  function of typed terms to typed values, which errs only where a
  project fails (in X86ᵀ, at chk, project's check).
  Monᵀ runs as its embedding ⌜ P ⌝ₚ into Clos5ᵀ. A program terminates
  with an observation (Semantics/Observation.agda) when, for some clock,
  it returns a value observed as o or errors (o-error), and diverges
  when it times out for every clock. Two programs are Equivalent
  (Framework/Clocked.agda) when each terminates with o exactly when the
  other does, and one diverges exactly when the other does.

  To read them: the languages (ISWIM/Language/, ISWIM/Language/Typed/), the
  passes (ISWIM/Compiler/), the interpreters, the observations, and
  the precondition Closed (ISWIM/Compiler/CaptureScope.agda).

-}

module ISWIM.Theorems.Interpreter where

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges; Equivalent)

import ISWIM.Language.ISWIM as ISWIM
open import ISWIM.Language.Typed.Type using (Any)
import ISWIM.Language.Typed.ISWIM as ISWIMᵀ
import ISWIM.Language.Typed.Clos2 as Clos2ᵀ
import ISWIM.Language.Typed.Clos3 as Clos3ᵀ
import ISWIM.Language.Typed.Clos4 as Clos4ᵀ
import ISWIM.Language.Typed.Clos5 as Clos5ᵀ
import ISWIM.Language.Typed.Mon as Monᵀ
open Monᵀ using (⌜_⌝ₚ)
import ISWIM.Language.Typed.Imp as Impᵀ
import ISWIM.Language.Typed.CFG as CFGᵀ
open import Data.List using ([])

open import ISWIM.Compiler.Simplify using (simplify)
open import ISWIM.Compiler.Cast using (cast-closed)
open import ISWIM.Compiler.Capture using (capture)
open import ISWIM.Compiler.Prune using (prune-program)
open import ISWIM.Compiler.Concretize using (concretize-program)
open import ISWIM.Compiler.Split using (split-program)
open import ISWIM.Compiler.Hoist using (hoist)
open import ISWIM.Compiler.RCO using (rco-program)
open import ISWIM.Compiler.LiftLocals using (lift-program)
open import ISWIM.Compiler.Explicate using (explicate)
open import ISWIM.Compiler.Select using (select)
open import ISWIM.Compiler.Pipeline using (compile; compile-mon; compile-imp;
  compile-cfg; compile-x86)
open import ISWIM.Compiler.CaptureScope using (Closed)

import ISWIM.Semantics.Interp.ISWIM as ISWIMᵢ
import ISWIM.Semantics.Interp.Typed.ISWIM as ISWIMᵀᵢ
import ISWIM.Semantics.Interp.Typed.Clos2 as Clos2ᵀᵢ
import ISWIM.Semantics.Interp.Typed.Clos3 as Clos3ᵀᵢ
import ISWIM.Semantics.Interp.Typed.Clos4 as Clos4ᵀᵢ
import ISWIM.Semantics.Interp.Typed.Clos5 as Clos5ᵀᵢ
import ISWIM.Semantics.Interp.Typed.Imp as Impᵀᵢ
import ISWIM.Semantics.Interp.Typed.CFG as CFGᵀᵢ
import ISWIM.Semantics.Interp.Typed.X86 as X86ᵀᵢ

import ISWIM.proof.Correctness.Interp.SimplifyFuel as SimplifyFuel
import ISWIM.proof.Correctness.Interp.CastFuel as CastFuel
import ISWIM.proof.Correctness.Interp.CaptureFuel as CaptureFuel
import ISWIM.proof.Correctness.Interp.PruneFuel as PruneFuel
import ISWIM.proof.Correctness.Interp.ConcretizeFuel as ConcretizeFuel
import ISWIM.proof.Correctness.Interp.SplitFuel as SplitFuel
import ISWIM.proof.Correctness.Interp.HoistFuel as HoistFuel
import ISWIM.proof.Correctness.Interp.RCOFuel as RCOFuel
import ISWIM.proof.Correctness.Interp.LiftLocalsFuel as LiftLocalsFuel
import ISWIM.proof.Correctness.Interp.ExplicateFuel as ExplicateFuel
import ISWIM.proof.Correctness.Interp.SelectFuel as SelectFuel
import ISWIM.proof.Correctness.Interp.CompilerFuel as CompilerFuel

{- Each pass ------------------------------------------------------------------}

{- simplify, for closed programs (clock-monotone) -}
simplify-correct : ∀ (M : ISWIM.AST)
  → Closed M
  → Equivalent (ISWIMᵢ.sem M) (ISWIMᵢ.sem (simplify M))
simplify-correct = SimplifyFuel.simplify-correct

cast-correct : ∀ (M : ISWIM.AST)
  → Closed M
  → Equivalent (ISWIMᵢ.sem M) (ISWIMᵀᵢ.sem (cast-closed M))
cast-correct = CastFuel.cast-correct

capture-correct : ∀ (M : ISWIMᵀ.Tm 0 Any)
  → Equivalent (ISWIMᵀᵢ.sem M) (Clos2ᵀᵢ.sem (capture M))
capture-correct = CaptureFuel.capture-correct

prune-correct : ∀ (M : Clos2ᵀ.Tm 0 Any)
  → Equivalent (Clos2ᵀᵢ.sem M) (Clos2ᵀᵢ.sem (prune-program M))
prune-correct = PruneFuel.prune-correct

concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any)
  → Equivalent (Clos2ᵀᵢ.sem M) (Clos3ᵀᵢ.sem (concretize-program M))
concretize-correct = ConcretizeFuel.concretize-correct

split-correct : ∀ (M : Clos3ᵀ.Tm [] Any)
  → Equivalent (Clos3ᵀᵢ.sem M) (Clos4ᵀᵢ.sem (split-program M))
split-correct = SplitFuel.split-correct

hoist-correct : ∀ (M : Clos4ᵀ.Tm [] Any)
  → Equivalent (Clos4ᵀᵢ.sem M) (Clos5ᵀᵢ.sem (hoist M))
hoist-correct = HoistFuel.hoist-correct

rco-correct : ∀ (P : Clos5ᵀ.Program)
  → Equivalent (Clos5ᵀᵢ.sem P) (Clos5ᵀᵢ.sem ⌜ rco-program P ⌝ₚ)
rco-correct = RCOFuel.rco-correct

lift-locals-correct : ∀ (P : Monᵀ.Program)
  → Equivalent (Clos5ᵀᵢ.sem ⌜ P ⌝ₚ) (Impᵀᵢ.sem (lift-program P))
lift-locals-correct = LiftLocalsFuel.lift-locals-correct

explicate-correct : ∀ (P : Impᵀ.Program)
  → Equivalent (Impᵀᵢ.sem P) (CFGᵀᵢ.sem (explicate P))
explicate-correct = ExplicateFuel.explicate-correct

{- X86ᵀ's only error is chk, project's check: the X86ᵀ program gives the
   result of the CFGᵀ one -}
select-correct : ∀ (P : CFGᵀ.Program)
  → Equivalent (CFGᵀᵢ.sem P) (X86ᵀᵢ.sem (select P))
select-correct = SelectFuel.select-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST)
  → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Clos5ᵀᵢ.sem (compile M))
compile-correct = CompilerFuel.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST)
  → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Clos5ᵀᵢ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct = CompilerFuel.compile-mon-correct

compile-imp-correct : ∀ (M : ISWIM.AST)
  → Closed M
  → Equivalent (ISWIMᵢ.sem M) (Impᵀᵢ.sem (compile-imp M))
compile-imp-correct = CompilerFuel.compile-imp-correct

compile-cfg-correct : ∀ (M : ISWIM.AST)
  → Closed M
  → Equivalent (ISWIMᵢ.sem M) (CFGᵀᵢ.sem (compile-cfg M))
compile-cfg-correct = CompilerFuel.compile-cfg-correct

compile-x86-correct : ∀ (M : ISWIM.AST)
  → Closed M
  → Equivalent (ISWIMᵢ.sem M) (X86ᵀᵢ.sem (compile-x86 M))
compile-x86-correct = CompilerFuel.compile-x86-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, errors exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST)
  → Closed M
  → ∀ B k
  → Terminates (ISWIMᵢ.sem M) (o-const B k)
    ⇔ Terminates (Clos5ᵀᵢ.sem (compile M)) (o-const B k)
compile-const = CompilerFuel.compile-const

compile-converges : ∀ (M : ISWIM.AST)
  → Closed M
  → Converges (Terminates (ISWIMᵢ.sem M))
    ⇔ Converges (Terminates (Clos5ᵀᵢ.sem (compile M)))
compile-converges = CompilerFuel.compile-converges

compile-error : ∀ (M : ISWIM.AST)
  → Closed M
  → Terminates (ISWIMᵢ.sem M) o-error
    ⇔ Terminates (Clos5ᵀᵢ.sem (compile M)) o-error
compile-error = CompilerFuel.compile-error

compile-diverges : ∀ (M : ISWIM.AST)
  → Closed M
  → Diverges (ISWIMᵢ.sem M) ⇔ Diverges (Clos5ᵀᵢ.sem (compile M))
compile-diverges = CompilerFuel.compile-diverges
