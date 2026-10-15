{-

  The correctness of the ISWIMμ compiler (Mu/Compiler/Pipeline.agda), by
  clocked interpreters and value relations: the public statements. The
  proofs (clock for clock; for simplify, which removes calls,
  clock-monotone) are in Mu/proof/Correctness/Interp/; each theorem here
  is one of them, with its type written out.

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ
           --concretize--> Clos3μ --delay--> Clos4μ --globalize--> Clos5μ
           --rco--> Monμ --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  Each language has an interpreter with a clock (here Lᵢ.sem for
  language L, Mu/Semantics/Interp/), down to the typed assembly language
  X86μ: a total function of typed terms to typed values. Monμ runs as
  its embedding ⌜ P ⌝ₚ into Clos5μ. A program terminates with an
  observation (Semantics/Observation.agda) when, for some clock, it
  returns a value observed as o, and diverges when it times out for
  every clock. Two programs are Equivalent (Framework/Clocked.agda) when
  each terminates with o exactly when the other does, and one diverges
  exactly when the other does.

  To read them: the languages (Mu/Language/), the passes (Mu/Compiler/),
  the interpreters and the observations.

-}

module Mu.Theorems.Interpreter where

open import Framework.Primitives using (Int)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges; Equivalent)

open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.Clos2 as Clos2μ
import Mu.Language.Clos3 as Clos3μ
import Mu.Language.Clos4 as Clos4μ
import Mu.Language.Clos5 as Clos5μ
import Mu.Language.Mon as Monμ
open Monμ using (⌜_⌝ₚ)
import Mu.Language.Imp as Impμ
import Mu.Language.CFG as CFGμ

open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Delay using (delay-program)
open import Mu.Compiler.Globalize using (globalize)
open import Mu.Compiler.RCO using (rco-program)
open import Mu.Compiler.LiftLocals using (lift-program)
open import Mu.Compiler.Explicate using (explicate)
open import Mu.Compiler.Select using (select)
open import Mu.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

import Mu.Semantics.Interp.ISWIM as ISWIMμᵢ
import Mu.Semantics.Interp.Clos2 as Clos2μᵢ
import Mu.Semantics.Interp.Clos3 as Clos3μᵢ
import Mu.Semantics.Interp.Clos4 as Clos4μᵢ
import Mu.Semantics.Interp.Clos5 as Clos5μᵢ
import Mu.Semantics.Interp.Imp as Impμᵢ
import Mu.Semantics.Interp.CFG as CFGμᵢ
import Mu.Semantics.Interp.X86 as X86μᵢ

import Mu.proof.Correctness.Interp.SimplifyFuel as SimplifyFuel
import Mu.proof.Correctness.Interp.EncloseFuel as EncloseFuel
import Mu.proof.Correctness.Interp.OptimizeFuel as OptimizeFuel
import Mu.proof.Correctness.Interp.ConcretizeFuel as ConcretizeFuel
import Mu.proof.Correctness.Interp.DelayFuel as DelayFuel
import Mu.proof.Correctness.Interp.GlobalizeFuel as GlobalizeFuel
import Mu.proof.Correctness.Interp.RCOFuel as RCOFuel
import Mu.proof.Correctness.Interp.LiftLocalsFuel as LiftLocalsFuel
import Mu.proof.Correctness.Interp.ExplicateFuel as ExplicateFuel
import Mu.proof.Correctness.Interp.SelectFuel as SelectFuel
import Mu.proof.Correctness.Interp.CompilerFuel as CompilerFuel

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Each pass ------------------------------------------------------------------}

simplify-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (ISWIMμᵢ.sem (simplify M))
simplify-correct = SimplifyFuel.simplify-correct

enclose-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Clos2μᵢ.sem (enclose M))
enclose-correct = EncloseFuel.enclose-correct

optimize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → Equivalent (Clos2μᵢ.sem M) (Clos2μᵢ.sem (optimize-program M))
optimize-correct = OptimizeFuel.optimize-correct

concretize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → Equivalent (Clos2μᵢ.sem M) (Clos3μᵢ.sem (concretize-program M))
concretize-correct = ConcretizeFuel.concretize-correct

delay-correct : ∀ {A} (M : Clos3μ.Tm [] A) → Equivalent (Clos3μᵢ.sem M) (Clos4μᵢ.sem (delay-program M))
delay-correct = DelayFuel.delay-correct

globalize-correct : ∀ {A} (M : Clos4μ.Tm [] A) → Equivalent (Clos4μᵢ.sem M) (Clos5μᵢ.sem (globalize M))
globalize-correct = GlobalizeFuel.globalize-correct

rco-correct : ∀ {A} (P : Clos5μ.Program A) → Equivalent (Clos5μᵢ.sem P) (Clos5μᵢ.sem ⌜ rco-program P ⌝ₚ)
rco-correct = RCOFuel.rco-correct

lift-locals-correct : ∀ {A} (P : Monμ.Program A) → Equivalent (Clos5μᵢ.sem ⌜ P ⌝ₚ) (Impμᵢ.sem (lift-program P))
lift-locals-correct = LiftLocalsFuel.lift-locals-correct

explicate-correct : ∀ {A} (P : Impμ.Program A) → Equivalent (Impμᵢ.sem P) (CFGμᵢ.sem (explicate P))
explicate-correct = ExplicateFuel.explicate-correct

select-correct : ∀ {A} (P : CFGμ.Program A) → Equivalent (CFGμᵢ.sem P) (X86μᵢ.sem (select P))
select-correct = SelectFuel.select-correct

{- The whole compiler, for closed programs of any type ----------------------}

compile-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Clos5μᵢ.sem (compile M))
compile-correct = CompilerFuel.compile-correct

compile-mon-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Clos5μᵢ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct = CompilerFuel.compile-mon-correct

compile-imp-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Impμᵢ.sem (compile-imp M))
compile-imp-correct = CompilerFuel.compile-imp-correct

compile-cfg-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (CFGμᵢ.sem (compile-cfg M))
compile-cfg-correct = CompilerFuel.compile-cfg-correct

compile-x86-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (X86μᵢ.sem (compile-x86 M))
compile-x86-correct = CompilerFuel.compile-x86-correct

{- The end-to-end theorem, for a main program of type Int: the
   interpreters of ISWIMμ and X86μ stop with the same constant, or both diverge -}

compile-x86-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμᵢ.sem M) (o-const Int k) ⇔ Terminates (X86μᵢ.sem (compile-x86 M)) (o-const Int k)
compile-x86-const = CompilerFuel.compile-x86-const

compile-x86-diverges : ∀ (M : ISWIMμ.Tm [] (base Int))
  → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile-x86 M))
compile-x86-diverges = CompilerFuel.compile-x86-diverges
