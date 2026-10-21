{-

  The correctness of the compiler in the graph model with errors:
  the public statements. The proofs are in proof/Correctness/GraphErr/
  and proof/Adequacy/GraphErr/EndToEnd.agda; each theorem here is one of
  them, with its type written out.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

  To read them: the typed languages (Language/Typed/), the passes
  (Compiler/), the semantics of each typed language
  (Semantics/GraphErr/Typed/, X86ᵀ included; Monᵀ means its embedding
  into Clos5ᵀ, ⌜_⌝ₚ), that of ISWIM (Semantics/GraphErr/), the machines
  of ISWIM, Clos5ᵀ and X86ᵀ (Semantics/CEK/), and the domain and
  operators they are built from (Framework/GraphModel/). An error is the
  element ω; in the typed semantics only project (a cast from Any)
  checks kinds and errs.

  Every pass but delay is an equation (≃), select instructions
  included: X86ᵀ, like CFGᵀ, checks kinds only at project (chk).

  Adequacy: for X86ᵀ, direct, that of its semantics for its machine
  (Adequacy/GraphErr/X86.agda), on the programs of the compiler, whose
  definitions' code depends only on the older ones and whose table is
  consistent; for Clos5ᵀ, derived from the ISWIM machine's, Same, and
  the simulation of the CEK column (Theorems/Simulation.agda).

-}

module Theorems.GraphErrors where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; ω; const)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
import Semantics.CEK.Typed.X86 as X86ᵀₘ

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
open import Compiler.EncloseScope using (Closed)

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

open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Typed.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵀ)
open import Semantics.GraphErr.Typed.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Semantics.GraphErr.Typed.Clos3 using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Semantics.GraphErr.Typed.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧₅)
open import Semantics.GraphErr.Typed.Imp using (⟦_⟧ᵢ)
open import Semantics.GraphErr.Typed.CFG using (⟦_⟧ᶜ)
open import Semantics.GraphErr.Typed.X86 using (⟦_⟧ₜ)

import proof.Correctness.GraphErr.SimplifyCorrect as SimplifyCorrect
import proof.Correctness.GraphErr.EncloseCorrect as Enclose
import proof.Correctness.GraphErr.OptimizeCorrect as Optimize
import proof.Correctness.GraphErr.ConcretizeCorrect as Concretize
import proof.Correctness.GraphErr.DelayCorrect as Delay
import proof.Correctness.GraphErr.GlobalizeCorrect as Globalize
import proof.Correctness.GraphErr.RCOCorrect as RCO
import proof.Correctness.GraphErr.LiftLocalsCorrect as LiftLocals
import proof.Correctness.GraphErr.ExplicateCorrect as Explicate
import proof.Correctness.GraphErr.SelectCorrect as Select
import proof.Correctness.GraphErr.CompilerCorrect as Compiler
import proof.Adequacy.GraphErr.EndToEnd as Adequacy
import proof.Adequacy.GraphErr.ISWIM as AdequacyISWIM
import proof.Adequacy.GraphErr.Simplify as SimplifyMachine
open Adequacy using (Agree)

open import Data.List using ([])
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

{- The environment of a closed program: every variable denotes {ω}, an
   error, as a free variable is in the machines -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

{- Each pass ------------------------------------------------------------------}

{- every pass but delay preserves the meaning of a program exactly (≃),
   errors included -}

simplify-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = SimplifyCorrect.simplify-correct

cast-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ cast-closed M ⟧ᵀ ρ₀
cast-correct = Compiler.cast-correct-closed

enclose-correct : ∀ (M : ISWIMᵀ.Tm 0 Any) → ⟦ M ⟧ᵀ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct = Enclose.enclose-correct

optimize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ optimize-program M ⟧₂ ρ₀
optimize-correct = Optimize.optimize-correct

concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = Concretize.concretize-correct

{- delay preserves and reflects an error, the constants a program
   produces, and whether it produces a value -}
delay-correct-error : ∀ (M : Clos3ᵀ.Tm [] Any)
  → (ω ∈ ⟦ M ⟧₃ ρ₀ → ω ∈ ⟦ delay-program M ⟧₄ ρ₀) × (ω ∈ ⟦ delay-program M ⟧₄ ρ₀ → ω ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-error = Delay.delay-correct-error

delay-correct-const : ∀ (M : Clos3ᵀ.Tm [] Any) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-const = Delay.delay-correct-const

delay-correct-val : ∀ (M : Clos3ᵀ.Tm [] Any)
  → (val∈ (⟦ M ⟧₃ ρ₀) → val∈ (⟦ delay-program M ⟧₄ ρ₀)) × (val∈ (⟦ delay-program M ⟧₄ ρ₀) → val∈ (⟦ M ⟧₃ ρ₀))
delay-correct-val = Delay.delay-correct-val

globalize-correct : ∀ (M : Clos4ᵀ.Tm [] Any) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ globalize M ⟧₅
globalize-correct = Globalize.globalize-correct

rco-correct : ∀ (P : Clos5ᵀ.Program) → ⟦ P ⟧₅ ≃ ⟦ ⌜ rco-program P ⌝ₚ ⟧₅
rco-correct = RCO.rco-correct

lift-locals-correct : ∀ (P : Monᵀ.Program) → ⟦ ⌜ P ⌝ₚ ⟧₅ ≃ ⟦ lift-program P ⟧ᵢ
lift-locals-correct = LiftLocals.lift-locals-correct

explicate-correct : ∀ (P : Impᵀ.Program) → ⟦ P ⟧ᵢ ≃ ⟦ explicate P ⟧ᶜ
explicate-correct = Explicate.explicate-correct

{- two meanings err together, hold the same constants, and hold a value
   together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = ((ω ∈ D) ⇔ (ω ∈ E)) × (∀ {B} (c : base-rep B) → ((const c ∈ D) ⇔ (const c ∈ E))) × (val∈ D ⇔ val∈ E)

{- for every CFGᵀ program -}
select-correct : ∀ (P : CFGᵀ.Program) → ⟦ P ⟧ᶜ ≃ ⟦ select P ⟧ₜ
select-correct = Select.select-correct

{- The whole compiler, for closed programs -------------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧₅
compile-correct = Compiler.compile-same₅

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅
compile-mon-correct = Compiler.compile-mon-same

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-imp M ⟧ᵢ
compile-imp-correct = Compiler.compile-imp-same

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-cfg M ⟧ᶜ
compile-cfg-correct = Compiler.compile-cfg-same

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-x86 M ⟧ₜ
compile-x86-correct = Compiler.compile-x86-same

{- Adequacy: the denotation of a closed program tells all three outcomes
   of its machine apart -------------------------------------------------------}

{- the ISWIM machine -}
iswim-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) o-error
iswim-error-iff = AdequacyISWIM.error-iff

iswim-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) (o-const B k)
iswim-const-iff = AdequacyISWIM.const-iff

iswim-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω) ⇔ Converges (Terminates (ISWIMₘ.sem M))
iswim-converges-iff = AdequacyISWIM.converges-iff

iswim-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ M ⟧ ρ₀))
iswim-diverges-iff = AdequacyISWIM.diverges-iff

{- the Clos5ᵀ machine, for the programs compile produces -}
clos5-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) o-error
clos5-error-iff = Adequacy.clos5-error-iff

clos5-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
clos5-const-iff = Adequacy.clos5-const-iff

clos5-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile M ⟧₅ × d ≢ ω) ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
clos5-converges-iff = Adequacy.clos5-converges-iff

clos5-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (Clos5ᵀₘ.sem (compile M)) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ compile M ⟧₅))
clos5-diverges-iff = Adequacy.clos5-diverges-iff

{- the X86ᵀ machine, for the programs compile-x86 produces -}
x86-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) o-error
x86-error-iff = Adequacy.x86-error-iff

x86-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff = Adequacy.x86-const-iff

x86-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile-x86 M ⟧ₜ × d ≢ ω) ⇔ Converges (Terminates (X86ᵀₘ.sem (compile-x86 M)))
x86-converges-iff = Adequacy.x86-converges-iff

x86-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (X86ᵀₘ.sem (compile-x86 M)) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ compile-x86 M ⟧ₜ))
x86-diverges-iff = Adequacy.x86-diverges-iff

{- The compiler, observed through the machines ---------------------------------}

end-to-end-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) o-error
end-to-end-error M c = Agree.error (Adequacy.end-to-end M c)

end-to-end-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
end-to-end-const M c = Agree.const (Adequacy.end-to-end M c)

end-to-end-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
end-to-end-converges M c = Agree.converges (Adequacy.end-to-end M c)

end-to-end-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (Clos5ᵀₘ.sem (compile M))
end-to-end-diverges M c = Agree.diverges (Adequacy.end-to-end M c)

end-to-end-x86-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) o-error
end-to-end-x86-error M c = Agree.error (Adequacy.end-to-end-x86 M c)

end-to-end-x86-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) (o-const B k)
end-to-end-x86-const M c = Agree.const (Adequacy.end-to-end-x86 M c)

end-to-end-x86-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (X86ᵀₘ.sem (compile-x86 M)))
end-to-end-x86-converges M c = Agree.converges (Adequacy.end-to-end-x86 M c)

end-to-end-x86-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (X86ᵀₘ.sem (compile-x86 M))
end-to-end-x86-diverges M c = Agree.diverges (Adequacy.end-to-end-x86 M c)

{- simplify, observed through the ISWIM machine -}
simplify-machine-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (ISWIMₘ.sem (simplify M)) o-error
simplify-machine-error = SimplifyMachine.simplify-error

simplify-machine-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (ISWIMₘ.sem (simplify M)) (o-const B k)
simplify-machine-const = SimplifyMachine.simplify-const

simplify-machine-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (ISWIMₘ.sem (simplify M)))
simplify-machine-converges = SimplifyMachine.simplify-converges

simplify-machine-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (ISWIMₘ.sem (simplify M))
simplify-machine-diverges = SimplifyMachine.simplify-diverges
