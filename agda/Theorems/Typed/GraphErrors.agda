{-

  The correctness of the typed compiler in the graph model with errors:
  the public statements. The proofs are in proof/Correctness/Typed/GraphErr/
  and proof/Adequacy/Typed/GraphErr.agda; each theorem here is one of
  them, with its type written out.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86

  To read them: the typed languages (Language/Typed/), the passes
  (Compiler/Typed/), the semantics of each typed language
  (Semantics/GraphErr/Typed/; Monᵀ means its embedding into Clos5ᵀ, ⌜_⌝ₚ),
  those of ISWIM and X86 (Semantics/GraphErr/), and the domain and
  operators they are built from (Framework/GraphModel/). As in
  Theorems/GraphErrors.agda, an error is the element ω; in the typed
  semantics only project (a cast from Any) checks kinds and errs.

  Select is the one pass that is not an equation (≃), unlike in the
  untyped graph model with errors: X86 checks the kind of every operand,
  so its code has error entries at inputs of the wrong kind, where the
  code of CFGᵀ, which checks nothing, has none. It errs, produces the
  same constants and produces a value exactly when CFGᵀ does (Same).

  Adequacy: for X86, the untyped machine's (Adequacy/GraphErr/X86.agda)
  on the typed compiler's programs, which are well formed; for Clos5ᵀ,
  derived from the ISWIM machine's, Same, and the simulation of the CEK
  column (Theorems/Typed/Simulation.agda).

-}

module Theorems.Typed.GraphErrors where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; _≃_)
open import Framework.GraphModel.Domain using (Value; ω; const)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Theorems.GraphErrors using (ρ₀; Same)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
import Semantics.CEK.X86 as X86ₘ

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

open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Typed.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵀ)
open import Semantics.GraphErr.Typed.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Semantics.GraphErr.Typed.Clos3 using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Semantics.GraphErr.Typed.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧₅)
open import Semantics.GraphErr.Typed.Imp using (⟦_⟧ᵢ)
open import Semantics.GraphErr.Typed.CFG using (⟦_⟧ᶜ)
open import Semantics.GraphErr.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)

import proof.Correctness.Typed.GraphErr.EncloseCorrect as Enclose
import proof.Correctness.Typed.GraphErr.OptimizeCorrect as Optimize
import proof.Correctness.Typed.GraphErr.ConcretizeCorrect as Concretize
import proof.Correctness.Typed.GraphErr.DelayCorrect as Delay
import proof.Correctness.Typed.GraphErr.GlobalizeCorrect as Globalize
import proof.Correctness.Typed.GraphErr.RCOCorrect as RCO
import proof.Correctness.Typed.GraphErr.LiftLocalsCorrect as LiftLocals
import proof.Correctness.Typed.GraphErr.ExplicateCorrect as Explicate
import proof.Correctness.Typed.GraphErr.SelectCorrect as Select
import proof.Correctness.Typed.GraphErr.CompilerCorrect as Compiler
import proof.Adequacy.Typed.GraphErr as Adequacy
open Adequacy using (Agree)

open import Data.List using ([])
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

{- Each pass ------------------------------------------------------------------}

{- every pass but delay and select preserves the meaning of a program
   exactly (≃), errors included; simplify's statement is unchanged
   (Theorems/GraphErrors.agda) -}

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

rco-correct : ∀ (P : Clos5ᵀ.Program) → ⟦ ⌜ rco-program P ⌝ₚ ⟧₅ ≃ ⟦ P ⟧₅
rco-correct = RCO.rco-correct

lift-locals-correct : ∀ (P : Monᵀ.Program) → ⟦ lift-program P ⟧ᵢ ≃ ⟦ ⌜ P ⌝ₚ ⟧₅
lift-locals-correct = LiftLocals.lift-locals-correct

explicate-correct : ∀ (P : Impᵀ.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
explicate-correct = Explicate.explicate-correct

{- select: Same, for every CFGᵀ program -}
select-correct : ∀ (P : CFGᵀ.Program) → Same ⟦ P ⟧ᶜ ⟦ select P ⟧ₓ
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

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-x86 M ⟧ₓ
compile-x86-correct = Select.compile-x86-same

{- Adequacy: the denotation of a closed program tells all three outcomes
   of its machine apart (for ISWIM, unchanged: Theorems/GraphErrors.agda) --}

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

{- the X86 machine, for the programs compile-x86 produces -}
x86-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) o-error
x86-error-iff = Adequacy.x86-error-iff

x86-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff = Adequacy.x86-const-iff

x86-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile-x86 M ⟧ₓ × d ≢ ω) ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
x86-converges-iff = Adequacy.x86-converges-iff

x86-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (X86ₘ.sem (compile-x86 M)) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ compile-x86 M ⟧ₓ))
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
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (X86ₘ.sem (compile-x86 M)) o-error
end-to-end-x86-error M c = Agree.error (Adequacy.end-to-end-x86 M c)

end-to-end-x86-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
end-to-end-x86-const M c = Agree.const (Adequacy.end-to-end-x86 M c)

end-to-end-x86-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
end-to-end-x86-converges M c = Agree.converges (Adequacy.end-to-end-x86 M c)

end-to-end-x86-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (X86ₘ.sem (compile-x86 M))
end-to-end-x86-diverges M c = Agree.diverges (Adequacy.end-to-end-x86 M c)
