{-

  The correctness of the compiler in the graph model with errors: the
  public statements. The proofs are in proof/Semantics/GraphErr/,
  proof/Correctness/GraphErr/ and proof/Adequacy/GraphErr/; each theorem
  here is one of them, with its type written out, so that it can be read
  without opening proof/.

    ISWIM --simplify--> ISWIM --capture--> Clos2 --prune--> Clos2 --concretize--> Clos3
          --split--> Clos4 --hoist--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  The graph model with errors (Semantics/GraphErr/) is the graph model
  in which a program that stops with an error denotes a set that holds
  the error value ω (Framework/GraphModel/Domain.agda), while one that
  diverges denotes the empty set; its operators are the graph model's,
  under an error monad that propagates ω in the machines' evaluation
  order (Framework/GraphModel/ErrorMonad.agda), and
  the semantics of Clos5, Imp, CFG and X86 err where their machines do
  (a call of a missing definition, a frame slot out of range, an unset
  register, a value of the wrong kind).

  So, unlike in the graph model (Theorems/Denotational.agda and
  Theorems/Adequacy.agda), the denotation of a closed program tells all
  three outcomes of its machine apart, and the compiler is correct for
  each: the ISWIM machine on M and the Clos5 and X86 machines on the
  compiled program stop with an error together, stop with the same
  constants, stop with an answer together, and diverge together.

  To read them: the languages (Language/), the passes (Compiler/), the
  semantics (Semantics/GraphErr/) and the domain and operators they are
  built from (Framework/GraphModel/{Domain,OpsBase,Ops,ErrorMonad}.agda); and,
  for adequacy, the machines (Semantics/CEK/{ISWIM,Clos5,X86}.agda) and
  the observations (Semantics/Observation.agda).

-}

module Untyped.Theorems.GraphErrors where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; ω; const)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.ISWIM as ISWIMₘ
import Untyped.Semantics.CEK.Clos5 as Clos5ₘ
import Semantics.CEK.X86 as X86ₘ

import Language.ISWIM as ISWIM
import Untyped.Language.Clos2 as Clos2
import Untyped.Language.Clos3 as Clos3
import Untyped.Language.Clos4 as Clos4
import Untyped.Language.Clos5 as Clos5
open import Untyped.Language.Mon using (MonProgram)
import Untyped.Language.Imp as Imp
import Untyped.Language.CFG as CFG
open import Framework.Syntax.Scope Clos2.Op Clos2.sig using (WS)
open import Compiler.Simplify using (simplify)
open import Untyped.Compiler.Capture using (capture)
open import Untyped.Compiler.Prune using (prune-program)
open import Untyped.Compiler.Concretize using (concretize-program)
open import Untyped.Compiler.Split using (split)
open import Untyped.Compiler.Hoist using (hoist)
open import Untyped.Compiler.RCO using (rco-program)
open import Untyped.Compiler.LiftLocals using (lift-program)
open import Untyped.Compiler.Explicate using (explicate)
open import Untyped.Compiler.Select using (select)
open import Untyped.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Untyped.Compiler.PipelineScope using (Scoped)
open import Compiler.CaptureScope using (Closed)
open import Framework.GraphModel.ErrorMonad using (val∈)

open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Untyped.Semantics.GraphErr.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Untyped.Semantics.GraphErr.Clos3 using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Untyped.Semantics.GraphErr.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Untyped.Semantics.GraphErr.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Untyped.Semantics.GraphErr.ImpK using () renaming (⟦_⟧ᴷₚ to ⟦_⟧ᵢ)
open import Untyped.Semantics.GraphErr.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Untyped.Semantics.GraphErr.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)

import proof.Correctness.GraphErr.SimplifyCorrect as SimplifyCorrect
import Untyped.proof.Correctness.GraphErr.CaptureCorrect as CaptureCorrect
import Untyped.proof.Correctness.GraphErr.PruneCorrect as PruneCorrect
import Untyped.proof.Correctness.GraphErr.ConcretizeCorrect as ConcretizeCorrect
import Untyped.proof.Correctness.GraphErr.SplitPreserve as SplitCorrect
import Untyped.proof.Correctness.GraphErr.HoistCorrect as HoistCorrect
import Untyped.proof.Correctness.GraphErr.RCOCorrect as RCOCorrect
import Untyped.proof.Correctness.GraphErr.LiftLocalsCorrect as LiftLocalsCorrect
import Untyped.proof.Correctness.GraphErr.ExplicateCorrect as ExplicateCorrect
import Untyped.proof.Correctness.GraphErr.SelectCorrect as SelectCorrect
import Untyped.proof.Correctness.GraphErr.CompilerCorrect as CompilerCorrect
import proof.Adequacy.GraphErr.ISWIM as Adequacy
import proof.Adequacy.GraphErr.Simplify as SimplifyMachine
import Untyped.proof.Adequacy.GraphErr.Clos5 as AdequacyClos5
import Untyped.proof.Adequacy.GraphErr.X86CompileWF as AdequacyX86
import Untyped.proof.Adequacy.GraphErr.EndToEnd as EndToEnd

open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

{- The environment of a closed program: every variable denotes {ω}, an
   error, as a free variable is in the machines -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

{- Each pass ------------------------------------------------------------------}

{- every pass but split preserves the meaning of a program exactly (≃),
   errors included -}

simplify-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = SimplifyCorrect.simplify-correct

capture-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ capture M ⟧₂ ρ₀
capture-correct = CaptureCorrect.capture-correct

{- prune, for well-scoped programs (capture produces them) -}
prune-correct : ∀ (M : Clos2.AST) → WS 0 M → ⟦ M ⟧₂ ρ₀ ≃ ⟦ prune-program M ⟧₂ ρ₀
prune-correct = PruneCorrect.prune-correct

concretize-correct : ∀ (M : Clos2.AST) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = ConcretizeCorrect.concretize-correct-closed

{- split changes how closures are represented, so it is not an equation:
   it preserves and reflects an error, the constants a program produces,
   and whether it produces a value (an element other than ω) -}
split-correct-error : ∀ (M : Clos3.AST)
  → (ω ∈ ⟦ M ⟧₃ ρ₀ → ω ∈ ⟦ split M ⟧₄ ρ₀) × (ω ∈ ⟦ split M ⟧₄ ρ₀ → ω ∈ ⟦ M ⟧₃ ρ₀)
split-correct-error = SplitCorrect.split-correct-error

split-correct-const : ∀ (M : Clos3.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ split M ⟧₄ ρ₀)
  × (const c ∈ ⟦ split M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧₃ ρ₀)
split-correct-const = SplitCorrect.split-correct-const

split-correct-val : ∀ (M : Clos3.AST)
  → (val∈ (⟦ M ⟧₃ ρ₀) → val∈ (⟦ split M ⟧₄ ρ₀)) × (val∈ (⟦ split M ⟧₄ ρ₀) → val∈ (⟦ M ⟧₃ ρ₀))
split-correct-val = SplitCorrect.split-correct-val

hoist-correct : ∀ (M : Clos4.AST) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ hoist M ⟧₅
hoist-correct = HoistCorrect.hoist-correct

{- rco, for well-scoped programs (hoist produces them) -}
rco-correct : ∀ (P : Clos5.Program) → Scoped P → ⟦ rco-program P ⟧₅ ≃ ⟦ P ⟧₅
rco-correct = RCOCorrect.rco-correct

{- lift locals, for programs in monadic normal form (which rco produces) -}
lift-locals-correct : ∀ (P : Clos5.Program) (mp : MonProgram P) → ⟦ lift-program P mp ⟧ᵢ ≃ ⟦ P ⟧₅
lift-locals-correct = LiftLocalsCorrect.lift-locals-correct

explicate-correct : ∀ (P : Imp.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
explicate-correct = ExplicateCorrect.explicate-correct

select-correct : ∀ (P : CFG.Program) → ⟦ select P ⟧ₓ ≃ ⟦ P ⟧ᶜ
select-correct = SelectCorrect.select-correct

{- The whole compiler ---------------------------------------------------------}

{- two meanings err together, hold the same constants, and hold a value
   together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = ((ω ∈ D) ⇔ (ω ∈ E)) × (∀ {B} (c : base-rep B) → ((const c ∈ D) ⇔ (const c ∈ E))) × (val∈ D ⇔ val∈ E)

compile-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧₅
compile-correct = CompilerCorrect.compile-same

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-mon M ⟧₅
compile-mon-correct = CompilerCorrect.compile-mon-same

compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-imp M ⟧ᵢ
compile-imp-correct = CompilerCorrect.compile-imp-same

compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-cfg M ⟧ᶜ
compile-cfg-correct = CompilerCorrect.compile-cfg-same

compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-x86 M ⟧ₓ
compile-x86-correct = CompilerCorrect.compile-x86-same

{- Adequacy: the denotation of a closed program tells all three outcomes
   of its machine apart -------------------------------------------------------}

{- the ISWIM machine -}
iswim-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) o-error
iswim-error-iff = Adequacy.error-iff

iswim-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) (o-const B k)
iswim-const-iff = Adequacy.const-iff

iswim-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω) ⇔ Converges (Terminates (ISWIMₘ.sem M))
iswim-converges-iff = Adequacy.converges-iff

iswim-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ M ⟧ ρ₀))
iswim-diverges-iff = Adequacy.diverges-iff

{- the Clos5 machine, for the programs compile produces -}
clos5-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ₘ.sem (compile M)) o-error
clos5-error-iff = AdequacyClos5.clos5-error-iff

clos5-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ₘ.sem (compile M)) (o-const B k)
clos5-const-iff = AdequacyClos5.clos5-const-iff

clos5-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile M ⟧₅ × d ≢ ω) ⇔ Converges (Terminates (Clos5ₘ.sem (compile M)))
clos5-converges-iff = AdequacyClos5.clos5-converges-iff

clos5-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (Clos5ₘ.sem (compile M)) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ compile M ⟧₅))
clos5-diverges-iff = AdequacyClos5.clos5-diverges-iff

{- the X86 machine, for the programs compile-x86 produces -}
x86-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) o-error
x86-error-iff = AdequacyX86.x86-error-iff

x86-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff = AdequacyX86.x86-const-iff

x86-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile-x86 M ⟧ₓ × d ≢ ω) ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
x86-converges-iff = AdequacyX86.x86-converges-iff

x86-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (X86ₘ.sem (compile-x86 M)) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ compile-x86 M ⟧ₓ))
x86-diverges-iff = AdequacyX86.x86-diverges-iff

{- The compiler, observed through the machines: for a closed program, the
   ISWIM machine and the machine of the compiled program stop with an
   error together, stop with the same constants, stop with an answer
   together and diverge together ---------------------------------------------}

end-to-end-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (Clos5ₘ.sem (compile M)) o-error
end-to-end-error M c = EndToEnd.Agree.error (EndToEnd.end-to-end M c)

end-to-end-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (Clos5ₘ.sem (compile M)) (o-const B k)
end-to-end-const M c = EndToEnd.Agree.const (EndToEnd.end-to-end M c)

end-to-end-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (Clos5ₘ.sem (compile M)))
end-to-end-converges M c = EndToEnd.Agree.converges (EndToEnd.end-to-end M c)

end-to-end-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (Clos5ₘ.sem (compile M))
end-to-end-diverges M c = EndToEnd.Agree.diverges (EndToEnd.end-to-end M c)

end-to-end-x86-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (X86ₘ.sem (compile-x86 M)) o-error
end-to-end-x86-error M c = EndToEnd.Agree.error (EndToEnd.end-to-end-x86 M c)

end-to-end-x86-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
end-to-end-x86-const M c = EndToEnd.Agree.const (EndToEnd.end-to-end-x86 M c)

end-to-end-x86-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
end-to-end-x86-converges M c = EndToEnd.Agree.converges (EndToEnd.end-to-end-x86 M c)

end-to-end-x86-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (X86ₘ.sem (compile-x86 M))
end-to-end-x86-diverges M c = EndToEnd.Agree.diverges (EndToEnd.end-to-end-x86 M c)

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
