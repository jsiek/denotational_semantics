{-

  The correctness of the compiler in the graph model: the public
  statements. The proofs are in proof/Correctness/Graph/;
  each theorem here is one of them, with its type written out, so that it
  can be read without opening proof/.

    ISWIM --simplify--> ISWIM --capture--> Clos2 --prune--> Clos2 --concretize--> Clos3
          --split--> Clos4 --hoist--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  To read them: the languages (Language/), the passes
  (Compiler/), the semantics of each language
  (Semantics/Graph/) and the domain and operators they are built
  from (Framework/GraphModel/).

-}

module ISWIM.Untyped.Theorems.Denotational where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; nonempty; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; const; ω)

import ISWIM.Language.ISWIM as ISWIM
import ISWIM.Untyped.Language.Clos2 as Clos2
import ISWIM.Untyped.Language.Clos3 as Clos3
import ISWIM.Untyped.Language.Clos4 as Clos4
import ISWIM.Untyped.Language.Clos5 as Clos5
open import ISWIM.Untyped.Language.Mon using (MonProgram)
import ISWIM.Untyped.Language.Imp as Imp
import ISWIM.Untyped.Language.CFG as CFG
import ISWIM.Language.X86 as X86

open import ISWIM.Compiler.Simplify using (simplify)
open import ISWIM.Untyped.Compiler.Capture using (capture)
open import ISWIM.Untyped.Compiler.Prune using (prune-program)
open import ISWIM.Untyped.Compiler.Concretize using (concretize-program)
open import ISWIM.Untyped.Compiler.Split using (split)
open import ISWIM.Untyped.Compiler.Hoist using (hoist)
open import ISWIM.Untyped.Compiler.RCO using (rco-program)
open import ISWIM.Untyped.Compiler.LiftLocals using (lift-program)
open import ISWIM.Untyped.Compiler.Explicate using (explicate)
open import ISWIM.Untyped.Compiler.Select using (select)
open import ISWIM.Untyped.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import ISWIM.Semantics.Graph.ISWIM using (⟦_⟧)
open import ISWIM.Untyped.Semantics.Graph.Clos2Iswim using () renaming (⟦_⟧ to ⟦_⟧₂)
open import ISWIM.Untyped.Semantics.Graph.Clos3Iswim using () renaming (⟦_⟧ to ⟦_⟧₃)
open import ISWIM.Untyped.Semantics.Graph.Clos4Iswim using () renaming (⟦_⟧ to ⟦_⟧₄)
open import ISWIM.Untyped.Semantics.Graph.Clos5Iswim using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import ISWIM.Untyped.Semantics.Graph.ImpK using () renaming (⟦_⟧ᴷₚ to ⟦_⟧ᵢ)
open import ISWIM.Untyped.Semantics.Graph.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import ISWIM.Untyped.Semantics.Graph.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)

import ISWIM.proof.Correctness.Graph.SimplifyCorrect as SimplifyCorrect
import ISWIM.Untyped.proof.Correctness.Graph.CaptureCorrect as CaptureCorrect
import ISWIM.Untyped.proof.Correctness.Graph.PruneCorrect as PruneCorrect
import ISWIM.Untyped.proof.Correctness.Graph.ConcretizeCorrect as ConcretizeCorrect
import ISWIM.Untyped.proof.Correctness.Graph.SplitPreserve as SplitCorrect
import ISWIM.Untyped.proof.Correctness.Graph.HoistCorrect as HoistCorrect
import ISWIM.Untyped.proof.Correctness.Graph.RCOCorrect as RCOCorrect
import ISWIM.Untyped.proof.Correctness.Graph.LiftLocalsCorrectK as LiftLocalsCorrect
import ISWIM.Untyped.proof.Correctness.Graph.ExplicateCorrectK as ExplicateCorrect
import ISWIM.Untyped.proof.Correctness.Graph.SelectCorrect as SelectCorrect
import ISWIM.Untyped.proof.Correctness.Graph.CompilerCorrect as CompilerCorrect

open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_)

{- The environment of a closed program: every variable denotes {ω}, the
   default value. (It only matters for open terms, as the passes are
   stated on whole terms.) -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

{- Each pass ------------------------------------------------------------------}

{- every pass but split preserves the meaning of a program exactly (≃) -}

{- simplify (ISWIM → ISWIM, the first pass) -}
simplify-correct : ∀ (M : ISWIM.AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = SimplifyCorrect.simplify-correct

capture-correct : ∀ (M : ISWIM.AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ capture M ⟧₂ ρ₀
capture-correct = CaptureCorrect.capture-correct-closed

prune-correct : ∀ (M : Clos2.AST) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ prune-program M ⟧₂ ρ₀
prune-correct = PruneCorrect.prune-correct-closed

concretize-correct : ∀ (M : Clos2.AST) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = ConcretizeCorrect.concretize-correct-closed

{- split preserves and reflects the constants a program produces, and
   whether it produces anything -}
split-correct-const : ∀ (M : Clos3.AST) {B} (c : base-rep B)
  → (  const c ∈ ⟦ M ⟧₃ ρ₀
     → const c ∈ ⟦ split M ⟧₄ ρ₀)
  × (  const c ∈ ⟦ split M ⟧₄ ρ₀
     → const c ∈ ⟦ M ⟧₃ ρ₀)
split-correct-const = SplitCorrect.split-correct-const

split-correct-nonempty : ∀ (M : Clos3.AST)
  → (  nonempty (⟦ M ⟧₃ ρ₀)
     → nonempty (⟦ split M ⟧₄ ρ₀))
  × (  nonempty (⟦ split M ⟧₄ ρ₀)
     → nonempty (⟦ M ⟧₃ ρ₀))
split-correct-nonempty = SplitCorrect.split-correct-nonempty

hoist-correct : ∀ (M : Clos4.AST) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ hoist M ⟧₅
hoist-correct = HoistCorrect.hoist-correct

rco-correct : ∀ (P : Clos5.Program) → ⟦ rco-program P ⟧₅ ≃ ⟦ P ⟧₅
rco-correct = RCOCorrect.rco-program-correct

{- lift locals, for programs in monadic normal form (which rco produces) -}
lift-locals-correct : ∀ (P : Clos5.Program)
  → (mp : MonProgram P)
  → ⟦ lift-program P mp ⟧ᵢ ≃ ⟦ P ⟧₅
lift-locals-correct = LiftLocalsCorrect.lift-program-correct

explicate-correct : ∀ (P : Imp.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
explicate-correct = ExplicateCorrect.explicate-correct

{- select instructions, when each global definition has at least 2 slots,
   for its parameters (the programs that the compiler produces do) -}
select-correct : ∀ (P : CFG.Program)
  → All (λ b → 2 ≤ CFG.Body.locals b) (CFG.Program.defs P)
  → ⟦ select P ⟧ₓ ≃ ⟦ P ⟧ᶜ
select-correct = SelectCorrect.select-correct

{- The whole compiler --------------------------------------------------------}

{- the compiled program produces the same constants as the original, and
   produces something exactly when the original does: into Clos5 (compile),
   into monadic normal form (compile-mon), Imp (compile-imp), CFG
   (compile-cfg) and X86 (compile-x86) -}

compile-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (  const c ∈ ⟦ M ⟧ ρ₀
     → const c ∈ ⟦ compile M ⟧₅)
  × (  const c ∈ ⟦ compile M ⟧₅
     → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const = CompilerCorrect.compile-correct-const

compile-correct-nonempty : ∀ (M : ISWIM.AST)
  → (  nonempty (⟦ M ⟧ ρ₀)
     → nonempty ⟦ compile M ⟧₅)
  × (  nonempty ⟦ compile M ⟧₅
     → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty = CompilerCorrect.compile-correct-nonempty

compile-mon-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (  const c ∈ ⟦ M ⟧ ρ₀
     → const c ∈ ⟦ compile-mon M ⟧₅)
  × (  const c ∈ ⟦ compile-mon M ⟧₅
     → const c ∈ ⟦ M ⟧ ρ₀)
compile-mon-correct-const = RCOCorrect.compile-mon-correct-const

compile-mon-correct-nonempty : ∀ (M : ISWIM.AST)
  → (  nonempty (⟦ M ⟧ ρ₀)
     → nonempty ⟦ compile-mon M ⟧₅)
  × (  nonempty ⟦ compile-mon M ⟧₅
     → nonempty (⟦ M ⟧ ρ₀))
compile-mon-correct-nonempty = RCOCorrect.compile-mon-correct-nonempty

compile-imp-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (  const c ∈ ⟦ M ⟧ ρ₀
     → const c ∈ ⟦ compile-imp M ⟧ᵢ)
  × (  const c ∈ ⟦ compile-imp M ⟧ᵢ
     → const c ∈ ⟦ M ⟧ ρ₀)
compile-imp-correct-const = LiftLocalsCorrect.compile-imp-correct-const

compile-imp-correct-nonempty : ∀ (M : ISWIM.AST)
  → (  nonempty (⟦ M ⟧ ρ₀)
     → nonempty ⟦ compile-imp M ⟧ᵢ)
  × (  nonempty ⟦ compile-imp M ⟧ᵢ
     → nonempty (⟦ M ⟧ ρ₀))
compile-imp-correct-nonempty = LiftLocalsCorrect.compile-imp-correct-nonempty

compile-cfg-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (  const c ∈ ⟦ M ⟧ ρ₀
     → const c ∈ ⟦ compile-cfg M ⟧ᶜ)
  × (  const c ∈ ⟦ compile-cfg M ⟧ᶜ
     → const c ∈ ⟦ M ⟧ ρ₀)
compile-cfg-correct-const = ExplicateCorrect.compile-cfg-correct-const

compile-cfg-correct-nonempty : ∀ (M : ISWIM.AST)
  → (  nonempty (⟦ M ⟧ ρ₀)
     → nonempty ⟦ compile-cfg M ⟧ᶜ)
  × (  nonempty ⟦ compile-cfg M ⟧ᶜ
     → nonempty (⟦ M ⟧ ρ₀))
compile-cfg-correct-nonempty = ExplicateCorrect.compile-cfg-correct-nonempty

compile-x86-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (  const c ∈ ⟦ M ⟧ ρ₀
     → const c ∈ ⟦ compile-x86 M ⟧ₓ)
  × (  const c ∈ ⟦ compile-x86 M ⟧ₓ
     → const c ∈ ⟦ M ⟧ ρ₀)
compile-x86-correct-const = SelectCorrect.compile-x86-correct-const

compile-x86-correct-nonempty : ∀ (M : ISWIM.AST)
  → (  nonempty (⟦ M ⟧ ρ₀)
     → nonempty ⟦ compile-x86 M ⟧ₓ)
  × (  nonempty ⟦ compile-x86 M ⟧ₓ
     → nonempty (⟦ M ⟧ ρ₀))
compile-x86-correct-nonempty = SelectCorrect.compile-x86-correct-nonempty
