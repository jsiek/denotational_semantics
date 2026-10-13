{-

  The correctness of the compiler in the graph model: the public
  statements. The proofs are in proof/Correctness/Graph/;
  each theorem here is one of them, with its type written out, so that it
  can be read without opening proof/.

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  To read them: the languages (Language/), the passes
  (Compiler/), the semantics of each language
  (Semantics/Graph/) and the domain and operators they are built
  from (Framework/GraphModel/).

-}

module Theorems.Denotational where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; nonempty; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; const; ω)

import Language.ISWIM as ISWIM
import Language.Clos2 as Clos2
import Language.Clos3 as Clos3
import Language.Clos4 as Clos4
import Language.Clos5 as Clos5
open import Language.Mon using (MonProgram)
import Language.Imp as Imp
import Language.CFG as CFG
import Language.X86 as X86

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

open import Semantics.Graph.ISWIM using (⟦_⟧)
open import Semantics.Graph.Clos2Iswim using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Semantics.Graph.Clos3Iswim using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Semantics.Graph.Clos4Iswim using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Semantics.Graph.Clos5Iswim using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Semantics.Graph.ImpK using () renaming (⟦_⟧ᴷₚ to ⟦_⟧ᵢ)
open import Semantics.Graph.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Semantics.Graph.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)

import proof.Correctness.Graph.SimplifyCorrect as SimplifyCorrect
import proof.Correctness.Graph.EncloseCorrect as EncloseCorrect
import proof.Correctness.Graph.OptimizeCorrect as OptimizeCorrect
import proof.Correctness.Graph.ConcretizeCorrect as ConcretizeCorrect
import proof.Correctness.Graph.DelayPreserve as DelayCorrect
import proof.Correctness.Graph.GlobalizeCorrect as GlobalizeCorrect
import proof.Correctness.Graph.RCOCorrect as RCOCorrect
import proof.Correctness.Graph.LiftLocalsCorrectK as LiftLocalsCorrect
import proof.Correctness.Graph.ExplicateCorrectK as ExplicateCorrect
import proof.Correctness.Graph.SelectCorrect as SelectCorrect
import proof.Correctness.Graph.CompilerCorrect as CompilerCorrect

open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_)

{- The environment of a closed program: every variable denotes {ω}, the
   default value. (It only matters for open terms, as the passes are
   stated on whole terms.) -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

{- Each pass ------------------------------------------------------------------}

{- every pass but delay preserves the meaning of a program exactly (≃) -}

{- simplify (ISWIM → ISWIM, run before enclose; not yet part of compile) -}
simplify-correct : ∀ (M : ISWIM.AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = SimplifyCorrect.simplify-correct

enclose-correct : ∀ (M : ISWIM.AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct = EncloseCorrect.enclose-correct-closed

optimize-correct : ∀ (M : Clos2.AST) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ optimize-program M ⟧₂ ρ₀
optimize-correct = OptimizeCorrect.optimize-correct-closed

concretize-correct : ∀ (M : Clos2.AST) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = ConcretizeCorrect.concretize-correct-closed

{- delay preserves and reflects the constants a program produces, and
   whether it produces anything -}
delay-correct-const : ∀ (M : Clos3.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ delay M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-const = DelayCorrect.delay-correct-const

delay-correct-nonempty : ∀ (M : Clos3.AST)
  → (nonempty (⟦ M ⟧₃ ρ₀) → nonempty (⟦ delay M ⟧₄ ρ₀))
  × (nonempty (⟦ delay M ⟧₄ ρ₀) → nonempty (⟦ M ⟧₃ ρ₀))
delay-correct-nonempty = DelayCorrect.delay-correct-nonempty

globalize-correct : ∀ (M : Clos4.AST) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ globalize M ⟧₅
globalize-correct = GlobalizeCorrect.globalize-correct

rco-correct : ∀ (P : Clos5.Program) → ⟦ rco-program P ⟧₅ ≃ ⟦ P ⟧₅
rco-correct = RCOCorrect.rco-program-correct

{- lift locals, for programs in monadic normal form (which rco produces) -}
lift-locals-correct : ∀ (P : Clos5.Program) (mp : MonProgram P) → ⟦ lift-program P mp ⟧ᵢ ≃ ⟦ P ⟧₅
lift-locals-correct = LiftLocalsCorrect.lift-program-correct

explicate-correct : ∀ (P : Imp.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
explicate-correct = ExplicateCorrect.explicate-correct

{- select instructions, when each global definition has at least 2 slots,
   for its parameters (the programs that the compiler produces do) -}
select-correct : ∀ (P : CFG.Program) → All (λ b → 2 ≤ CFG.Body.locals b) (CFG.Program.defs P)
  → ⟦ select P ⟧ₓ ≃ ⟦ P ⟧ᶜ
select-correct = SelectCorrect.select-correct

{- The whole compiler --------------------------------------------------------}

{- the compiled program produces the same constants as the original, and
   produces something exactly when the original does: into Clos5 (compile),
   into monadic normal form (compile-mon), Imp (compile-imp), CFG
   (compile-cfg) and X86 (compile-x86) -}

compile-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧₅)
  × (const c ∈ ⟦ compile M ⟧₅ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const = CompilerCorrect.compile-correct-const

compile-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧₅)
  × (nonempty ⟦ compile M ⟧₅ → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty = CompilerCorrect.compile-correct-nonempty

compile-mon-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-mon M ⟧₅)
  × (const c ∈ ⟦ compile-mon M ⟧₅ → const c ∈ ⟦ M ⟧ ρ₀)
compile-mon-correct-const = RCOCorrect.compile-mon-correct-const

compile-mon-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-mon M ⟧₅)
  × (nonempty ⟦ compile-mon M ⟧₅ → nonempty (⟦ M ⟧ ρ₀))
compile-mon-correct-nonempty = RCOCorrect.compile-mon-correct-nonempty

compile-imp-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-imp M ⟧ᵢ)
  × (const c ∈ ⟦ compile-imp M ⟧ᵢ → const c ∈ ⟦ M ⟧ ρ₀)
compile-imp-correct-const = LiftLocalsCorrect.compile-imp-correct-const

compile-imp-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-imp M ⟧ᵢ)
  × (nonempty ⟦ compile-imp M ⟧ᵢ → nonempty (⟦ M ⟧ ρ₀))
compile-imp-correct-nonempty = LiftLocalsCorrect.compile-imp-correct-nonempty

compile-cfg-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-cfg M ⟧ᶜ)
  × (const c ∈ ⟦ compile-cfg M ⟧ᶜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-cfg-correct-const = ExplicateCorrect.compile-cfg-correct-const

compile-cfg-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-cfg M ⟧ᶜ)
  × (nonempty ⟦ compile-cfg M ⟧ᶜ → nonempty (⟦ M ⟧ ρ₀))
compile-cfg-correct-nonempty = ExplicateCorrect.compile-cfg-correct-nonempty

compile-x86-correct-const : ∀ (M : ISWIM.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-x86 M ⟧ₓ)
  × (const c ∈ ⟦ compile-x86 M ⟧ₓ → const c ∈ ⟦ M ⟧ ρ₀)
compile-x86-correct-const = SelectCorrect.compile-x86-correct-const

compile-x86-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-x86 M ⟧ₓ)
  × (nonempty ⟦ compile-x86 M ⟧ₓ → nonempty (⟦ M ⟧ ρ₀))
compile-x86-correct-nonempty = SelectCorrect.compile-x86-correct-nonempty
