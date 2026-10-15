{-

  The correctness of the ISWIMμ compiler (Mu/Compiler/Pipeline.agda) in
  the graph model: the public statements. The proofs are in
  Mu/proof/Correctness/Graph/; each theorem here is one of them, with
  its type written out.

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ
           --concretize--> Clos3μ --delay--> Clos4μ --globalize--> Clos5μ
           --rco--> Monμ --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  To read them: the languages (Mu/Language/), the passes
  (Mu/Compiler/), the semantics of each language, X86μ included
  (Mu/Semantics/Graph/; Monμ means its embedding into Clos5μ, ⌜_⌝ₚ), and
  the domain and operators they are built from (Framework/GraphModel/).
  A program is a closed term of any type; the end-to-end theorem is
  stated for a main program of type Int, as in the other styles (whose
  statement, on the machines, is that of Mu/Theorems/Adequacy.agda).

-}

module Mu.Theorems.Denotational where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (⌈_⌉; _∈_; nonempty; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; const; ω)

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

open import Mu.Semantics.Graph.ISWIM using (⟦_⟧)
open import Mu.Semantics.Graph.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Mu.Semantics.Graph.Clos3 using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Mu.Semantics.Graph.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.Semantics.Graph.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Mu.Semantics.Graph.Imp using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.Semantics.Graph.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.Semantics.Graph.X86 using (⟦_⟧ₜ)

import Mu.proof.Correctness.Graph.SimplifyCorrect as Simplify
import Mu.proof.Correctness.Graph.EncloseCorrect as Enclose
import Mu.proof.Correctness.Graph.OptimizeCorrect as Optimize
import Mu.proof.Correctness.Graph.ConcretizeCorrect as Concretize
import Mu.proof.Correctness.Graph.DelayCorrect as Delay
import Mu.proof.Correctness.Graph.GlobalizeCorrect as Globalize
import Mu.proof.Correctness.Graph.RCOCorrect as RCO
import Mu.proof.Correctness.Graph.LiftLocalsCorrect as LiftLocals
import Mu.proof.Correctness.Graph.ExplicateCorrect as Explicate
import Mu.proof.Correctness.Graph.SelectCorrect as Select
import Mu.proof.Correctness.Graph.CompilerCorrect as Compiler

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂)

{- The environment of a closed program: every variable denotes {ω}, the
   default value. (It only matters for open terms, as the passes are
   stated on whole terms.) -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

{- Each pass ------------------------------------------------------------------}

{- every pass but delay preserves the meaning of a program exactly (≃) -}

simplify-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = Simplify.simplify-correct

enclose-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct = Enclose.enclose-correct

optimize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ optimize-program M ⟧₂ ρ₀
optimize-correct = Optimize.optimize-correct

concretize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = Concretize.concretize-correct

{- delay preserves and reflects the constants a program produces, and
   whether it produces anything -}
delay-correct-const : ∀ {A} (M : Clos3μ.Tm [] A) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-const = Delay.delay-correct-const

delay-correct-nonempty : ∀ {A} (M : Clos3μ.Tm [] A)
  → (nonempty (⟦ M ⟧₃ ρ₀) → nonempty (⟦ delay-program M ⟧₄ ρ₀))
  × (nonempty (⟦ delay-program M ⟧₄ ρ₀) → nonempty (⟦ M ⟧₃ ρ₀))
delay-correct-nonempty = Delay.delay-correct-nonempty

globalize-correct : ∀ {A} (M : Clos4μ.Tm [] A) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ globalize M ⟧₅
globalize-correct = Globalize.globalize-correct

rco-correct : ∀ {A} (P : Clos5μ.Program A) → ⟦ P ⟧₅ ≃ ⟦ ⌜ rco-program P ⌝ₚ ⟧₅
rco-correct = RCO.rco-correct

lift-locals-correct : ∀ {A} (P : Monμ.Program A) → ⟦ ⌜ P ⌝ₚ ⟧₅ ≃ ⟦ lift-program P ⟧ᵢ
lift-locals-correct = LiftLocals.lift-locals-correct

explicate-correct : ∀ {A} (P : Impμ.Program A) → ⟦ P ⟧ᵢ ≃ ⟦ explicate P ⟧ᶜ
explicate-correct = Explicate.explicate-correct

select-correct : ∀ {A} (P : CFGμ.Program A) → ⟦ P ⟧ᶜ ≃ ⟦ select P ⟧ₜ
select-correct = Select.select-correct

{- The whole compiler, for closed programs of any type ----------------------}

{- the compiled program produces the same constants as the original, and
   produces something exactly when the original does: into Clos5μ
   (compile), Monμ (compile-mon), Impμ (compile-imp), CFGμ (compile-cfg)
   and X86μ (compile-x86) -}

compile-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧₅)
  × (const c ∈ ⟦ compile M ⟧₅ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M = proj₁ (Compiler.compile-same M)

compile-correct-nonempty : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧₅)
  × (nonempty ⟦ compile M ⟧₅ → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M = proj₂ (Compiler.compile-same M)

compile-mon-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅)
  × (const c ∈ ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ → const c ∈ ⟦ M ⟧ ρ₀)
compile-mon-correct-const M = proj₁ (Compiler.compile-mon-same M)

compile-mon-correct-nonempty : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅)
  × (nonempty ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ → nonempty (⟦ M ⟧ ρ₀))
compile-mon-correct-nonempty M = proj₂ (Compiler.compile-mon-same M)

compile-imp-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-imp M ⟧ᵢ)
  × (const c ∈ ⟦ compile-imp M ⟧ᵢ → const c ∈ ⟦ M ⟧ ρ₀)
compile-imp-correct-const M = proj₁ (Compiler.compile-imp-same M)

compile-imp-correct-nonempty : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-imp M ⟧ᵢ)
  × (nonempty ⟦ compile-imp M ⟧ᵢ → nonempty (⟦ M ⟧ ρ₀))
compile-imp-correct-nonempty M = proj₂ (Compiler.compile-imp-same M)

compile-cfg-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-cfg M ⟧ᶜ)
  × (const c ∈ ⟦ compile-cfg M ⟧ᶜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-cfg-correct-const M = proj₁ (Compiler.compile-cfg-same M)

compile-cfg-correct-nonempty : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-cfg M ⟧ᶜ)
  × (nonempty ⟦ compile-cfg M ⟧ᶜ → nonempty (⟦ M ⟧ ρ₀))
compile-cfg-correct-nonempty M = proj₂ (Compiler.compile-cfg-same M)

compile-x86-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-x86 M ⟧ₜ)
  × (const c ∈ ⟦ compile-x86 M ⟧ₜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-x86-correct-const M = proj₁ (Compiler.compile-x86-same M)

compile-x86-correct-nonempty : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-x86 M ⟧ₜ)
  × (nonempty ⟦ compile-x86 M ⟧ₜ → nonempty (⟦ M ⟧ ρ₀))
compile-x86-correct-nonempty M = proj₂ (Compiler.compile-x86-same M)

{- The end-to-end theorem, for a main program of type Int: the same
   constants, and something exactly when the original produces
   something -}

compile-x86-int-const : ∀ (M : ISWIMμ.Tm [] (base Int)) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-x86 M ⟧ₜ)
  × (const c ∈ ⟦ compile-x86 M ⟧ₜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-x86-int-const M = proj₁ (Compiler.compile-x86-int M)

compile-x86-int-nonempty : ∀ (M : ISWIMμ.Tm [] (base Int))
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-x86 M ⟧ₜ)
  × (nonempty ⟦ compile-x86 M ⟧ₜ → nonempty (⟦ M ⟧ ρ₀))
compile-x86-int-nonempty M = proj₂ (Compiler.compile-x86-int M)
