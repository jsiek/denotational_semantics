{-

  The correctness of the compiler in the graph model: the public
  statements. The proofs are in proof/Correctness/Graph/; each
  theorem here is one of them, with its type written out.

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86

  To read them: the typed languages (Language/Typed/), the passes
  (Compiler/), the semantics of each typed language
  (Semantics/Graph/Typed/; Monᵀ means its embedding into Clos5ᵀ, ⌜_⌝ₚ),
  those of ISWIM and X86 (Semantics/Graph/), and the domain and operators
  they are built from (Framework/GraphModel/). In the graph model a
  failed project, like any error, means ∅.

-}

module Theorems.Denotational where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (⌈_⌉; _∈_; nonempty; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; const; ω)

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

open import Semantics.Graph.ISWIM using (⟦_⟧)
open import Semantics.Graph.Typed.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵀ)
open import Semantics.Graph.Typed.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Semantics.Graph.Typed.Clos3 using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Semantics.Graph.Typed.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Semantics.Graph.Typed.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Semantics.Graph.Typed.Imp using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Semantics.Graph.Typed.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Semantics.Graph.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)

import proof.Correctness.Graph.SimplifyCorrect as SimplifyCorrect
import proof.Correctness.Graph.CastCorrect as Cast
import proof.Correctness.Graph.EncloseCorrect as Enclose
import proof.Correctness.Graph.OptimizeCorrect as Optimize
import proof.Correctness.Graph.ConcretizeCorrect as Concretize
import proof.Correctness.Graph.DelayCorrect as Delay
import proof.Correctness.Graph.GlobalizeCorrect as Globalize
import proof.Correctness.Graph.RCOCorrect as RCO
import proof.Correctness.Graph.LiftLocalsCorrect as LiftLocals
import proof.Correctness.Graph.ExplicateCorrect as Explicate
import proof.Correctness.Graph.SelectCorrect as Select
import proof.Correctness.Graph.CompilerCorrect as Compiler

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂)

{- The environment of a closed program: every variable denotes {ω}, the
   default value. (It only matters for open terms, as the passes are
   stated on whole terms.) -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

{- Each pass ------------------------------------------------------------------}

{- every pass but delay preserves the meaning of a program exactly (≃) -}

{- simplify (ISWIM → ISWIM, the first pass) -}
simplify-correct : ∀ (M : ISWIM.AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = SimplifyCorrect.simplify-correct

cast-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ cast-closed M ⟧ᵀ ρ₀
cast-correct = Cast.cast-correct

enclose-correct : ∀ (M : ISWIMᵀ.Tm 0 Any) → ⟦ M ⟧ᵀ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct = Enclose.enclose-correct

optimize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ optimize-program M ⟧₂ ρ₀
optimize-correct = Optimize.optimize-correct

concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = Concretize.concretize-correct

{- delay preserves and reflects the constants a program produces, and
   whether it produces anything -}
delay-correct-const : ∀ (M : Clos3ᵀ.Tm [] Any) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-const = Delay.delay-correct-const

delay-correct-nonempty : ∀ (M : Clos3ᵀ.Tm [] Any)
  → (nonempty (⟦ M ⟧₃ ρ₀) → nonempty (⟦ delay-program M ⟧₄ ρ₀))
  × (nonempty (⟦ delay-program M ⟧₄ ρ₀) → nonempty (⟦ M ⟧₃ ρ₀))
delay-correct-nonempty = Delay.delay-correct-nonempty

globalize-correct : ∀ (M : Clos4ᵀ.Tm [] Any) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ globalize M ⟧₅
globalize-correct = Globalize.globalize-correct

rco-correct : ∀ (P : Clos5ᵀ.Program) → ⟦ ⌜ rco-program P ⌝ₚ ⟧₅ ≃ ⟦ P ⟧₅
rco-correct = RCO.rco-correct

lift-locals-correct : ∀ (P : Monᵀ.Program) → ⟦ lift-program P ⟧ᵢ ≃ ⟦ ⌜ P ⌝ₚ ⟧₅
lift-locals-correct = LiftLocals.lift-locals-correct

explicate-correct : ∀ (P : Impᵀ.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
explicate-correct = Explicate.explicate-correct

{- for every CFGᵀ program: a frame is typed, so select's frames are large
   enough by construction -}
select-correct : ∀ (P : CFGᵀ.Program) → ⟦ select P ⟧ₓ ≃ ⟦ P ⟧ᶜ
select-correct = Select.select-correct

{- The whole compiler, for closed programs ----------------------------------}

{- the compiled program produces the same constants as the original, and
   produces something exactly when the original does: into Clos5ᵀ
   (compile), Monᵀ (compile-mon), Impᵀ (compile-imp), CFGᵀ (compile-cfg)
   and X86 (compile-x86) -}

compile-correct-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧₅)
  × (const c ∈ ⟦ compile M ⟧₅ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M w = proj₁ (Compiler.compile-same M w)

compile-correct-nonempty : ∀ (M : ISWIM.AST) → Closed M
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧₅)
  × (nonempty ⟦ compile M ⟧₅ → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M w = proj₂ (Compiler.compile-same M w)

compile-mon-correct-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅)
  × (const c ∈ ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ → const c ∈ ⟦ M ⟧ ρ₀)
compile-mon-correct-const M w = proj₁ (Compiler.compile-mon-same M w)

compile-mon-correct-nonempty : ∀ (M : ISWIM.AST) → Closed M
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅)
  × (nonempty ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ → nonempty (⟦ M ⟧ ρ₀))
compile-mon-correct-nonempty M w = proj₂ (Compiler.compile-mon-same M w)

compile-imp-correct-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-imp M ⟧ᵢ)
  × (const c ∈ ⟦ compile-imp M ⟧ᵢ → const c ∈ ⟦ M ⟧ ρ₀)
compile-imp-correct-const M w = proj₁ (Compiler.compile-imp-same M w)

compile-imp-correct-nonempty : ∀ (M : ISWIM.AST) → Closed M
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-imp M ⟧ᵢ)
  × (nonempty ⟦ compile-imp M ⟧ᵢ → nonempty (⟦ M ⟧ ρ₀))
compile-imp-correct-nonempty M w = proj₂ (Compiler.compile-imp-same M w)

compile-cfg-correct-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-cfg M ⟧ᶜ)
  × (const c ∈ ⟦ compile-cfg M ⟧ᶜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-cfg-correct-const M w = proj₁ (Compiler.compile-cfg-same M w)

compile-cfg-correct-nonempty : ∀ (M : ISWIM.AST) → Closed M
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-cfg M ⟧ᶜ)
  × (nonempty ⟦ compile-cfg M ⟧ᶜ → nonempty (⟦ M ⟧ ρ₀))
compile-cfg-correct-nonempty M w = proj₂ (Compiler.compile-cfg-same M w)

compile-x86-correct-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile-x86 M ⟧ₓ)
  × (const c ∈ ⟦ compile-x86 M ⟧ₓ → const c ∈ ⟦ M ⟧ ρ₀)
compile-x86-correct-const M w = proj₁ (Compiler.compile-x86-same M w)

compile-x86-correct-nonempty : ∀ (M : ISWIM.AST) → Closed M
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile-x86 M ⟧ₓ)
  × (nonempty ⟦ compile-x86 M ⟧ₓ → nonempty (⟦ M ⟧ ρ₀))
compile-x86-correct-nonempty M w = proj₂ (Compiler.compile-x86-same M w)
