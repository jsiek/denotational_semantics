{-

  The typed pilot: the public statements. Cast insertion (after Essentials
  of Compilation, ch. 9) makes the intermediate languages statically
  typed, and the closure-conversion passes are proved on them, in two
  columns:

    ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --concretize--> Clos3ᵀ --delay--> Clos4ᵀ

  * CEK machines (Semantics/CEK/Typed/): each pass gives Equivalent
    machines; cast insertion relates the untyped ISWIM machine
    (Semantics/CEK/ISWIM.agda) to the typed one.
  * The graph model with errors (Semantics/GraphErr/Typed/): every pass
    but delay preserves the meaning exactly (≃); delay preserves and
    reflects an error, the constants and having a value. Cast insertion
    relates the untyped semantics (Semantics/GraphErr/ISWIM.agda) to the
    typed one.

  Programs are closed, as well-scoped terms in no variables (WS 0).

  To read them: the types and typed languages (Language/Typed/), the
  passes (Compiler/Typed/), and the two semantics.

-}

module Theorems.Typed where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; ω; const)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import Semantics.CEK.Smallstep using (Equivalent)

open import Language.ISWIM using (AST; Op; sig)
open import Framework.Syntax.Scope Op sig using (WS)
open import Language.Typed.Type using (Any)
import Language.Typed.ISWIM as ISWIMᵀ
import Language.Typed.Clos2 as Clos2ᵀ
import Language.Typed.Clos3 as Clos3ᵀ
open import Compiler.Typed.Cast using (cast-program)
open import Compiler.Typed.Enclose using (enclose)
open import Compiler.Typed.Concretize using (concretize-program)
open import Compiler.Typed.Delay using (delay-program)
open import Compiler.Typed.Pipeline using (compileᵀ)

import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.ISWIM as ISWIMᵀₘ
import Semantics.CEK.Typed.Clos2 as Clos2ᵀₘ
import Semantics.CEK.Typed.Clos3 as Clos3ᵀₘ
import Semantics.CEK.Typed.Clos4 as Clos4ᵀₘ
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Typed.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵀ)
open import Semantics.GraphErr.Typed.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Semantics.GraphErr.Typed.Clos3 using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Semantics.GraphErr.Typed.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)

import proof.Correctness.Typed.CEK.CastSim as CastSim
import proof.Correctness.Typed.CEK.EncloseSim as EncloseSim
import proof.Correctness.Typed.CEK.ConcretizeSim as ConcretizeSim
import proof.Correctness.Typed.CEK.DelaySim as DelaySim
import proof.Correctness.Typed.CEK.CompilerSim as CompilerSim
import proof.Correctness.Typed.GraphErr.CastCorrect as CastCorrect
import proof.Correctness.Typed.GraphErr.EncloseCorrect as EncloseCorrect
import proof.Correctness.Typed.GraphErr.ConcretizeCorrect as ConcretizeCorrect
import proof.Correctness.Typed.GraphErr.DelayCorrect as DelayCorrect
import proof.Correctness.Typed.GraphErr.CompilerCorrect as CompilerCorrect

open import Data.List using ([])
open import Data.Product using (_×_)
open import Framework.Iff using (_⇔_)

{- CEK machines -------------------------------------------------------------}

cast-sim : ∀ (M : AST) (w : WS 0 M) → Equivalent (ISWIMₘ.sem M) (ISWIMᵀₘ.sem (cast-program M w))
cast-sim = CastSim.cast-correct

enclose-sim : ∀ (M : ISWIMᵀ.Tm 0 Any) → Equivalent (ISWIMᵀₘ.sem M) (Clos2ᵀₘ.sem (enclose M))
enclose-sim = EncloseSim.enclose-correct

concretize-sim : ∀ (M : Clos2ᵀ.Tm 0 Any)
  → Equivalent (Clos2ᵀₘ.sem M) (Clos3ᵀₘ.sem (concretize-program M))
concretize-sim = ConcretizeSim.concretize-correct

delay-sim : ∀ (M : Clos3ᵀ.Tm [] Any) → Equivalent (Clos3ᵀₘ.sem M) (Clos4ᵀₘ.sem (delay-program M))
delay-sim = DelaySim.delay-correct

compile-sim : ∀ (M : AST) (w : WS 0 M) → Equivalent (ISWIMₘ.sem M) (Clos4ᵀₘ.sem (compileᵀ M w))
compile-sim = CompilerSim.compile-correct

{- The graph model with errors ----------------------------------------------}

ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

cast-correct : ∀ (M : AST) (w : WS 0 M) → ⟦ M ⟧ ρ₀ ≃ ⟦ cast-program M w ⟧ᵀ ρ₀
cast-correct = CastCorrect.cast-correct

enclose-correct : ∀ (M : ISWIMᵀ.Tm 0 Any) → ⟦ M ⟧ᵀ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct = EncloseCorrect.enclose-correct

concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = ConcretizeCorrect.concretize-correct

delay-correct-error : ∀ (M : Clos3ᵀ.Tm [] Any)
  → (ω ∈ ⟦ M ⟧₃ ρ₀ → ω ∈ ⟦ delay-program M ⟧₄ ρ₀) × (ω ∈ ⟦ delay-program M ⟧₄ ρ₀ → ω ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-error = DelayCorrect.delay-correct-error

delay-correct-const : ∀ (M : Clos3ᵀ.Tm [] Any) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-const = DelayCorrect.delay-correct-const

delay-correct-val : ∀ (M : Clos3ᵀ.Tm [] Any)
  → (val∈ (⟦ M ⟧₃ ρ₀) → val∈ (⟦ delay-program M ⟧₄ ρ₀)) × (val∈ (⟦ delay-program M ⟧₄ ρ₀) → val∈ (⟦ M ⟧₃ ρ₀))
delay-correct-val = DelayCorrect.delay-correct-val

{- two meanings err together, hold the same constants, and hold a value
   together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = ((ω ∈ D) ⇔ (ω ∈ E)) × (∀ {B} (c : base-rep B) → ((const c ∈ D) ⇔ (const c ∈ E))) × (val∈ D ⇔ val∈ E)

compile-correct : ∀ (M : AST) (w : WS 0 M) → Same (⟦ M ⟧ ρ₀) (⟦ compileᵀ M w ⟧₄ ρ₀)
compile-correct = CompilerCorrect.compile-same
