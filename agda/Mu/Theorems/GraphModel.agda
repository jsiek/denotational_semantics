{-

  The correctness of the ISWIMμ compiler in the graph model: the
  statements of Theorem 4.1 (compiler correctness) and Theorem 4.4
  (correctness of delay) of the paper. The proofs are in
  Mu/proof/Correctness/GraphModel/; each theorem here is one of them,
  with its type written out.

    ISWIMμ --simplify--> ISWIMμ --enclose--> Closμ --optimize--> Closμ
           --concretize--> EnvClosμ --delay--> PairClosμ
           --globalize--> GlobalFunμ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

  compile (Mu/Compiler/Pipeline.agda) is the composition of the ten
  passes. A denotation is a set of graph elements
  (Framework/GraphModel/Domain.agda): c ∈ D is const c ∈ D, D ≠ ∅ is
  nonempty D, and the empty environment of a closed term is ρ₀
  (Mu/Semantics/GraphModel/Closed.agda: every variable denotes {⟨⟩}).

  To read them: the languages (Mu/Language/), the passes
  (Mu/Compiler/), the graph-model semantics of ISWIMμ, EnvClosμ,
  PairClosμ and X86μ (Mu/Semantics/GraphModel/), and the domain and
  operators they are built from (Framework/GraphModel/).

-}

module Mu.Theorems.GraphModel where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (const)

open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.EnvClos as EnvClosμ

open import Mu.Compiler.Delay using (delay-program)
open import Mu.Compiler.Pipeline using (compile)

open import Mu.Semantics.GraphModel.ISWIM using (⟦_⟧)
open import Mu.Semantics.GraphModel.EnvClos using () renaming (⟦_⟧ to ⟦_⟧ᵉ)
open import Mu.Semantics.GraphModel.PairClos using () renaming (⟦_⟧ to ⟦_⟧ᶠ)
open import Mu.Semantics.GraphModel.X86 using (⟦_⟧ₜ)
open import Mu.Semantics.GraphModel.Closed public using (ρ₀)

import Mu.proof.Correctness.GraphModel.DelayCorrect as Delay
import Mu.proof.Correctness.GraphModel.CompilerCorrect as Compiler

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂)

{- Theorem 4.1 (Compiler correctness) -----------------------------------------}

{- for a closed ISWIMμ term M of type Int, and every constant c:
   c ∈ ⟦ M ⟧ if and only if c ∈ ⟦ compile M ⟧ -}
compile-int-const : ∀ (M : ISWIMμ.Tm [] (base Int)) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧ₜ)
  × (const c ∈ ⟦ compile M ⟧ₜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-int-const M = proj₁ (Compiler.compile-int M)

{- moreover, ⟦ M ⟧ ≠ ∅ if and only if ⟦ compile M ⟧ ≠ ∅ -}
compile-int-nonempty : ∀ (M : ISWIMμ.Tm [] (base Int))
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧ₜ)
  × (nonempty ⟦ compile M ⟧ₜ → nonempty (⟦ M ⟧ ρ₀))
compile-int-nonempty M = proj₂ (Compiler.compile-int M)

{- Theorem 4.1, for closed terms of every type (the paper: "The same
   statement holds for closed terms of every type") -}

compile-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧ₜ)
  × (const c ∈ ⟦ compile M ⟧ₜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M = proj₁ (Compiler.compile-same M)

compile-correct-nonempty : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧ₜ)
  × (nonempty ⟦ compile M ⟧ₜ → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M = proj₂ (Compiler.compile-same M)

{- Theorem 4.4 (Correctness of delay) -----------------------------------------}

{- for a closed EnvClosμ term M, and every constant c:
   c ∈ ⟦ M ⟧ if and only if c ∈ ⟦ delay M ⟧ -}
delay-correct-const : ∀ {A} (M : EnvClosμ.Tm [] A) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵉ ρ₀ → const c ∈ ⟦ delay-program M ⟧ᶠ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧ᶠ ρ₀ → const c ∈ ⟦ M ⟧ᵉ ρ₀)
delay-correct-const = Delay.delay-correct-const

{- moreover, ⟦ M ⟧ ≠ ∅ if and only if ⟦ delay M ⟧ ≠ ∅ -}
delay-correct-nonempty : ∀ {A} (M : EnvClosμ.Tm [] A)
  → (nonempty (⟦ M ⟧ᵉ ρ₀) → nonempty (⟦ delay-program M ⟧ᶠ ρ₀))
  × (nonempty (⟦ delay-program M ⟧ᶠ ρ₀) → nonempty (⟦ M ⟧ᵉ ρ₀))
delay-correct-nonempty = Delay.delay-correct-nonempty
