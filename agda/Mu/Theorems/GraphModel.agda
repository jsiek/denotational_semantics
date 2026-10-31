{-

  The correctness of the FPC compiler in the graph model: the
  statements of Theorem 4.1 (compiler correctness) and Theorem 4.4
  (correctness of split) of the paper. The proofs are in
  Mu/proof/Correctness/GraphModel/; each theorem here is one of them,
  with its type written out.

    FPC --simplify--> FPC --capture--> Closμ --prune--> Closμ
           --concretize--> EnvClosμ --split--> PairClosμ
           --hoist--> GlobalFunμ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

  compile (Mu/Compiler/Pipeline.agda) is the composition of the ten
  passes. A denotation is a set of graph elements
  (Framework/GraphModel/Domain.agda): c ∈ D is const c ∈ D, D ≠ ∅ is
  nonempty D, and the empty environment of a closed term is ρ₀
  (Mu/Semantics/GraphModel/Closed.agda: every variable denotes {⟨⟩}).

  To read them: the languages (Mu/Language/), the passes
  (Mu/Compiler/), the graph-model semantics of FPC, EnvClosμ,
  PairClosμ and X86μ (Mu/Semantics/GraphModel/), and the domain and
  operators they are built from (Framework/GraphModel/).

-}

module Mu.Theorems.GraphModel where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (const)

open import Mu.Language.Type using (base)
import Mu.Language.FPC as FPC
import Mu.Language.EnvClos as EnvClosμ

open import Mu.Compiler.Split using (split-program)
open import Mu.Compiler.Pipeline using (compile)

open import Mu.Semantics.GraphModel.FPC using (⟦_⟧)
open import Mu.Semantics.GraphModel.EnvClos using () renaming (⟦_⟧ to ⟦_⟧ᵉ)
open import Mu.Semantics.GraphModel.PairClos using () renaming (⟦_⟧ to ⟦_⟧ᶠ)
open import Mu.Semantics.GraphModel.X86 using (⟦_⟧ₜ)
open import Mu.Semantics.GraphModel.Closed public using (ρ₀)

import Mu.proof.Correctness.GraphModel.SplitCorrect as Split
import Mu.proof.Correctness.GraphModel.CompilerCorrect as Compiler

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂)

{- Theorem 4.1 (Compiler correctness) -----------------------------------------}

{- for a closed FPC term M of type Int, and every constant c:
   c ∈ ⟦ M ⟧ if and only if c ∈ ⟦ compile M ⟧ -}
compile-int-const : ∀ (M : FPC.Tm [] (base Int)) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧ₜ)
  × (const c ∈ ⟦ compile M ⟧ₜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-int-const M = proj₁ (Compiler.compile-int M)

{- moreover, ⟦ M ⟧ ≠ ∅ if and only if ⟦ compile M ⟧ ≠ ∅ -}
compile-int-nonempty : ∀ (M : FPC.Tm [] (base Int))
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧ₜ)
  × (nonempty ⟦ compile M ⟧ₜ → nonempty (⟦ M ⟧ ρ₀))
compile-int-nonempty M = proj₂ (Compiler.compile-int M)

{- Theorem 4.1, for closed terms of every type (the paper: "The same
   statement holds for closed terms of every type") -}

compile-correct-const : ∀ {A} (M : FPC.Tm [] A) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧ₜ)
  × (const c ∈ ⟦ compile M ⟧ₜ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M = proj₁ (Compiler.compile-same M)

compile-correct-nonempty : ∀ {A} (M : FPC.Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧ₜ)
  × (nonempty ⟦ compile M ⟧ₜ → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M = proj₂ (Compiler.compile-same M)

{- Theorem 4.4 (Correctness of split) -----------------------------------------}

{- for a closed EnvClosμ term M, and every constant c:
   c ∈ ⟦ M ⟧ if and only if c ∈ ⟦ split M ⟧ -}
split-correct-const : ∀ {A} (M : EnvClosμ.Tm [] A) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵉ ρ₀ → const c ∈ ⟦ split-program M ⟧ᶠ ρ₀)
  × (const c ∈ ⟦ split-program M ⟧ᶠ ρ₀ → const c ∈ ⟦ M ⟧ᵉ ρ₀)
split-correct-const = Split.split-correct-const

{- moreover, ⟦ M ⟧ ≠ ∅ if and only if ⟦ split M ⟧ ≠ ∅ -}
split-correct-nonempty : ∀ {A} (M : EnvClosμ.Tm [] A)
  → (nonempty (⟦ M ⟧ᵉ ρ₀) → nonempty (⟦ split-program M ⟧ᶠ ρ₀))
  × (nonempty (⟦ split-program M ⟧ᶠ ρ₀) → nonempty (⟦ M ⟧ᵉ ρ₀))
split-correct-nonempty = Split.split-correct-nonempty
