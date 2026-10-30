{-

  Correctness of split (EnvClosμ → PairClosμ) in the graph model, as for
  typed split (proof/Correctness/Graph/SplitCorrect.agda): split changes
  how a closure is represented, so it is not an equation; it preserves
  (SplitPreserve) and reflects (SplitReflect) the constants a closed
  program produces, and whether it produces anything.

-}

open import Framework.GraphModel.Prelude
open import Framework.Primitives using (base-rep)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Mu.Language.EnvClos using (Tm)
open import Mu.Compiler.Split using (split-program)
open import Mu.Semantics.GraphModel.EnvClos using (⟦_⟧)
open import Mu.Semantics.GraphModel.PairClos renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.proof.Correctness.GraphModel.SplitPreserve using (preserve-const; preserve-nonempty)
open import Mu.proof.Correctness.GraphModel.SplitReflect using (reflect-const; reflect-nonempty)

open import Data.List using ([])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

module Mu.proof.Correctness.GraphModel.SplitCorrect where

split-correct-const : ∀ {A} (M : Tm [] A) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ split-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ split-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
split-correct-const M c = ⟨ preserve-const M c , reflect-const M c ⟩

split-correct-nonempty : ∀ {A} (M : Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ split-program M ⟧₄ ρ₀))
  × (nonempty (⟦ split-program M ⟧₄ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
split-correct-nonempty M = ⟨ preserve-nonempty M , reflect-nonempty M ⟩
