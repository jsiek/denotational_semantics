{-

  Correctness of typed split (Clos3ᵀ → Clos4ᵀ) in the graph model: split
  changes how a closure is represented, so it is not an equation; it
  preserves (SplitPreserve) and reflects (SplitReflect) the constants a
  closed program produces, and whether it produces anything.

-}

open import Framework.GraphModel.Prelude
open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.Domain using (ρ₀)
open import Language.Typed.Type using (Any)
open import Language.Typed.Clos3 using (Tm)
open import Compiler.Split using (split-program)
open import Semantics.Graph.Typed.Clos3 using (⟦_⟧)
open import Semantics.Graph.Typed.Clos4 renaming (⟦_⟧ to ⟦_⟧₄)
open import proof.Correctness.Graph.SplitPreserve using (preserve-const; preserve-nonempty)
open import proof.Correctness.Graph.SplitReflect using (reflect-const; reflect-nonempty)

open import Data.List using ([])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

module proof.Correctness.Graph.SplitCorrect where

split-correct-const : ∀ (M : Tm [] Any) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ split-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ split-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
split-correct-const M c = ⟨ preserve-const M c , reflect-const M c ⟩

split-correct-nonempty : ∀ (M : Tm [] Any)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ split-program M ⟧₄ ρ₀))
  × (nonempty (⟦ split-program M ⟧₄ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
split-correct-nonempty M = ⟨ preserve-nonempty M , reflect-nonempty M ⟩
