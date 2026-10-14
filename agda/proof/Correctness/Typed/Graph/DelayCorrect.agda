{-

  Correctness of typed delay (Clos3ᵀ → Clos4ᵀ) in the graph model: delay
  changes how a closure is represented, so it is not an equation; it
  preserves (DelayPreserve) and reflects (DelayReflect) the constants a
  closed program produces, and whether it produces anything.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Domain using (ρ₀)
open import Language.Typed.Type using (Any)
open import Language.Typed.Clos3 using (Tm)
open import Compiler.Typed.Delay using (delay-program)
open import Semantics.Graph.Typed.Clos3 using (⟦_⟧)
open import Semantics.Graph.Typed.Clos4 renaming (⟦_⟧ to ⟦_⟧₄)
open import proof.Correctness.Typed.Graph.DelayPreserve using (preserve-const; preserve-nonempty)
open import proof.Correctness.Typed.Graph.DelayReflect using (reflect-const; reflect-nonempty)

open import Data.List using ([])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

module proof.Correctness.Typed.Graph.DelayCorrect where

delay-correct-const : ∀ (M : Tm [] Any) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
delay-correct-const M c = ⟨ preserve-const M c , reflect-const M c ⟩

delay-correct-nonempty : ∀ (M : Tm [] Any)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay-program M ⟧₄ ρ₀))
  × (nonempty (⟦ delay-program M ⟧₄ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
delay-correct-nonempty M = ⟨ preserve-nonempty M , reflect-nonempty M ⟩
