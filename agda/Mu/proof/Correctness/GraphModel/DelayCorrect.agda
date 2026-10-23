{-

  Correctness of delay (EnvClosμ → FlatClosμ) in the graph model, as for
  typed delay (proof/Correctness/Graph/DelayCorrect.agda): delay changes
  how a closure is represented, so it is not an equation; it preserves
  (DelayPreserve) and reflects (DelayReflect) the constants a closed
  program produces, and whether it produces anything.

-}

open import Framework.GraphModel.Prelude
open import Framework.Primitives using (base-rep)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Mu.Language.EnvClos using (Tm)
open import Mu.Compiler.Delay using (delay-program)
open import Mu.Semantics.GraphModel.EnvClos using (⟦_⟧)
open import Mu.Semantics.GraphModel.FlatClos renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.proof.Correctness.GraphModel.DelayPreserve using (preserve-const; preserve-nonempty)
open import Mu.proof.Correctness.GraphModel.DelayReflect using (reflect-const; reflect-nonempty)

open import Data.List using ([])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

module Mu.proof.Correctness.GraphModel.DelayCorrect where

delay-correct-const : ∀ {A} (M : Tm [] A) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
delay-correct-const M c = ⟨ preserve-const M c , reflect-const M c ⟩

delay-correct-nonempty : ∀ {A} (M : Tm [] A)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay-program M ⟧₄ ρ₀))
  × (nonempty (⟦ delay-program M ⟧₄ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
delay-correct-nonempty M = ⟨ preserve-nonempty M , reflect-nonempty M ⟩
