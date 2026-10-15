{-

  Correctness of typed delay (Clos3ᵀ → Clos4ᵀ) in the graph model with
  errors: delay changes how a closure is represented, so it is not an
  equation; it preserves (DelayPreserve) and reflects (DelayReflect) an
  error, the constants a program produces, and whether it produces a
  value.

-}

open import Framework.GraphModel.Prelude
open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import proof.Framework.GraphModel.Domain using (ρ₀)
open import Language.Typed.Type using (Any)
open import Language.Typed.Clos3 using (Tm)
open import Compiler.Delay using (delay-program)
open import Semantics.GraphErr.Typed.Clos3 using (⟦_⟧)
open import Semantics.GraphErr.Typed.Clos4 renaming (⟦_⟧ to ⟦_⟧₄)
open import proof.Correctness.GraphErr.DelayPreserve using (preserve₀; ⊑-val)
open import proof.Correctness.GraphErr.DelayReflect using (reflect-error; reflect-const; reflect-val)

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Level using (lower)

module proof.Correctness.GraphErr.DelayCorrect where

delay-correct-error : ∀ (M : Tm [] Any)
  → (ω ∈ ⟦ M ⟧ ρ₀ → ω ∈ ⟦ delay-program M ⟧₄ ρ₀) × (ω ∈ ⟦ delay-program M ⟧₄ ρ₀ → ω ∈ ⟦ M ⟧ ρ₀)
delay-correct-error M = ⟨ (λ ω∈ → lower (preserve₀ M ω ω∈)) , reflect-error M ⟩

delay-correct-const : ∀ (M : Tm [] Any) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
delay-correct-const M c = ⟨ (λ c∈ → lower (preserve₀ M (const c) c∈)) , reflect-const M c ⟩

delay-correct-val : ∀ (M : Tm [] Any)
  → (val∈ (⟦ M ⟧ ρ₀) → val∈ (⟦ delay-program M ⟧₄ ρ₀)) × (val∈ (⟦ delay-program M ⟧₄ ρ₀) → val∈ (⟦ M ⟧ ρ₀))
delay-correct-val M =
  ⟨ (λ { ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ → let ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⊑-val v≢ (preserve₀ M v v∈) in ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ }) , reflect-val M ⟩
