{-

  Correctness of typed split (Clos3ᵀ → Clos4ᵀ) in the graph model with
  errors: split changes how a closure is represented, so it is not an
  equation; it preserves (SplitPreserve) and reflects (SplitReflect) an
  error, the constants a program produces, and whether it produces a
  value.

-}

open import Framework.GraphModel.Prelude
open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import proof.Framework.GraphModel.Domain using (ρ₀)
open import Language.Typed.Type using (Any)
open import Language.Typed.Clos3 using (Tm)
open import Compiler.Split using (split-program)
open import Semantics.GraphErr.Typed.Clos3 using (⟦_⟧)
open import Semantics.GraphErr.Typed.Clos4 renaming (⟦_⟧ to ⟦_⟧₄)
open import proof.Correctness.GraphErr.SplitPreserve using (preserve₀; ⊑-val)
open import proof.Correctness.GraphErr.SplitReflect using (reflect-error; reflect-const; reflect-val)

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Level using (lower)

module proof.Correctness.GraphErr.SplitCorrect where

split-correct-error : ∀ (M : Tm [] Any)
  → (ω ∈ ⟦ M ⟧ ρ₀ → ω ∈ ⟦ split-program M ⟧₄ ρ₀) × (ω ∈ ⟦ split-program M ⟧₄ ρ₀ → ω ∈ ⟦ M ⟧ ρ₀)
split-correct-error M = ⟨ (λ ω∈ → lower (preserve₀ M ω ω∈)) , reflect-error M ⟩

split-correct-const : ∀ (M : Tm [] Any) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ split-program M ⟧₄ ρ₀)
  × (const c ∈ ⟦ split-program M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
split-correct-const M c = ⟨ (λ c∈ → lower (preserve₀ M (const c) c∈)) , reflect-const M c ⟩

split-correct-val : ∀ (M : Tm [] Any)
  → (val∈ (⟦ M ⟧ ρ₀) → val∈ (⟦ split-program M ⟧₄ ρ₀)) × (val∈ (⟦ split-program M ⟧₄ ρ₀) → val∈ (⟦ M ⟧ ρ₀))
split-correct-val M =
  ⟨ (λ { ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ → let ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⊑-val v≢ (preserve₀ M v v∈) in ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ }) , reflect-val M ⟩
