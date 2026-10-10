{-

  Correctness of the whole closure-conversion compiler:

    ISWIM --annotate--> Clos1 --enclose--> Clos2 --optimize--> Clos2
          --concretize--> Clos3 --delay--> Clos4 --globalize--> Clos5

  For a closed ISWIM program, the compiled Clos5 program produces the same
  constants as the original, and produces something exactly when the
  original does.

-}

open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Lang.ISWIM
open import Compiler.Model.Graph.Sem.ISWIM
import Compiler.Lang.Clos5 as L5
open import Compiler.Model.Graph.Sem.Clos5Iswim using (⟦_⟧ₚ)
open import Compiler.Compile.Globalize using (globalize)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.AnnotateCorrect
  using (compile-iswim; compile-iswim-correct-const; compile-iswim-correct-nonempty)
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect using (globalize-correct)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

module Compiler.Model.Graph.Correctness.CompilerCorrect where

compile : AST → L5.Program
compile M = globalize (compile-iswim M)

compile-correct-const : ∀ (M : AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧ₚ)
  × (const c ∈ ⟦ compile M ⟧ₚ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M c =
  ⟨ (λ c∈ → proj₁ G≃ _ (proj₁ rest c∈))
  , (λ c∈ → proj₂ rest (proj₂ G≃ _ c∈)) ⟩
  where
  rest = compile-iswim-correct-const M c
  G≃ = globalize-correct (compile-iswim M)

compile-correct-nonempty : ∀ (M : AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧ₚ)
  × (nonempty ⟦ compile M ⟧ₚ → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M =
  ⟨ (λ ne → let ne' = proj₁ rest ne in ⟨ proj₁ ne' , proj₁ G≃ _ (proj₂ ne') ⟩)
  , (λ ne → proj₂ rest ⟨ proj₁ ne , proj₂ G≃ _ (proj₂ ne) ⟩) ⟩
  where
  rest = compile-iswim-correct-nonempty M
  G≃ = globalize-correct (compile-iswim M)
