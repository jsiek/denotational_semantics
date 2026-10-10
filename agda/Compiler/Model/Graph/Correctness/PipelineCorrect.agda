{-

  Correctness of the back half of the closure-conversion pipeline:

    Clos1 --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3 --delay--> Clos4

  For a closed Clos1 program in the shape that annotate produces
  (Enclosed), the compiled program produces the same constants as the
  original, and produces something exactly when the original does.

-}

open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Lang.Clos1
open import Compiler.Model.Graph.Sem.Clos1Iswim
import Compiler.Model.Graph.Sem.Clos4Iswim as S4
import Compiler.Lang.Clos4 as L4
open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Compile.Optimize using (optimize-program)
open import Compiler.Compile.Concretize using (concretize-program)
open import Compiler.Compile.Delay using (delay)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.EncloseCorrect using (Enclosed; enclose-correct-closed)
open import Compiler.Model.Graph.Correctness.OptimizeCorrect using (optimize-correct-closed)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (compile-correct-const; compile-correct-nonempty)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

module Compiler.Model.Graph.Correctness.PipelineCorrect where

compile : AST → L4.AST
compile M = delay (concretize-program (optimize-program (enclose M)))

pipeline-correct-const : ∀ (M : AST) → Enclosed M → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ S4.⟦ compile M ⟧ ρ₀)
  × (const c ∈ S4.⟦ compile M ⟧ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
pipeline-correct-const M e c =
  ⟨ (λ c∈ → proj₁ rest (proj₁ M₂≃ _ (proj₁ M₁≃ _ c∈)))
  , (λ c∈ → proj₂ M₁≃ _ (proj₂ M₂≃ _ (proj₂ rest c∈))) ⟩
  where
  M₁≃ = enclose-correct-closed M e
  M₂≃ = optimize-correct-closed (enclose M)
  rest = compile-correct-const (optimize-program (enclose M)) c

pipeline-correct-nonempty : ∀ (M : AST) → Enclosed M
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (S4.⟦ compile M ⟧ ρ₀))
  × (nonempty (S4.⟦ compile M ⟧ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
pipeline-correct-nonempty M e =
  ⟨ (λ ne → proj₁ rest ⟨ proj₁ ne , proj₁ M₂≃ _ (proj₁ M₁≃ _ (proj₂ ne)) ⟩)
  , (λ ne → let ne' = proj₂ rest ne in
            ⟨ proj₁ ne' , proj₂ M₁≃ _ (proj₂ M₂≃ _ (proj₂ ne')) ⟩) ⟩
  where
  M₁≃ = enclose-correct-closed M e
  M₂≃ = optimize-correct-closed (enclose M)
  rest = compile-correct-nonempty (optimize-program (enclose M))
