{-

  The closure-conversion passes of the pilot (Mu/Compiler/Pipeline.agda)
  in the plain graph model, as for the typed pipeline
  (proof/Correctness/Graph/CompilerCorrect.agda): for a closed ISWIMμ
  program, compile₄ produces the same constants as the source, and
  produces something exactly when the source does (Same). Enclose,
  optimize and concretize preserve the meaning exactly (≃); delay
  preserves and reflects constants and nonemptiness.

-}

module Mu.proof.Correctness.Graph.CompilerCorrect where

open import Framework.Primitives using (base-rep)
open import Framework.Iff using (_⇔_)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ρ₀) renaming (const to dconst)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Pipeline using (compile₄)
open import Mu.Semantics.Graph.ISWIM using (⟦_⟧)
open import Mu.Semantics.Graph.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.proof.Correctness.Graph.EncloseCorrect using (enclose-correct)
open import Mu.proof.Correctness.Graph.OptimizeCorrect using (optimize-correct)
open import Mu.proof.Correctness.Graph.ConcretizeCorrect using (concretize-correct)
open import Mu.proof.Correctness.Graph.DelayCorrect using (delay-correct-const; delay-correct-nonempty)

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

{- the same constants, and nonempty together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = (∀ {B} (c : base-rep B) → (dconst c ∈ D) ⇔ (dconst c ∈ E)) × (nonempty D ⇔ nonempty E)

⇔∘ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔∘ ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

compile₄-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) (⟦ compile₄ M ⟧₄ ρ₀)
compile₄-same M with ≃-trans (enclose-correct M) (≃-trans (optimize-correct (enclose M)) (concretize-correct M₂))
  where
  M₂ = optimize-program (enclose M)
... | ⟨ D⊆ , E⊆ ⟩ =
  ⟨ (λ k → ⇔∘ ⟨ D⊆ _ , E⊆ _ ⟩ (delay-correct-const M₃ k))
  , ⇔∘ ⟨ (λ { ⟨ d , d∈ ⟩ → ⟨ d , D⊆ d d∈ ⟩ }) , (λ { ⟨ d , d∈ ⟩ → ⟨ d , E⊆ d d∈ ⟩ }) ⟩ (delay-correct-nonempty M₃) ⟩
  where M₃ = concretize-program (optimize-program (enclose M))
