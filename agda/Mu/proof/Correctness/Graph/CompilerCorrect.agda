{-

  The compiler of the pilot (Mu/Compiler/Pipeline.agda) in the plain
  graph model, as for the typed pipeline
  (proof/Correctness/Graph/CompilerCorrect.agda): for a closed ISWIMμ
  program, the compiled program, in Clos4μ, Clos5μ, Monμ (by its
  embedding), Impμ, CFGμ and X86μ, produces the same constants as the
  source, and produces something exactly when the source does (Same).
  Every pass but delay preserves the meaning exactly (≃); delay
  preserves and reflects constants and nonemptiness. The end-to-end
  theorem is stated for a main program of type Int, the observation of
  the pilot (compile-x86-int); the others hold at any type.

-}

module Mu.proof.Correctness.Graph.CompilerCorrect where

open import Framework.Primitives using (base-rep; Int)
open import Framework.Iff using (_⇔_)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ρ₀) renaming (const to dconst)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Pipeline
open import Mu.Semantics.Graph.ISWIM using (⟦_⟧)
open import Mu.Semantics.Graph.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.Semantics.Graph.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Mu.Semantics.Graph.Imp using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.Semantics.Graph.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.Semantics.Graph.X86 using (⟦_⟧ₜ)
open import Mu.proof.Correctness.Graph.SimplifyCorrect using (simplify-correct)
open import Mu.proof.Correctness.Graph.EncloseCorrect using (enclose-correct)
open import Mu.proof.Correctness.Graph.OptimizeCorrect using (optimize-correct)
open import Mu.proof.Correctness.Graph.ConcretizeCorrect using (concretize-correct)
open import Mu.proof.Correctness.Graph.DelayCorrect using (delay-correct-const; delay-correct-nonempty)
open import Mu.proof.Correctness.Graph.GlobalizeCorrect using (globalize-correct)
open import Mu.proof.Correctness.Graph.RCOCorrect using (rco-correct)
open import Mu.proof.Correctness.Graph.LiftLocalsCorrect using (lift-locals-correct)
open import Mu.proof.Correctness.Graph.ExplicateCorrect using (explicate-correct)
open import Mu.proof.Correctness.Graph.SelectCorrect using (select-correct)

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

{- the same constants, and nonempty together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = (∀ {B} (c : base-rep B) → (dconst c ∈ D) ⇔ (dconst c ∈ E)) × (nonempty D ⇔ nonempty E)

⇔∘ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔∘ ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

{- Same D E, and E ≃ E' -}
then : ∀ {D E E'} → Same D E → E ≃ E' → Same D E'
then ⟨ c , n ⟩ ⟨ E⊆ , E'⊆ ⟩ =
  ⟨ (λ k → ⇔∘ (c k) ⟨ E⊆ _ , E'⊆ _ ⟩)
  , ⇔∘ n ⟨ (λ { ⟨ d , d∈ ⟩ → ⟨ d , E⊆ d d∈ ⟩ }) , (λ { ⟨ d , d∈ ⟩ → ⟨ d , E'⊆ d d∈ ⟩ }) ⟩ ⟩

compile₄-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) (⟦ compile₄ M ⟧₄ ρ₀)
compile₄-same M with ≃-trans (simplify-correct M) (≃-trans (enclose-correct M₁) (≃-trans (optimize-correct (enclose M₁)) (concretize-correct M₂)))
  where
  M₁ = simplify M
  M₂ = optimize-program (enclose M₁)
... | ⟨ D⊆ , E⊆ ⟩ =
  ⟨ (λ k → ⇔∘ ⟨ D⊆ _ , E⊆ _ ⟩ (delay-correct-const M₃ k))
  , ⇔∘ ⟨ (λ { ⟨ d , d∈ ⟩ → ⟨ d , D⊆ d d∈ ⟩ }) , (λ { ⟨ d , d∈ ⟩ → ⟨ d , E⊆ d d∈ ⟩ }) ⟩ (delay-correct-nonempty M₃) ⟩
  where M₃ = concretize-program (optimize-program (enclose (simplify M)))

compile-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧₅
compile-same M = then (compile₄-same M) (globalize-correct (compile₄ M))

compile-mon-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅
compile-mon-same M = then (compile-same M) (rco-correct (compile M))

compile-imp-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile-imp M ⟧ᵢ
compile-imp-same M = then (compile-mon-same M) (lift-locals-correct (compile-mon M))

compile-cfg-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile-cfg M ⟧ᶜ
compile-cfg-same M = then (compile-imp-same M) (explicate-correct (compile-imp M))

compile-x86-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile-x86 M ⟧ₜ
compile-x86-same M = then (compile-cfg-same M) (select-correct (compile-cfg M))

{- the end-to-end theorem, for a main program of type Int -}
compile-x86-int : ∀ (M : Tm [] (base Int)) → Same (⟦ M ⟧ ρ₀) ⟦ compile-x86 M ⟧ₜ
compile-x86-int = compile-x86-same
