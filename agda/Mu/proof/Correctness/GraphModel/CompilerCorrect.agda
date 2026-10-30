{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) in the plain
  graph model, as for the typed pipeline
  (proof/Correctness/Graph/CompilerCorrect.agda): for a closed ISWIMμ
  program, the compiled program, in PairClosμ, GlobalFunμ, Monμ (by its
  embedding), Impμ, CFGμ and X86μ, produces the same constants as the
  source, and produces something exactly when the source does (Same).
  Every pass but delay preserves the meaning exactly (≃); delay
  preserves and reflects constants and nonemptiness. The end-to-end
  theorem is stated for a main program of type Int, the observation of
  ISWIMμ (compile-int); the others hold at any type.

-}

module Mu.proof.Correctness.GraphModel.CompilerCorrect where

open import Framework.Primitives using (base-rep; Int)
open import Framework.Iff using (_⇔_)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to dconst)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Capture using (capture)
open import Mu.Compiler.Prune using (prune-program)
open import Mu.Compiler.Pipeline
open import Mu.Semantics.GraphModel.ISWIM using (⟦_⟧)
open import Mu.Semantics.GraphModel.EnvClos using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Mu.Semantics.GraphModel.PairClos using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.Semantics.GraphModel.GlobalFun using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Mu.Semantics.GraphModel.Imp using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.Semantics.GraphModel.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.Semantics.GraphModel.X86 using (⟦_⟧ₜ)
open import Mu.proof.Correctness.GraphModel.SimplifyCorrect using (simplify-correct)
open import Mu.proof.Correctness.GraphModel.CaptureCorrect using (capture-correct)
open import Mu.proof.Correctness.GraphModel.PruneCorrect using (prune-correct)
open import Mu.proof.Correctness.GraphModel.ConcretizeCorrect using (concretize-correct)
open import Mu.proof.Correctness.GraphModel.DelayCorrect using (delay-correct-const; delay-correct-nonempty)
open import Mu.proof.Correctness.GraphModel.GlobalizeCorrect using (globalize-correct)
open import Mu.proof.Correctness.GraphModel.RCOCorrect using (rco-correct)
open import Mu.proof.Correctness.GraphModel.LiftLocalsCorrect using (lift-locals-correct)
open import Mu.proof.Correctness.GraphModel.ExplicateCorrect using (explicate-correct)
open import Mu.proof.Correctness.GraphModel.SelectCorrect using (select-correct)
open import Mu.proof.Semantics.GraphModel.Binders using (ne-≃)

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

{- the same constants, and nonempty together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = (∀ {B} (c : base-rep B) → (dconst c ∈ D) ⇔ (dconst c ∈ E)) × (nonempty D ⇔ nonempty E)

⇔∘ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔∘ ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

{- one Same after another (then), and an equation as one (same) -}
then : ∀ {D E F} → Same D E → Same E F → Same D F
then ⟨ c , n ⟩ ⟨ c' , n' ⟩ = ⟨ (λ k → ⇔∘ (c k) (c' k)) , ⇔∘ n n' ⟩

same : ∀ {D E} → D ≃ E → Same D E
same D≃@(⟨ D⊆ , E⊆ ⟩) = ⟨ (λ k → ⟨ D⊆ _ , E⊆ _ ⟩) , ⟨ ne-≃ D≃ , ne-≃ (≃-sym D≃) ⟩ ⟩

{- closure conversion, enclose = concretize ∘ prune ∘ capture -}
enclose-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₃ ρ₀
enclose-correct M =
  ≃-trans (capture-correct M) (≃-trans (prune-correct (capture M)) (concretize-correct (prune-program (capture M))))

compile-to-PairClos-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) (⟦ compile-to-PairClos M ⟧₄ ρ₀)
compile-to-PairClos-same M =
  then (same (≃-trans (simplify-correct M) (enclose-correct M₁)))
       ⟨ delay-correct-const (enclose M₁) , delay-correct-nonempty (enclose M₁) ⟩
  where
  M₁ = simplify M

compile-to-GlobalFun-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile-to-GlobalFun M ⟧₅
compile-to-GlobalFun-same M = then (compile-to-PairClos-same M) (same (globalize-correct (compile-to-PairClos M)))

compile-to-Mon-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ ⌜ compile-to-Mon M ⌝ₚ ⟧₅
compile-to-Mon-same M = then (compile-to-GlobalFun-same M) (same (rco-correct (compile-to-GlobalFun M)))

compile-to-Imp-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile-to-Imp M ⟧ᵢ
compile-to-Imp-same M = then (compile-to-Mon-same M) (same (lift-locals-correct (compile-to-Mon M)))

compile-to-CFG-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile-to-CFG M ⟧ᶜ
compile-to-CFG-same M = then (compile-to-Imp-same M) (same (explicate-correct (compile-to-Imp M)))

compile-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧ₜ
compile-same M = then (compile-to-CFG-same M) (same (select-correct (compile-to-CFG M)))

{- the end-to-end theorem, for a main program of type Int -}
compile-int : ∀ (M : Tm [] (base Int)) → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧ₜ
compile-int = compile-same
