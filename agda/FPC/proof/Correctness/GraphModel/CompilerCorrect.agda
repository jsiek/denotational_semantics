{-

  The FPC compiler (FPC/Compiler/Pipeline.agda) in the plain
  graph model, as for the typed pipeline
  (ISWIM/proof/Correctness/Graph/CompilerCorrect.agda): for a closed FPC
  program, the compiled program, in PairClosμ, GlobalFunμ, Monμ (by its
  embedding), Impμ, CFGμ and X86μ, produces the same constants as the
  source, and produces something exactly when the source does (Same).
  Every pass but split preserves the meaning exactly (≃); split
  preserves and reflects constants and nonemptiness. The end-to-end
  theorem is stated for a main program of type Int, the observation of
  FPC (compile-int); the others hold at any type.

-}

module FPC.proof.Correctness.GraphModel.CompilerCorrect where

open import Framework.Primitives using (base-rep; Int)
open import proof.Framework.Iff using (_⇔_; ⇔∘)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to
  dconst)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import FPC.Language.Type using (base)
open import FPC.Language.FPC using (Tm)
open import FPC.Language.Mon using (⌜_⌝ₚ)
open import FPC.Compiler.Simplify using (simplify)
open import FPC.Compiler.Capture using (capture)
open import FPC.Compiler.Prune using (prune-program)
open import FPC.Compiler.Pipeline
open import FPC.Semantics.GraphModel.FPC using (⟦_⟧)
open import FPC.Semantics.GraphModel.EnvClos using () renaming (⟦_⟧ to ⟦_⟧₃)
open import FPC.Semantics.GraphModel.PairClos using () renaming (⟦_⟧ to ⟦_⟧₄)
open import FPC.Semantics.GraphModel.GlobalFun using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import FPC.Semantics.GraphModel.Imp using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import FPC.Semantics.GraphModel.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import FPC.Semantics.GraphModel.X86 using (⟦_⟧ₜ)
open import FPC.proof.Correctness.GraphModel.SimplifyCorrect using
  (simplify-correct)
open import FPC.proof.Correctness.GraphModel.CaptureCorrect using
  (capture-correct)
open import FPC.proof.Correctness.GraphModel.PruneCorrect using (prune-correct)
open import FPC.proof.Correctness.GraphModel.ConcretizeCorrect using
  (concretize-correct)
open import FPC.proof.Correctness.GraphModel.SplitCorrect using
  (split-correct-const; split-correct-nonempty)
open import FPC.proof.Correctness.GraphModel.HoistCorrect using (hoist-correct)
open import FPC.proof.Correctness.GraphModel.RCOCorrect using (rco-correct)
open import FPC.proof.Correctness.GraphModel.LiftLocalsCorrect using
  (lift-locals-correct)
open import FPC.proof.Correctness.GraphModel.ExplicateCorrect using
  (explicate-correct)
open import FPC.proof.Correctness.GraphModel.SelectCorrect using
  (select-correct)
open import FPC.proof.Semantics.GraphModel.Binders using (ne-≃)

open import Data.List using ([])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

{- the same constants, and nonempty together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E =
  (∀ {B} (c : base-rep B) → (dconst c ∈ D) ⇔ (dconst c ∈ E))
  × (nonempty D ⇔ nonempty E)

{- one Same after another (then), and an equation as one (same) -}
then : ∀ {D E F}
  → Same D E
  → Same E F
  → Same D F
then ⟨ c , n ⟩ ⟨ c' , n' ⟩ = ⟨ (λ k → ⇔∘ (c k) (c' k)) , ⇔∘ n n' ⟩

same : ∀ {D E}
  → D ≃ E
  → Same D E
same D≃@(⟨ D⊆ , E⊆ ⟩) =
  ⟨ (λ k → ⟨ D⊆ _ , E⊆ _ ⟩) , ⟨ ne-≃ D≃ , ne-≃ (≃-sym D≃) ⟩ ⟩

{- closure conversion, enclose = concretize ∘ prune ∘ capture -}
enclose-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₃ ρ₀
enclose-correct M =
  ≃-trans (capture-correct M)
    (≃-trans (prune-correct (capture M))
      (concretize-correct (prune-program (capture M))))

compile-to-PairClos-same : ∀ {A} (M : Tm [] A)
  → Same (⟦ M ⟧ ρ₀) (⟦ compile-to-PairClos M ⟧₄ ρ₀)
compile-to-PairClos-same M =
  then (same (≃-trans (simplify-correct M) (enclose-correct M₁)))
       ⟨ split-correct-const (enclose M₁)
           , split-correct-nonempty (enclose M₁) ⟩
  where
  M₁ = simplify M

compile-to-GlobalFun-same : ∀ {A} (M : Tm [] A)
  → Same (⟦ M ⟧ ρ₀) ⟦ compile-to-GlobalFun M ⟧₅
compile-to-GlobalFun-same M =
  then (compile-to-PairClos-same M)
  (same (hoist-correct (compile-to-PairClos M)))

compile-to-Mon-same : ∀ {A} (M : Tm [] A)
  → Same (⟦ M ⟧ ρ₀) ⟦ ⌜ compile-to-Mon M ⌝ₚ ⟧₅
compile-to-Mon-same M =
  then (compile-to-GlobalFun-same M)
  (same (rco-correct (compile-to-GlobalFun M)))

compile-to-Imp-same : ∀ {A} (M : Tm [] A)
  → Same (⟦ M ⟧ ρ₀) ⟦ compile-to-Imp M ⟧ᵢ
compile-to-Imp-same M =
  then (compile-to-Mon-same M) (same (lift-locals-correct (compile-to-Mon M)))

compile-to-CFG-same : ∀ {A} (M : Tm [] A)
  → Same (⟦ M ⟧ ρ₀) ⟦ compile-to-CFG M ⟧ᶜ
compile-to-CFG-same M =
  then (compile-to-Imp-same M) (same (explicate-correct (compile-to-Imp M)))

compile-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧ₜ
compile-same M =
  then (compile-to-CFG-same M) (same (select-correct (compile-to-CFG M)))

{- the end-to-end theorem, for a main program of type Int -}
compile-int : ∀ (M : Tm [] (base Int)) → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧ₜ
compile-int = compile-same
