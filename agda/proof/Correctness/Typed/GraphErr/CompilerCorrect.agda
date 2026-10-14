{-

  The typed pilot's compiler (Compiler/Typed/Pipeline.agda) in the graph
  model with errors: for a well-scoped closed ISWIM program, the Clos4ᵀ
  program errs exactly when the source does, produces the same constants,
  and produces a value exactly when the source does (Same, as in
  proof/Correctness/GraphErr/CompilerCorrect.agda, repeated here). Cast
  insertion, enclose and concretize preserve the meaning exactly (≃);
  delay preserves and reflects the three facts.

-}

module proof.Correctness.Typed.GraphErr.CompilerCorrect where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import Framework.Iff using (_⇔_)
open import Language.ISWIM using (AST; Op; sig)
open import Framework.Syntax.Scope Op sig using (WS)
open import Compiler.Typed.Pipeline using (compileᵀ)
open import Compiler.Typed.Cast using (cast-program)
open import Compiler.Typed.Enclose using (enclose)
open import Compiler.Typed.Concretize using (concretize-program)
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
import Semantics.GraphErr.Typed.Clos3
import Semantics.GraphErr.Typed.Clos4 as S4
open import proof.Correctness.Typed.GraphErr.CastCorrect using (cast-correct)
open import proof.Correctness.Typed.GraphErr.EncloseCorrect using (enclose-correct)
open import proof.Correctness.Typed.GraphErr.ConcretizeCorrect using (concretize-correct)
open import proof.Correctness.Typed.GraphErr.DelayCorrect
  using (delay-correct-error; delay-correct-const; delay-correct-val)

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

Same : 𝒫 Value → 𝒫 Value → Set
Same D E = ((ω ∈ D) ⇔ (ω ∈ E)) × (∀ {B} (c : base-rep B) → ((dconst c ∈ D) ⇔ (dconst c ∈ E))) × (val∈ D ⇔ val∈ E)

⇔∘ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔∘ ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

compile-same : ∀ (M : AST) (w : WS 0 M) → Same (⟦ M ⟧ ρ₀) (S4.⟦ compileᵀ M w ⟧ ρ₀)
compile-same M w = go (≃-trans (cast-correct M w) (≃-trans (enclose-correct M₁) (concretize-correct (enclose M₁))))
  where
  M₁ = cast-program M w
  M₃ = concretize-program (enclose M₁)
  go : ⟦ M ⟧ ρ₀ ≃ Semantics.GraphErr.Typed.Clos3.⟦ M₃ ⟧ ρ₀ → Same (⟦ M ⟧ ρ₀) (S4.⟦ compileᵀ M w ⟧ ρ₀)
  go ⟨ D⊆ , E⊆ ⟩ =
    ⟨ ⇔∘ ⟨ D⊆ ω , E⊆ ω ⟩ (delay-correct-error M₃)
    , ⟨ (λ c → ⇔∘ ⟨ D⊆ (dconst c) , E⊆ (dconst c) ⟩ (delay-correct-const M₃ c))
      , ⇔∘ ⟨ (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ D⊆ d d∈ , d≢ ⟩ ⟩ })
           , (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ E⊆ d d∈ , d≢ ⟩ ⟩ }) ⟩ (delay-correct-val M₃) ⟩ ⟩
