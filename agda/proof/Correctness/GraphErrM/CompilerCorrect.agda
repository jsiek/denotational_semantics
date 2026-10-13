{-

  The whole compiler in the graph model with errors: for a closed ISWIM
  program, the compiled program (into Clos5, monadic Clos5, Imp, CFG and
  X86) errs exactly when the source does, produces the same constants,
  and produces a value exactly when the source does (Same). Every pass but
  delay preserves the meaning exactly (≃); delay preserves and reflects
  these three facts.

-}

module proof.Correctness.GraphErrM.CompilerCorrect where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Simplify using (simplify)
open import Compiler.Enclose using (enclose)
open import Compiler.Optimize using (optimize-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Framework.Iff using (_⇔_)

open import Semantics.GraphErrM.ISWIM using (⟦_⟧)
import Semantics.GraphErrM.Clos4 as S4
open import Semantics.GraphErrM.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Semantics.GraphErrM.ImpK using () renaming (⟦_⟧ᴷₚ to ⟦_⟧ᵢ)
open import Semantics.GraphErrM.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Semantics.GraphErrM.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)

open import proof.Correctness.GraphErrM.SimplifyCorrect using (simplify-correct)
open import proof.Correctness.GraphErrM.EncloseCorrect using (enclose-correct)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import proof.Correctness.GraphErrM.OptimizeCorrect using (optimize-correct-compile)
open import proof.Correctness.GraphErrM.ConcretizeCorrect using (concretize-correct-closed)
open import proof.Correctness.GraphErrM.DelayPreserve
  using (delay-correct-error; delay-correct-const; delay-correct-val)
open import proof.Correctness.GraphErrM.GlobalizeCorrect using (globalize-correct-compile)
open import proof.Correctness.GraphErrM.RCOCorrect using (rco-correct-compile)
open import proof.Correctness.GraphErrM.LiftLocalsCorrect using (lift-correct-compile)
open import proof.Correctness.GraphErrM.ExplicateCorrect using (explicate-correct-compile)
open import proof.Correctness.GraphErrM.SelectCorrect using (select-correct-compile)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

{- two sets err together, have the same constants, and have values together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = ((ω ∈ D) ⇔ (ω ∈ E)) × (∀ {B} (c : base-rep B) → ((dconst c ∈ D) ⇔ (dconst c ∈ E))) × (val∈ D ⇔ val∈ E)

≃→Same : ∀ {D E} → D ≃ E → Same D E
≃→Same ⟨ D⊆ , E⊆ ⟩ =
  ⟨ ⟨ D⊆ ω , E⊆ ω ⟩
  , ⟨ (λ c → ⟨ D⊆ (dconst c) , E⊆ (dconst c) ⟩)
    , ⟨ (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ D⊆ d d∈ , d≢ ⟩ ⟩ }) , (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ E⊆ d d∈ , d≢ ⟩ ⟩ }) ⟩ ⟩ ⟩

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

Same-trans : ∀ {D E F} → Same D E → Same E F → Same D F
Same-trans ⟨ e₁ , ⟨ c₁ , v₁ ⟩ ⟩ ⟨ e₂ , ⟨ c₂ , v₂ ⟩ ⟩ =
  ⟨ ⇔-trans e₁ e₂ , ⟨ (λ c → ⇔-trans (c₁ c) (c₂ c)) , ⇔-trans v₁ v₂ ⟩ ⟩

≃-sym′ : ∀ {D E : 𝒫 Value} → D ≃ E → E ≃ D
≃-sym′ ⟨ a , b ⟩ = ⟨ b , a ⟩

{- into Clos4, before globalize -}
compile₄-same : ∀ M → Closed M → Same (⟦ M ⟧ ρ₀) (S4.⟦ compile₄ M ⟧ ρ₀)
compile₄-same M c =
  Same-trans (≃→Same (≃-trans (simplify-correct M c)
               (≃-trans (enclose-correct (simplify M) (simplify-closed M c))
                 (≃-trans (optimize-correct-compile M c)
                   (concretize-correct-closed (optimize-program (enclose (simplify M))))))))
    ⟨ delay-correct-error C₃ , ⟨ delay-correct-const C₃ , delay-correct-val C₃ ⟩ ⟩
  where C₃ = concretize-program (optimize-program (enclose (simplify M)))

compile-same : ∀ M → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧₅
compile-same M c = Same-trans (compile₄-same M c) (≃→Same (globalize-correct-compile M c))

compile-mon-same : ∀ M → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-mon M ⟧₅
compile-mon-same M c = Same-trans (compile-same M c) (≃→Same (≃-sym′ (rco-correct-compile M c)))

compile-imp-same : ∀ M → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-imp M ⟧ᵢ
compile-imp-same M c = Same-trans (compile-mon-same M c) (≃→Same (≃-sym′ (lift-correct-compile M c)))

compile-cfg-same : ∀ M → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-cfg M ⟧ᶜ
compile-cfg-same M c = Same-trans (compile-imp-same M c) (≃→Same (≃-sym′ (explicate-correct-compile M c)))

compile-x86-same : ∀ M → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-x86 M ⟧ₓ
compile-x86-same M c = Same-trans (compile-cfg-same M c) (≃→Same (≃-sym′ (select-correct-compile M c)))
