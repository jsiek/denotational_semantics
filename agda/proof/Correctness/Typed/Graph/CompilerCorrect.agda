{-

  The typed compiler (Compiler/Typed/Pipeline.agda) in the plain graph
  model: for a closed ISWIM program, the compiled program, in Clos5ᵀ,
  Monᵀ (by its embedding), Impᵀ, CFGᵀ and X86, produces the same
  constants as the source, and produces something exactly when the
  source does (Same). Simplify (today's proof), cast insertion and every
  later pass but delay preserve the meaning exactly (≃); delay preserves
  and reflects constants and nonemptiness.

-}

module proof.Correctness.Typed.Graph.CompilerCorrect where

open import Framework.Primitives using (base-rep)
open import Framework.Iff using (_⇔_)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ρ₀) renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Simplify using (simplify)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import Compiler.Typed.Cast using (cast-closed)
open import Compiler.Typed.Enclose using (enclose)
open import Compiler.Typed.Optimize using (optimize-program)
open import Compiler.Typed.Concretize using (concretize-program)
open import Compiler.Typed.Pipeline
open import Language.Typed.Mon using (⌜_⌝ₚ)
open import Semantics.Graph.ISWIM using (⟦_⟧)
open import Semantics.Graph.Typed.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Semantics.Graph.Typed.Imp using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Semantics.Graph.Typed.CFG using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Semantics.Graph.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)
open import proof.Correctness.Graph.SimplifyCorrect using (simplify-correct)
open import proof.Correctness.Typed.Graph.CastCorrect using (cast-correct)
open import proof.Correctness.Typed.Graph.EncloseCorrect using (enclose-correct)
open import proof.Correctness.Typed.Graph.OptimizeCorrect using (optimize-correct)
open import proof.Correctness.Typed.Graph.ConcretizeCorrect using (concretize-correct)
open import proof.Correctness.Typed.Graph.DelayCorrect using (delay-correct-const; delay-correct-nonempty)
open import proof.Correctness.Typed.Graph.GlobalizeCorrect using (globalize-correct)
open import proof.Correctness.Typed.Graph.RCOCorrect using (rco-correct)
open import proof.Correctness.Typed.Graph.LiftLocalsCorrect using (lift-locals-correct)
open import proof.Correctness.Typed.Graph.ExplicateCorrect using (explicate-correct)
open import proof.Correctness.Typed.Graph.SelectCorrect using (select-correct)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

{- the same constants, and nonempty together -}
Same : 𝒫 Value → 𝒫 Value → Set
Same D E = (∀ {B} (c : base-rep B) → (dconst c ∈ D) ⇔ (dconst c ∈ E)) × (nonempty D ⇔ nonempty E)

⇔∘ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔∘ ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

{- Same D E, and E ≃ E' -}
then : ∀ {D E E'} → Same D E → E' ≃ E → Same D E'
then ⟨ c , n ⟩ ⟨ E'⊆ , E⊆ ⟩ =
  ⟨ (λ k → ⇔∘ (c k) ⟨ E⊆ _ , E'⊆ _ ⟩)
  , ⇔∘ n ⟨ (λ { ⟨ d , d∈ ⟩ → ⟨ d , E⊆ d d∈ ⟩ }) , (λ { ⟨ d , d∈ ⟩ → ⟨ d , E'⊆ d d∈ ⟩ }) ⟩ ⟩

compile-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧₅
compile-same M c with ≃-trans (simplify-correct M) (≃-trans (cast-correct (simplify M) (simplify-closed M c))
                       (≃-trans (enclose-correct M₁) (≃-trans (optimize-correct (enclose M₁)) (concretize-correct M₂))))
  where
  M₁ = cast-closed (simplify M)
  M₂ = optimize-program (enclose M₁)
... | ⟨ D⊆ , E⊆ ⟩ =
  then ⟨ (λ k → ⇔∘ ⟨ D⊆ _ , E⊆ _ ⟩ (delay-correct-const M₃ k))
       , ⇔∘ ⟨ (λ { ⟨ d , d∈ ⟩ → ⟨ d , D⊆ d d∈ ⟩ }) , (λ { ⟨ d , d∈ ⟩ → ⟨ d , E⊆ d d∈ ⟩ }) ⟩ (delay-correct-nonempty M₃) ⟩
       (≃-sym (globalize-correct (compile₄ M)))
  where M₃ = concretize-program (optimize-program (enclose (cast-closed (simplify M))))

compile-mon-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅
compile-mon-same M c = then (compile-same M c) (rco-correct (compile M))

compile-imp-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-imp M ⟧ᵢ
compile-imp-same M c = then (compile-mon-same M c) (lift-locals-correct (compile-mon M))

compile-cfg-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-cfg M ⟧ᶜ
compile-cfg-same M c = then (compile-imp-same M c) (explicate-correct (compile-imp M))

compile-x86-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-x86 M ⟧ₓ
compile-x86-same M c = then (compile-cfg-same M c) (select-correct (compile-cfg M))
