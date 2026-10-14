{-

  The typed pilot's compiler (Compiler/Typed/Pipeline.agda) in the graph
  model with errors: for a well-scoped closed ISWIM program, the Clos4ᵀ
  program errs exactly when the source does, produces the same constants,
  and produces a value exactly when the source does (Same, as in
  proof/Correctness/GraphErr/CompilerCorrect.agda, repeated here). Cast
  insertion, enclose, optimize and concretize preserve the meaning exactly (≃);
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
open import Compiler.Typed.Optimize using (optimize-program)
open import Compiler.Typed.Concretize using (concretize-program)
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
import Semantics.GraphErr.Typed.Clos3
import Semantics.GraphErr.Typed.ISWIM
open import proof.Compiler.SimplifyScope using (closed-ws)
import Semantics.GraphErr.Typed.Clos4 as S4
open import proof.Correctness.Typed.GraphErr.CastCorrect using (cast-correct)
open import proof.Correctness.Typed.GraphErr.EncloseCorrect using (enclose-correct)
open import proof.Correctness.Typed.GraphErr.OptimizeCorrect using (optimize-correct)
open import proof.Correctness.Typed.GraphErr.ConcretizeCorrect using (concretize-correct)
open import proof.Correctness.Typed.GraphErr.DelayCorrect
  using (delay-correct-error; delay-correct-const; delay-correct-val)

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (sym; cong)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Simplify using (simplify)
open import Compiler.Typed.Cast using (cast-closed)
open import Compiler.Typed.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg)
open import proof.Compiler.Typed.CastScope using (simplify-ws; cast-closed-≡)
open import proof.Correctness.GraphErr.SimplifyCorrect using (simplify-correct)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧₅)
open import Semantics.GraphErr.Typed.Imp using (⟦_⟧ᵢ)
open import Semantics.GraphErr.Typed.CFG using (⟦_⟧ᶜ)
open import Language.Typed.Mon using (⌜_⌝ₚ)
open import proof.Correctness.Typed.GraphErr.GlobalizeCorrect using (globalize-correct)
open import proof.Correctness.Typed.GraphErr.RCOCorrect using (rco-correct)
open import proof.Correctness.Typed.GraphErr.LiftLocalsCorrect using (lift-locals-correct)
open import proof.Correctness.Typed.GraphErr.ExplicateCorrect using (explicate-correct)

Same : 𝒫 Value → 𝒫 Value → Set
Same D E = ((ω ∈ D) ⇔ (ω ∈ E)) × (∀ {B} (c : base-rep B) → ((dconst c ∈ D) ⇔ (dconst c ∈ E))) × (val∈ D ⇔ val∈ E)

⇔∘ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔∘ ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

compile-same : ∀ (M : AST) (w : WS 0 M) → Same (⟦ M ⟧ ρ₀) (S4.⟦ compileᵀ M w ⟧ ρ₀)
compile-same M w = go (≃-trans (cast-correct M w) (≃-trans (enclose-correct M₁) (≃-trans (optimize-correct (enclose M₁)) (concretize-correct M₂))))
  where
  M₁ = cast-program M w
  M₂ = optimize-program (enclose M₁)
  M₃ = concretize-program M₂
  go : ⟦ M ⟧ ρ₀ ≃ Semantics.GraphErr.Typed.Clos3.⟦ M₃ ⟧ ρ₀ → Same (⟦ M ⟧ ρ₀) (S4.⟦ compileᵀ M w ⟧ ρ₀)
  go ⟨ D⊆ , E⊆ ⟩ =
    ⟨ ⇔∘ ⟨ D⊆ ω , E⊆ ω ⟩ (delay-correct-error M₃)
    , ⟨ (λ c → ⇔∘ ⟨ D⊆ (dconst c) , E⊆ (dconst c) ⟩ (delay-correct-const M₃ c))
      , ⇔∘ ⟨ (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ D⊆ d d∈ , d≢ ⟩ ⟩ })
           , (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ E⊆ d d∈ , d≢ ⟩ ⟩ }) ⟩ (delay-correct-val M₃) ⟩ ⟩

{- The typed compiler from untyped ISWIM (Compiler/Typed/Pipeline.agda) -----------}

≃-Same : ∀ {D E E'} → Same D E → E ≃ E' → Same D E'
≃-Same ⟨ e , ⟨ c , v ⟩ ⟩ ⟨ E⊆ , E⊇ ⟩ =
  ⟨ ⇔∘ e ⟨ E⊆ ω , E⊇ ω ⟩
  , ⟨ (λ k → ⇔∘ (c k) ⟨ E⊆ (dconst k) , E⊇ (dconst k) ⟩)
    , ⇔∘ v ⟨ (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ E⊆ d d∈ , d≢ ⟩ ⟩ }) , (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ E⊇ d d∈ , d≢ ⟩ ⟩ }) ⟩ ⟩ ⟩

compile₄-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) (S4.⟦ compile₄ M ⟧ ρ₀)
compile₄-same M c rewrite cast-closed-≡ (simplify M) (simplify-ws M c) =
  ≃-Same′ (simplify-correct M c) (compile-same (simplify M) (simplify-ws M c))
  where
  ≃-Same′ : ∀ {D D' E} → D ≃ D' → Same D' E → Same D E
  ≃-Same′ ⟨ D⊆ , D⊇ ⟩ ⟨ e , ⟨ k , v ⟩ ⟩ =
    ⟨ ⇔∘ ⟨ D⊆ ω , D⊇ ω ⟩ e
    , ⟨ (λ b → ⇔∘ ⟨ D⊆ (dconst b) , D⊇ (dconst b) ⟩ (k b))
      , ⇔∘ ⟨ (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ D⊆ d d∈ , d≢ ⟩ ⟩ }) , (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ D⊇ d d∈ , d≢ ⟩ ⟩ }) ⟩ v ⟩ ⟩

compile-same₅ : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧₅
compile-same₅ M c = ≃-Same (compile₄-same M c) (globalize-correct (compile₄ M))

compile-mon-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅
compile-mon-same M c = ≃-Same (compile-same₅ M c) (≃-sym (rco-correct (compile M)))

compile-imp-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-imp M ⟧ᵢ
compile-imp-same M c = ≃-Same (compile-mon-same M c) (≃-sym (lift-locals-correct (compile-mon M)))

compile-cfg-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-cfg M ⟧ᶜ
compile-cfg-same M c = ≃-Same (compile-imp-same M c) (≃-sym (explicate-correct (compile-imp M)))

{- cast insertion on closed programs (cast-closed) -}
cast-correct-closed : ∀ (M : AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ Semantics.GraphErr.Typed.ISWIM.⟦ cast-closed M ⟧ ρ₀
cast-correct-closed M c rewrite cast-closed-≡ M (closed-ws {M} c) = cast-correct M (closed-ws {M} c)
