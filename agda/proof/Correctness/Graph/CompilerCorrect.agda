{-

  Correctness of the whole closure-conversion compiler:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  For a closed ISWIM program, the compiled Clos5 program produces the same
  constants as the original, and produces something exactly when the
  original does.

  Every pass but delay preserves denotations exactly (≃); delay preserves
  and reflects constants and nonemptiness, which is what Same records.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import Language.ISWIM
open import proof.Semantics.Graph.ISWIM
open import Semantics.Graph.Clos5Iswim using (⟦_⟧ₚ)
open import Compiler.Enclose using (enclose)
open import Compiler.Optimize using (optimize-program)
open import Compiler.Concretize using (concretize-program)
open import proof.Correctness.Graph.DelayFiniteCommon using (ρ₀)
open import proof.Correctness.Graph.EncloseCorrect using (enclose-correct-closed)
open import proof.Correctness.Graph.OptimizeCorrect using (optimize-correct-closed)
open import proof.Correctness.Graph.ConcretizeCorrect using (concretize-correct-closed)
open import proof.Correctness.Graph.DelayPreserve
  using (delay-correct-const; delay-correct-nonempty)
open import proof.Correctness.Graph.GlobalizeCorrect using (globalize-correct)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

module proof.Correctness.Graph.CompilerCorrect where

open import Compiler.Pipeline using (compile; compile₄) public

{- D and D' produce the same constants, and one is nonempty iff the other is -}
infix 4 _⇔_
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

Same : 𝒫 Value → 𝒫 Value → Set
Same D D' = (∀ {B} (c : base-rep B) → const c ∈ D ⇔ const c ∈ D') × (nonempty D ⇔ nonempty D')

⇔-trans : ∀ {A B C} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

Same-trans : ∀ {D D' D''} → Same D D' → Same D' D'' → Same D D''
Same-trans ⟨ c₁ , n₁ ⟩ ⟨ c₂ , n₂ ⟩ = ⟨ (λ c → ⇔-trans (c₁ c) (c₂ c)) , ⇔-trans n₁ n₂ ⟩

≃→Same : ∀ {D D'} → D ≃ D' → Same D D'
≃→Same ⟨ D⊆ , D⊇ ⟩ = ⟨ (λ c → ⟨ D⊆ _ , D⊇ _ ⟩) , ⟨ ne D⊆ , ne D⊇ ⟩ ⟩
  where ne = λ {A B : 𝒫 Value} (A⊆ : A ⊆ B) (n : nonempty A) → ⟨ proj₁ n , A⊆ _ (proj₂ n) ⟩

compile-same : ∀ (M : AST) → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧ₚ
compile-same M =
  Same-trans (≃→Same (≃-trans (enclose-correct-closed M)
                     (≃-trans (optimize-correct-closed M₂) (concretize-correct-closed M₂'))))
  (Same-trans ⟨ delay-correct-const M₃ , delay-correct-nonempty M₃ ⟩
              (≃→Same (globalize-correct (compile₄ M))))
  where
  M₂ = enclose M
  M₂' = optimize-program M₂
  M₃ = concretize-program M₂'

compile-correct-const : ∀ (M : AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧ₚ)
  × (const c ∈ ⟦ compile M ⟧ₚ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M = proj₁ (compile-same M)

compile-correct-nonempty : ∀ (M : AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧ₚ)
  × (nonempty ⟦ compile M ⟧ₚ → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M = proj₂ (compile-same M)
