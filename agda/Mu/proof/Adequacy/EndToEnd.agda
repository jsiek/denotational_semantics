{-

  The ISWIMμ compiler in the graph model, observed through the clocked
  interpreters: for a closed ISWIMμ program M,

    ISWIMμ interpreter  ⇔  ⟦ M ⟧ ρ₀                (Adequacy/ISWIM.agda)
                        ⇔  ⟦ compile-x86 M ⟧ₜ       (Correctness/Graph/CompilerCorrect.agda)
                        ⇔  X86μ interpreter         (Adequacy/X86.agda)

  for constants, and for divergence through the emptiness of the
  denotations. Since both adequacy theorems give divergence directly
  (soundness shows that neither interpreter errs), no no-error lemma is
  needed. So the graph model states, for a main of type Int, the
  theorem of the interpreter column
  (Correctness/Interp/CompilerFuel.agda: compile-x86-const and
  compile-x86-diverges): the two interpreters stop with the same
  constant, or both diverge.

-}

module Mu.proof.Adequacy.EndToEnd where

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (ρ₀)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Semantics.Graph.ISWIM using (⟦_⟧)
open import Mu.Semantics.Graph.X86 using (⟦_⟧ₜ)
open import Mu.Compiler.Pipeline using (compile-x86)
open import Semantics.Observation using (o-const; _⇔_)
open import proof.Semantics.Interp.Clock using (Terminates; Diverges)
import Mu.Semantics.Interp.ISWIM as I
import Mu.Semantics.Interp.X86 as X
import Mu.proof.Adequacy.ISWIM as AI
import Mu.proof.Adequacy.X86 as AX
open import Mu.proof.Correctness.Graph.CompilerCorrect using (compile-x86-same)

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

private
  _∘⇔_ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
  (f , g) ∘⇔ (h , k) = (λ a → h (f a)) , (λ c → g (k c))

  ⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
  ⇔-sym (f , g) = g , f

compile-x86-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (I.sem M) (o-const Int k) ⇔ Terminates (X.sem (compile-x86 M)) (o-const Int k)
compile-x86-const M k = ⇔-sym (AI.const-iff M) ∘⇔ (proj₁ (compile-x86-same M) k ∘⇔ AX.x86-const-iff M)

compile-x86-diverges : ∀ (M : Tm [] (base Int)) → Diverges (I.sem M) ⇔ Diverges (X.sem (compile-x86 M))
compile-x86-diverges M = AI.diverges-iff M ∘⇔ (empty ∘⇔ ⇔-sym (AX.x86-diverges-iff M))
  where
  S = proj₂ (compile-x86-same M)
  empty : (¬ nonempty (⟦ M ⟧ ρ₀)) ⇔ (¬ nonempty ⟦ compile-x86 M ⟧ₜ)
  empty = (λ ne n → ne (proj₂ S n)) , (λ ne n → ne (proj₁ S n))
