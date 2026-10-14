{-

  Instruction selection for the typed compiler in the graph model with
  errors: a CFGᵀ program and its X86 code have the same errors, the
  same constants and values exactly when one does (Same), and so does
  the whole compiler to X86.

  Not ≃, as in the graph model without errors: the typed semantics
  checks kinds only at project, so the code of CFGᵀ has no entries at
  inputs of the wrong kind, but X86 checks every operation and its code
  has error entries there. The proof goes through CFGᵀ with the X86
  checks (SelectCheck.agda), equal to X86 (SelectX86.agda) and related
  to CFGᵀ in both directions (SelectReflect.agda, SelectPreserve.agda);
  the relation is the identity on the errors, constants and values.

-}

module proof.Correctness.GraphErr.SelectCorrect where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import proof.Framework.GraphModel.ErrorMonad using (Lifted)
open import Framework.Iff using (_⇔_)
open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Pipeline using (compile-cfg; compile-x86)
open import Compiler.Select using (select)
import Language.Typed.CFG as C
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Typed.CFG using (⟦_⟧ᶜ)
import Semantics.GraphErr.X86 as X
open import proof.Correctness.GraphErr.CompilerCorrect using (Same; ⇔∘; ≃-Same; compile-cfg-same)
open import proof.Correctness.GraphErr.SelectRel using (_⊑_; ⊑-val)
open import proof.Correctness.GraphErr.SelectX86 using (select-check)
open import proof.Correctness.GraphErr.SelectReflect using (reflect)
open import proof.Correctness.GraphErr.SelectPreserve using (preserve)

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Level using (lower)

{- related both ways, two sets have the same errors, constants and values -}
⊑-Same : ∀ {D E} → Lifted _⊑_ D E → Lifted _⊑_ E D → Same D E
⊑-Same r r' =
  ⟨ ⟨ (λ ω∈ → lower (r ω ω∈)) , (λ ω∈ → lower (r' ω ω∈)) ⟩
  , ⟨ (λ c → ⟨ (λ c∈ → lower (r (dconst c) c∈)) , (λ c∈ → lower (r' (dconst c) c∈)) ⟩)
    , ⟨ (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⊑-val d d≢ (r d d∈) })
      , (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⊑-val d d≢ (r' d d∈) }) ⟩ ⟩ ⟩

select-correct : ∀ (P : C.Program) → Same ⟦ P ⟧ᶜ X.⟦ select P ⟧ₚ
select-correct P = ≃-Same (⊑-Same (preserve P) (reflect P)) (≃-sym (select-check P))

Same-trans : ∀ {D E F} → Same D E → Same E F → Same D F
Same-trans ⟨ e , ⟨ c , v ⟩ ⟩ ⟨ e' , ⟨ c' , v' ⟩ ⟩ = ⟨ ⇔∘ e e' , ⟨ (λ k → ⇔∘ (c k) (c' k)) , ⇔∘ v v' ⟩ ⟩

compile-x86-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) X.⟦ compile-x86 M ⟧ₚ
compile-x86-same M c = Same-trans (compile-cfg-same M c) (select-correct (compile-cfg M))
