{-

  The compiler to X86ᵀ (Compiler/SelectTAL.agda, compile-tal), a pilot
  (Theorems/TAL.agda), in the graph model with errors, for closed
  programs: the X86ᵀ program errs, has the same constants and has a
  value exactly when the source does (Same, as for the compiler to CFGᵀ,
  because of delay), since select into X86ᵀ is ≃ (SelectTALCorrect.agda).

-}

module proof.Correctness.GraphErr.CompilerTALCorrect where

open import proof.Framework.GraphModel.SetsAsPredicates using (≃-sym)
open import proof.Framework.GraphModel.Domain using (ρ₀)
open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Pipeline using (compile-cfg)
open import Compiler.PipelineTAL using (compile-tal)
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Typed.X86 using (⟦_⟧ₜ)
open import proof.Correctness.GraphErr.CompilerCorrect using (Same; ≃-Same; compile-cfg-same)
open import proof.Correctness.GraphErr.SelectTALCorrect using (select-correct)

compile-tal-same : ∀ (M : AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-tal M ⟧ₜ
compile-tal-same M c = ≃-Same (compile-cfg-same M c) (≃-sym (select-correct (compile-cfg M)))
