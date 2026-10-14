{-

  The compiler to X86ᵀ (Compiler/SelectTAL.agda, compile-tal), a pilot
  (Theorems/TAL.agda), is correct on the machines, for closed programs:
  the compiler to CFGᵀ (PipelineSim.agda), then select into X86ᵀ
  (SelectTALSim.agda).

-}

module proof.Correctness.CEK.PipelineTALSim where

open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.PipelineTAL using (compile-tal)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import proof.Correctness.CEK.PipelineSim using (compile-cfg-correct)
open import proof.Correctness.CEK.SelectTALSim using (select-correct)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.X86 as X

compile-tal-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (X.sem (compile-tal M))
compile-tal-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct _)
