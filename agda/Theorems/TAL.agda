{-

  A pilot: a typed assembly language, X86ᵀ (Language/Typed/X86.agda), as
  the target of the compiler, in two columns. The public statements; the
  proofs are in proof/Correctness/CEK/{SelectTALSim,PipelineTALSim}.agda,
  proof/Correctness/GraphErr/{SelectTALCorrect,CompilerTALCorrect}.agda
  and proof/Compiler/SelectTALErase.agda. Not part of the main theorems
  (Theorems/Simulation.agda, Theorems/GraphErrors.agda), whose compiler
  ends at untyped X86.

    ISWIM --simplify--> … --explicate control--> CFGᵀ --typed select--> X86ᵀ

  The pipeline ends at X86ᵀ (Compiler/PipelineTAL.agda, compile-tal): there
  is no erasure pass. X86ᵀ's only trapped error is project's check
  (chk); its machine (Semantics/CEK/Typed/X86.agda) and its semantics in
  the graph model with errors (Semantics/GraphErr/Typed/X86.agda) have
  no other.

  * CEK machine + simulation: select, and the compiler, are Equivalent.
  * Graph model with errors: select is an equation (≃), where select
    into untyped X86 is only Same; the compiler is Same (because of
    delay).
  * Without the types, typed select emits the instructions of select
    into X86 (Compiler/Select.agda): erase is not a pass, only the
    statement that the two emit the same code.

-}

module Theorems.TAL where

open import Semantics.CEK.Smallstep using (Equivalent)
open import Framework.GraphModel.SetsAsPredicates using (_≃_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Language.ISWIM as ISWIM
import Language.Typed.CFG as CFGᵀ
open import Compiler.EncloseScope using (Closed)
import Compiler.Select as Select
open import Compiler.SelectTAL using (select)
open import Compiler.PipelineTAL using (compile-tal)
open import Language.Typed.X86Erase using (erase)

import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.CFG as CFGᵀₘ
import Semantics.CEK.Typed.X86 as X86ᵀₘ
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Typed.CFG using (⟦_⟧ᶜ)
open import Semantics.GraphErr.Typed.X86 using (⟦_⟧ₜ)
open import Theorems.GraphErrors using (Same; ρ₀)

import proof.Correctness.CEK.SelectTALSim as SelectTALSim
import proof.Correctness.CEK.PipelineTALSim as PipelineTALSim
import proof.Correctness.GraphErr.SelectTALCorrect as SelectTALCorrect
import proof.Correctness.GraphErr.CompilerTALCorrect as CompilerTALCorrect
import proof.Compiler.SelectTALErase as SelectTALErase

{- CEK machine + simulation ---------------------------------------------------}

select-correct : ∀ (P : CFGᵀ.Program) → Equivalent (CFGᵀₘ.sem P) (X86ᵀₘ.sem (select P))
select-correct = SelectTALSim.select-correct

compile-tal-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (X86ᵀₘ.sem (compile-tal M))
compile-tal-correct = PipelineTALSim.compile-tal-correct

{- Graph model with errors -------------------------------------------------------}

select-correct-graph : ∀ (P : CFGᵀ.Program) → ⟦ select P ⟧ₜ ≃ ⟦ P ⟧ᶜ
select-correct-graph = SelectTALCorrect.select-correct

compile-tal-same : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile-tal M ⟧ₜ
compile-tal-same = CompilerTALCorrect.compile-tal-same

{- The same instructions as select into X86 ------------------------------------}

select-erase : ∀ (P : CFGᵀ.Program) → erase (select P) ≡ Select.select P
select-erase = SelectTALErase.select-erase
