{-

  Assurance, not a pass of the compiler and not in the comparison: the
  compiler ends at the typed assembly language X86ᵀ
  (Language/Typed/X86.agda), and without its types the code it emits is
  that of select into untyped X86, the target of the typed pipeline
  before X86ᵀ (Compiler/SelectX86.agda). The erasure
  (Language/Typed/X86Erase.agda) drops the types, the proofs about
  registers and frame bounds and the coercion ↑, and expands chk t x, d
  to X86's test of t on x and the move. The proof is in
  proof/Compiler/SelectErase.agda.

-}

module Theorems.Erasure where

open import Relation.Binary.PropositionalEquality using (_≡_)

import Language.Typed.CFG as CFGᵀ
open import Compiler.Select using (select)
import Compiler.SelectX86 as SelectX86
open import Language.Typed.X86Erase using (erase)

import proof.Compiler.SelectErase as SelectErase

{- select emits the instructions of select into untyped X86 -}
select-erase : ∀ (P : CFGᵀ.Program) → erase (select P) ≡ SelectX86.select P
select-erase = SelectErase.select-erase
