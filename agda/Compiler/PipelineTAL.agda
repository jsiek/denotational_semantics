{-

  The compiler to X86ᵀ, a pilot (Theorems/TAL.agda): the compiler to
  CFGᵀ (Compiler/Pipeline.agda), then typed select instructions
  (Compiler/SelectTAL.agda). It ends at X86ᵀ: there is no erasure pass.

-}

module Compiler.PipelineTAL where

open import Language.ISWIM using (AST)
open import Language.Typed.X86 using (Program)
open import Compiler.Pipeline using (compile-cfg)
open import Compiler.SelectTAL using (select)

compile-tal : AST → Program
compile-tal M = select (compile-cfg M)
