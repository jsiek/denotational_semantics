{-

  The whole closure-conversion compiler:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  All three correctness proofs (CompilerCorrect, CompilerSim,
  CompilerFuel) are about this compile.

-}

open import Compiler.Lang.ISWIM using (AST)
import Compiler.Lang.Clos4 as L4
import Compiler.Lang.Clos5 as L5
open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Compile.Optimize using (optimize-program)
open import Compiler.Compile.Concretize using (concretize-program)
open import Compiler.Compile.Delay using (delay)
open import Compiler.Compile.Globalize using (globalize)

module Compiler.Compile.Pipeline where

compile₄ : AST → L4.AST
compile₄ M = delay (concretize-program (optimize-program (enclose M)))

compile : AST → L5.Program
compile M = globalize (compile₄ M)
