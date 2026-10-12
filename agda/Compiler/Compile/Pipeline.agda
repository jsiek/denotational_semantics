{-

  The whole closure-conversion compiler:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  All three correctness proofs (CompilerCorrect, CompilerSim,
  CompilerFuel) are about this compile.

  compile-mon continues with remove complex operands (Clos5 → Clos5),
  into monadic normal form, and compile-imp then with lift locals
  (monadic Clos5 → Imp).

-}

open import Compiler.Lang.ISWIM using (AST)
import Compiler.Lang.Clos4 as L4
import Compiler.Lang.Clos5 as L5
open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Compile.Optimize using (optimize-program)
open import Compiler.Compile.Concretize using (concretize-program)
open import Compiler.Compile.Delay using (delay)
open import Compiler.Compile.Globalize using (globalize)
open import Compiler.Compile.RCO using (rco-program; rco-program-mon)
open import Compiler.Compile.LiftLocals using (lift-program)
import Compiler.Lang.Imp as Imp

module Compiler.Compile.Pipeline where

compile₄ : AST → L4.AST
compile₄ M = delay (concretize-program (optimize-program (enclose M)))

compile : AST → L5.Program
compile M = globalize (compile₄ M)

compile-mon : AST → L5.Program
compile-mon M = rco-program (compile M)

compile-imp : AST → Imp.Program
compile-imp M = lift-program (compile-mon M) (rco-program-mon (compile M))
