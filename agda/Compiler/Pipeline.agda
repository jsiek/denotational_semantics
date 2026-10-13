{-

  The whole closure-conversion compiler:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  All three correctness proofs (CompilerCorrect, CompilerSim,
  CompilerFuel) are about this compile.

  compile-mon continues with remove complex operands (Clos5 → Clos5),
  into monadic normal form, compile-imp then with lift locals
  (monadic Clos5 → Imp), and compile-cfg then with explicate control
  (Imp → CFG), and compile-x86 then with select instructions
  (CFG → X86).

-}

open import Language.ISWIM using (AST)
import Language.Clos4 as L4
import Language.Clos5 as L5
open import Compiler.Enclose using (enclose)
open import Compiler.Optimize using (optimize-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Delay using (delay)
open import Compiler.Globalize using (globalize)
open import Compiler.RCO using (rco-program; rco-program-mon)
open import Compiler.LiftLocals using (lift-program)
import Language.Imp as Imp
import Language.CFG as CFG
open import Compiler.Explicate using (explicate)
import Language.X86 as X86
open import Compiler.Select using (select)

module Compiler.Pipeline where

compile₄ : AST → L4.AST
compile₄ M = delay (concretize-program (optimize-program (enclose M)))

compile : AST → L5.Program
compile M = globalize (compile₄ M)

compile-mon : AST → L5.Program
compile-mon M = rco-program (compile M)

compile-imp : AST → Imp.Program
compile-imp M = lift-program (compile-mon M) (rco-program-mon (compile M))

compile-cfg : AST → CFG.Program
compile-cfg M = explicate (compile-imp M)

compile-x86 : AST → X86.Program
compile-x86 M = select (compile-cfg M)
