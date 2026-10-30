{-

  The whole closure-conversion compiler:

    ISWIM --simplify--> ISWIM --capture--> Clos2 --prune--> Clos2 --concretize--> Clos3
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
import Untyped.Language.Clos4 as L4
import Untyped.Language.Clos5 as L5
open import Compiler.Simplify using (simplify)
open import Untyped.Compiler.Capture using (capture)
open import Untyped.Compiler.Prune using (prune-program)
open import Untyped.Compiler.Concretize using (concretize-program)
open import Untyped.Compiler.Delay using (delay)
open import Untyped.Compiler.Globalize using (globalize)
open import Untyped.Compiler.RCO using (rco-program; rco-program-mon)
open import Untyped.Compiler.LiftLocals using (lift-program)
import Untyped.Language.Imp as Imp
import Untyped.Language.CFG as CFG
open import Untyped.Compiler.Explicate using (explicate)
import Language.X86 as X86
open import Untyped.Compiler.Select using (select)

module Untyped.Compiler.Pipeline where

compile₄ : AST → L4.AST
compile₄ M = delay (concretize-program (prune-program (capture (simplify M))))

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
