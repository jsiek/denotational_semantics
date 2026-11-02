{-

  The whole closure-conversion compiler:

    ISWIM --simplify--> ISWIM --capture--> Clos2 --prune--> Clos2 --concretize--> Clos3
          --split--> Clos4 --hoist--> Clos5

  All three correctness proofs (CompilerCorrect, CompilerSim,
  CompilerFuel) are about this compile.

  compile-mon continues with remove complex operands (Clos5 → Clos5),
  into monadic normal form, compile-imp then with lift locals
  (monadic Clos5 → Imp), and compile-cfg then with explicate control
  (Imp → CFG), and compile-x86 then with select instructions
  (CFG → X86).

-}

open import ISWIM.Language.ISWIM using (AST)
import ISWIM.Untyped.Language.Clos4 as L4
import ISWIM.Untyped.Language.Clos5 as L5
open import ISWIM.Compiler.Simplify using (simplify)
open import ISWIM.Untyped.Compiler.Capture using (capture)
open import ISWIM.Untyped.Compiler.Prune using (prune-program)
open import ISWIM.Untyped.Compiler.Concretize using (concretize-program)
open import ISWIM.Untyped.Compiler.Split using (split)
open import ISWIM.Untyped.Compiler.Hoist using (hoist)
open import ISWIM.Untyped.Compiler.RCO using (rco-program; rco-program-mon)
open import ISWIM.Untyped.Compiler.LiftLocals using (lift-program)
import ISWIM.Untyped.Language.Imp as Imp
import ISWIM.Untyped.Language.CFG as CFG
open import ISWIM.Untyped.Compiler.Explicate using (explicate)
import ISWIM.Language.X86 as X86
open import ISWIM.Untyped.Compiler.Select using (select)

module ISWIM.Untyped.Compiler.Pipeline where

compile₄ : AST → L4.AST
compile₄ M = split (concretize-program (prune-program (capture (simplify M))))

compile : AST → L5.Program
compile M = hoist (compile₄ M)

compile-mon : AST → L5.Program
compile-mon M = rco-program (compile M)

compile-imp : AST → Imp.Program
compile-imp M = lift-program (compile-mon M) (rco-program-mon (compile M))

compile-cfg : AST → CFG.Program
compile-cfg M = explicate (compile-imp M)

compile-x86 : AST → X86.Program
compile-x86 M = select (compile-cfg M)
