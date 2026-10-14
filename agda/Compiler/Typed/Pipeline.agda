{-

  The typed compiler, from untyped ISWIM to X86:

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86

  compile₄ goes to Clos4ᵀ, compile to Clos5ᵀ, and compile-mon,
  compile-imp, compile-cfg and compile-x86 continue, as the untyped
  compositions of the preserved untyped pipeline do
  (Untyped/Compiler/Pipeline.agda). Simplify stays on untyped
  ISWIM; cast insertion (cast-closed) needs a closed program.

-}

module Compiler.Typed.Pipeline where

open import Language.ISWIM using (AST)
open import Language.Typed.Type using (Any)
import Language.Typed.Clos4 as Clos4ᵀ
import Language.Typed.Clos5 as Clos5ᵀ
import Language.Typed.Mon as Monᵀ
import Language.Typed.Imp as Impᵀ
import Language.Typed.CFG as CFGᵀ
import Language.X86 as X86
open import Compiler.Simplify using (simplify)
open import Compiler.Typed.Cast using (cast-closed)
open import Compiler.Typed.Enclose using (enclose)
open import Compiler.Typed.Optimize using (optimize-program)
open import Compiler.Typed.Concretize using (concretize-program)
open import Compiler.Typed.Delay using (delay-program)
open import Compiler.Typed.Globalize using (globalize)
open import Compiler.Typed.RCO using (rco-program)
open import Compiler.Typed.LiftLocals using (lift-program)
open import Compiler.Typed.Explicate using (explicate)
open import Compiler.Typed.Select using (select)

open import Data.List using ([])

compile₄ : AST → Clos4ᵀ.Tm [] Any
compile₄ M = delay-program (concretize-program (optimize-program (enclose (cast-closed (simplify M)))))

compile : AST → Clos5ᵀ.Program
compile M = globalize (compile₄ M)

compile-mon : AST → Monᵀ.Program
compile-mon M = rco-program (compile M)

compile-imp : AST → Impᵀ.Program
compile-imp M = lift-program (compile-mon M)

compile-cfg : AST → CFGᵀ.Program
compile-cfg M = explicate (compile-imp M)

compile-x86 : AST → X86.Program
compile-x86 M = select (compile-cfg M)
