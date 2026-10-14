{-

  The typed compiler, from untyped ISWIM to the typed assembly language
  X86ᵀ:

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ
          --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ
          --globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

  compile₄ goes to Clos4ᵀ, compile to Clos5ᵀ, and compile-mon,
  compile-imp, compile-cfg and compile-x86 continue, as the untyped
  compositions of the preserved untyped pipeline do
  (Untyped/Compiler/Pipeline.agda; compile-x86 ends at X86ᵀ, where the
  untyped one ends at X86). Simplify stays on untyped ISWIM; cast
  insertion (cast-closed) needs a closed program.

-}

module Compiler.Pipeline where

open import Language.ISWIM using (AST)
open import Language.Typed.Type using (Any)
import Language.Typed.Clos4 as Clos4ᵀ
import Language.Typed.Clos5 as Clos5ᵀ
import Language.Typed.Mon as Monᵀ
import Language.Typed.Imp as Impᵀ
import Language.Typed.CFG as CFGᵀ
import Language.Typed.X86 as X86ᵀ
open import Compiler.Simplify using (simplify)
open import Compiler.Cast using (cast-closed)
open import Compiler.Enclose using (enclose)
open import Compiler.Optimize using (optimize-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Delay using (delay-program)
open import Compiler.Globalize using (globalize)
open import Compiler.RCO using (rco-program)
open import Compiler.LiftLocals using (lift-program)
open import Compiler.Explicate using (explicate)
open import Compiler.Select using (select)

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

compile-x86 : AST → X86ᵀ.Program
compile-x86 M = select (compile-cfg M)
