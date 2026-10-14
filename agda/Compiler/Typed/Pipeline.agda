{-

  The typed pilot's compiler, from ISWIM to Clos4ᵀ:

    ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ --optimize--> Clos2ᵀ
          --concretize--> Clos3ᵀ --delay--> Clos4ᵀ

-}

module Compiler.Typed.Pipeline where

open import Language.ISWIM using (AST; Op; sig)
open import Framework.Syntax.Scope Op sig using (WS)
open import Language.Typed.Type using (Any)
import Language.Typed.Clos4 as Clos4ᵀ
open import Compiler.Typed.Cast using (cast-program)
open import Compiler.Typed.Enclose using (enclose)
open import Compiler.Typed.Optimize using (optimize-program)
open import Compiler.Typed.Concretize using (concretize-program)
open import Compiler.Typed.Delay using (delay-program)

open import Data.List using ([])

compileᵀ : (M : AST) → WS 0 M → Clos4ᵀ.Tm [] Any
compileᵀ M w = delay-program (concretize-program (optimize-program (enclose (cast-program M w))))
