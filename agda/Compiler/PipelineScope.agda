{-

  Well-scoped Clos5 programs (Scoped), the precondition of the
  operational proofs of remove complex operands: main is closed (WS 0)
  and the code of each global definition uses only its two parameters
  (WS 2, Framework/Syntax/Scope.agda). (That the compiler produces them
  from closed ISWIM programs, compile-scoped, is in
  proof/Compiler/PipelineScope.agda.)

-}

module Compiler.PipelineScope where

import Language.Clos5 as C5
import Framework.Syntax.Scope

open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_)

module W5 = Framework.Syntax.Scope C5.Op C5.sig

{- Well-scoped Clos5 programs: main in the empty environment, each definition
   in its two parameters -}
Scoped : C5.Program → Set
Scoped (C5.program ds M) = All (W5.WS 2) ds × W5.WS 0 M
