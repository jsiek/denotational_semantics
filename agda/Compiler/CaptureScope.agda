{-

  Closed ISWIM programs, the precondition of the operational proofs of
  capture and of the whole compiler: those whose bound is 0, that is,
  that use no variables (bound, Framework/Syntax/Uses.agda). (That
  capture produces well-scoped Clos2 programs from them is in
  Untyped/proof/Compiler/CaptureScope.agda.)

-}

module Compiler.CaptureScope where

import Language.ISWIM as I
open import Framework.Syntax.Uses I.Op I.sig using (bound)

open import Relation.Binary.PropositionalEquality using (_≡_)

{- a closed program uses no variables -}
Closed : I.AST → Set
Closed M = bound M ≡ 0
