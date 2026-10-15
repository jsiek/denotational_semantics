{-

  The closure-conversion passes of the pilot, composed: from ISWIMμ to
  Clos4μ,

    ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ --concretize--> Clos3μ
           --delay--> Clos4μ

  as compile₄ of the typed pipeline (Compiler/Pipeline.agda) after cast
  insertion. A program is a closed term of any type.

-}

module Mu.Compiler.Pipeline where

open import Mu.Language.Type using (Type)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.Clos4 as Clos4μ
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Delay using (delay-program)

open import Data.List using ([])

compile₄ : ∀ {A : Type} → ISWIMμ.Tm [] A → Clos4μ.Tm [] A
compile₄ M = delay-program (concretize-program (optimize-program (enclose M)))
