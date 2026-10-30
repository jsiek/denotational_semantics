{-

  The passes of the ISWIMμ compiler, composed: from ISWIMμ to X86μ,

    ISWIMμ --simplify--> ISWIMμ --capture--> Closμ --prune--> Closμ
           --concretize--> EnvClosμ --delay--> PairClosμ --globalize--> GlobalFunμ --rco--> Monμ
           --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  as the typed pipeline's (Compiler/Pipeline.agda), without cast insertion:
  compile is the whole compiler, into X86μ; its prefixes compile-to-PairClos,
  compile-to-GlobalFun, compile-to-Mon, compile-to-Imp and compile-to-CFG
  stop at those languages. A program is a closed term of any type, and
  each compiled program has its type.

-}

module Mu.Compiler.Pipeline where

open import Mu.Language.Type using (Type)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.PairClos as PairClosμ
import Mu.Language.GlobalFun as GlobalFunμ
import Mu.Language.Mon as Monμ
import Mu.Language.Imp as Impμ
import Mu.Language.CFG as CFGμ
import Mu.Language.X86 as X86μ
open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Capture using (capture)
open import Mu.Compiler.Prune using (prune-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Delay using (delay-program)
open import Mu.Compiler.Globalize using (globalize)
open import Mu.Compiler.RCO using (rco-program)
open import Mu.Compiler.LiftLocals using (lift-program)
open import Mu.Compiler.Explicate using (explicate)
open import Mu.Compiler.Select using (select)

open import Data.List using ([])

compile-to-PairClos : ∀ {A : Type} → ISWIMμ.Tm [] A → PairClosμ.Tm [] A
compile-to-PairClos M = delay-program (concretize-program (prune-program (capture (simplify M))))

compile-to-GlobalFun : ∀ {A : Type} → ISWIMμ.Tm [] A → GlobalFunμ.Program A
compile-to-GlobalFun M = globalize (compile-to-PairClos M)

compile-to-Mon : ∀ {A : Type} → ISWIMμ.Tm [] A → Monμ.Program A
compile-to-Mon M = rco-program (compile-to-GlobalFun M)

compile-to-Imp : ∀ {A : Type} → ISWIMμ.Tm [] A → Impμ.Program A
compile-to-Imp M = lift-program (compile-to-Mon M)

compile-to-CFG : ∀ {A : Type} → ISWIMμ.Tm [] A → CFGμ.Program A
compile-to-CFG M = explicate (compile-to-Imp M)

compile : ∀ {A : Type} → ISWIMμ.Tm [] A → X86μ.Program A
compile M = select (compile-to-CFG M)
