{-

  The passes of the pilot, composed: from ISWIMμ to X86μ,

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ
           --concretize--> Clos3μ --delay--> Clos4μ --globalize--> Clos5μ --rco--> Monμ
           --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  as the typed pipeline's (Compiler/Pipeline.agda), without cast insertion:
  compile₄ goes to Clos4μ, compile to Clos5μ, and compile-mon,
  compile-imp, compile-cfg and compile-x86 continue. A program is a
  closed term of any type, and each compiled program has its type.

-}

module Mu.Compiler.Pipeline where

open import Mu.Language.Type using (Type)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.Clos4 as Clos4μ
import Mu.Language.Clos5 as Clos5μ
import Mu.Language.Mon as Monμ
import Mu.Language.Imp as Impμ
import Mu.Language.CFG as CFGμ
import Mu.Language.X86 as X86μ
open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Delay using (delay-program)
open import Mu.Compiler.Globalize using (globalize)
open import Mu.Compiler.RCO using (rco-program)
open import Mu.Compiler.LiftLocals using (lift-program)
open import Mu.Compiler.Explicate using (explicate)
open import Mu.Compiler.Select using (select)

open import Data.List using ([])

compile₄ : ∀ {A : Type} → ISWIMμ.Tm [] A → Clos4μ.Tm [] A
compile₄ M = delay-program (concretize-program (optimize-program (enclose (simplify M))))

compile : ∀ {A : Type} → ISWIMμ.Tm [] A → Clos5μ.Program A
compile M = globalize (compile₄ M)

compile-mon : ∀ {A : Type} → ISWIMμ.Tm [] A → Monμ.Program A
compile-mon M = rco-program (compile M)

compile-imp : ∀ {A : Type} → ISWIMμ.Tm [] A → Impμ.Program A
compile-imp M = lift-program (compile-mon M)

compile-cfg : ∀ {A : Type} → ISWIMμ.Tm [] A → CFGμ.Program A
compile-cfg M = explicate (compile-imp M)

compile-x86 : ∀ {A : Type} → ISWIMμ.Tm [] A → X86μ.Program A
compile-x86 M = select (compile-cfg M)
