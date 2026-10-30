{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) is correct by
  clocked interpreters, as the typed one
  (proof/Correctness/Interp/CompilerFuel.agda): each pass is proved
  clock for clock (simplify, which removes calls, clock-monotone), and the end theorems compose (equiv-trans), from
  ISWIMμ to PairClosμ (compile-to-PairClos), GlobalFunμ (compile-to-GlobalFun), Monμ run as GlobalFunμ
  (compile-to-Mon), Impμ, CFGμ and X86μ. A program is a closed term of any
  type; for a main of type Int, the interpreters of ISWIMμ and X86μ
  stop with the same constant, or both diverge (compile-const,
  compile-diverges), as in the other columns.

-}

module Mu.proof.Correctness.ClockedInterpreters.CompilerFuel where

open import Framework.Primitives using (Int)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Pipeline using (compile-to-PairClos; compile-to-GlobalFun; compile-to-Mon; compile-to-Imp; compile-to-CFG; compile)
open import Semantics.Observation
open import proof.Semantics.Interp.Clock
import Mu.Semantics.ClockedInterpreters.ISWIM as ISWIMμᵢ
import Mu.Semantics.ClockedInterpreters.PairClos as PairClosμᵢ
import Mu.Semantics.ClockedInterpreters.GlobalFun as GlobalFunμᵢ
import Mu.Semantics.ClockedInterpreters.Imp as Impμᵢ
import Mu.Semantics.ClockedInterpreters.CFG as CFGμᵢ
import Mu.Semantics.ClockedInterpreters.X86 as X86μᵢ

open import Mu.proof.Correctness.ClockedInterpreters.SimplifyFuel using (simplify-correct)
open import Mu.proof.Correctness.ClockedInterpreters.EncloseFuel using (enclose-correct)
open import Mu.proof.Correctness.ClockedInterpreters.OptimizeFuel using (optimize-correct)
open import Mu.proof.Correctness.ClockedInterpreters.ConcretizeFuel using (concretize-correct)
open import Mu.proof.Correctness.ClockedInterpreters.DelayFuel using (delay-correct)
open import Mu.proof.Correctness.ClockedInterpreters.GlobalizeFuel using (globalize-correct)
open import Mu.proof.Correctness.ClockedInterpreters.RCOFuel using (rco-correct)
open import Mu.proof.Correctness.ClockedInterpreters.LiftLocalsFuel using (lift-locals-correct)
open import Mu.proof.Correctness.ClockedInterpreters.ExplicateFuel using (explicate-correct)
open import Mu.proof.Correctness.ClockedInterpreters.SelectFuel using (select-correct)

open import Data.Integer using (ℤ)
open import Data.List using ([])

compile-to-PairClos-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (PairClosμᵢ.sem (compile-to-PairClos M))
compile-to-PairClos-correct M =
  equiv-trans (simplify-correct M) (equiv-trans (enclose-correct (simplify M)) (equiv-trans (optimize-correct M₁)
    (equiv-trans (concretize-correct M₂) (delay-correct (concretize-program M₂)))))
  where M₁ = enclose (simplify M)
        M₂ = optimize-program M₁

compile-to-GlobalFun-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (GlobalFunμᵢ.sem (compile-to-GlobalFun M))
compile-to-GlobalFun-correct M = equiv-trans (compile-to-PairClos-correct M) (globalize-correct (compile-to-PairClos M))

compile-to-Mon-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (GlobalFunμᵢ.sem ⌜ compile-to-Mon M ⌝ₚ)
compile-to-Mon-correct M = equiv-trans (compile-to-GlobalFun-correct M) (rco-correct (compile-to-GlobalFun M))

compile-to-Imp-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Impμᵢ.sem (compile-to-Imp M))
compile-to-Imp-correct M = equiv-trans (compile-to-Mon-correct M) (lift-locals-correct (compile-to-Mon M))

compile-to-CFG-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (CFGμᵢ.sem (compile-to-CFG M))
compile-to-CFG-correct M = equiv-trans (compile-to-Imp-correct M) (explicate-correct (compile-to-Imp M))

compile-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (X86μᵢ.sem (compile M))
compile-correct M = equiv-trans (compile-to-CFG-correct M) (select-correct (compile-to-CFG M))

{- for a main of type Int, as the other columns state it -}

compile-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμᵢ.sem M) (o-const Int k) ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const Int k)
compile-const M k = Equivalent.terminates (compile-correct M) (o-const Int k)

compile-diverges : ∀ (M : Tm [] (base Int)) → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile M))
compile-diverges M = Equivalent.diverges (compile-correct M)
