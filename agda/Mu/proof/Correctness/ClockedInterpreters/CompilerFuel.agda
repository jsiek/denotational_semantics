{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) is correct by
  clocked interpreters, as the typed one
  (proof/Correctness/Interp/CompilerFuel.agda): each pass is proved
  clock for clock (simplify, which removes calls, clock-monotone), and the end theorems compose (equiv-trans), from
  ISWIMμ to FlatClosμ (compile₄), GlobalFunμ (compile), Monμ run as GlobalFunμ
  (compile-mon), Impμ, CFGμ and X86μ. A program is a closed term of any
  type; for a main of type Int, the interpreters of ISWIMμ and X86μ
  stop with the same constant, or both diverge (compile-x86-const,
  compile-x86-diverges), as in the other columns.

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
open import Mu.Compiler.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Semantics.Observation
open import proof.Semantics.Interp.Clock
import Mu.Semantics.ClockedInterpreters.ISWIM as ISWIMμᵢ
import Mu.Semantics.ClockedInterpreters.FlatClos as FlatClosμᵢ
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

compile₄-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (FlatClosμᵢ.sem (compile₄ M))
compile₄-correct M =
  equiv-trans (simplify-correct M) (equiv-trans (enclose-correct (simplify M)) (equiv-trans (optimize-correct M₁)
    (equiv-trans (concretize-correct M₂) (delay-correct (concretize-program M₂)))))
  where M₁ = enclose (simplify M)
        M₂ = optimize-program M₁

compile-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (GlobalFunμᵢ.sem (compile M))
compile-correct M = equiv-trans (compile₄-correct M) (globalize-correct (compile₄ M))

compile-mon-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (GlobalFunμᵢ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct M = equiv-trans (compile-correct M) (rco-correct (compile M))

compile-imp-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Impμᵢ.sem (compile-imp M))
compile-imp-correct M = equiv-trans (compile-mon-correct M) (lift-locals-correct (compile-mon M))

compile-cfg-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (CFGμᵢ.sem (compile-cfg M))
compile-cfg-correct M = equiv-trans (compile-imp-correct M) (explicate-correct (compile-imp M))

compile-x86-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (X86μᵢ.sem (compile-x86 M))
compile-x86-correct M = equiv-trans (compile-cfg-correct M) (select-correct (compile-cfg M))

{- for a main of type Int, as the other columns state it -}

compile-x86-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμᵢ.sem M) (o-const Int k) ⇔ Terminates (X86μᵢ.sem (compile-x86 M)) (o-const Int k)
compile-x86-const M k = Equivalent.terminates (compile-x86-correct M) (o-const Int k)

compile-x86-diverges : ∀ (M : Tm [] (base Int)) → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile-x86 M))
compile-x86-diverges M = Equivalent.diverges (compile-x86-correct M)
