{-

  The compiler of the pilot (Mu/Compiler/Pipeline.agda) is correct by
  clocked interpreters, as the typed one
  (proof/Correctness/Interp/CompilerFuel.agda): each pass is proved
  clock for clock (simplify, which removes calls, clock-monotone), and the end theorems compose (equiv-trans), from
  ISWIMμ to Clos4μ (compile₄), Clos5μ (compile), Monμ run as Clos5μ
  (compile-mon), Impμ, CFGμ and X86μ. A program is a closed term of any
  type; for a main of type Int, the interpreters of ISWIMμ and X86μ
  stop with the same constant, or both diverge (compile-x86-const,
  compile-x86-diverges), as in the other columns.

-}

module Mu.proof.Correctness.Interp.CompilerFuel where

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
import Mu.Semantics.Interp.ISWIM as ISWIMμᵢ
import Mu.Semantics.Interp.Clos4 as Clos4μᵢ
import Mu.Semantics.Interp.Clos5 as Clos5μᵢ
import Mu.Semantics.Interp.Imp as Impμᵢ
import Mu.Semantics.Interp.CFG as CFGμᵢ
import Mu.Semantics.Interp.X86 as X86μᵢ

open import Mu.proof.Correctness.Interp.SimplifyFuel using (simplify-correct)
open import Mu.proof.Correctness.Interp.EncloseFuel using (enclose-correct)
open import Mu.proof.Correctness.Interp.OptimizeFuel using (optimize-correct)
open import Mu.proof.Correctness.Interp.ConcretizeFuel using (concretize-correct)
open import Mu.proof.Correctness.Interp.DelayFuel using (delay-correct)
open import Mu.proof.Correctness.Interp.GlobalizeFuel using (globalize-correct)
open import Mu.proof.Correctness.Interp.RCOFuel using (rco-correct)
open import Mu.proof.Correctness.Interp.LiftLocalsFuel using (lift-locals-correct)
open import Mu.proof.Correctness.Interp.ExplicateFuel using (explicate-correct)
open import Mu.proof.Correctness.Interp.SelectFuel using (select-correct)

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Data.Product using (_,_; proj₁; proj₂)

compile₄-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Clos4μᵢ.sem (compile₄ M))
compile₄-correct M =
  equiv-trans (simplify-correct M) (equiv-trans (enclose-correct (simplify M)) (equiv-trans (optimize-correct M₁)
    (equiv-trans (concretize-correct M₂) (delay-correct (concretize-program M₂)))))
  where M₁ = enclose (simplify M)
        M₂ = optimize-program M₁

compile-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Clos5μᵢ.sem (compile M))
compile-correct M = equiv-trans (compile₄-correct M) (globalize-correct (compile₄ M))

compile-mon-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Clos5μᵢ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct M = equiv-trans (compile-correct M) (rco-correct (compile M))

compile-imp-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (Impμᵢ.sem (compile-imp M))
compile-imp-correct M = equiv-trans (compile-mon-correct M) (lift-locals-correct (compile-mon M))

compile-cfg-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (CFGμᵢ.sem (compile-cfg M))
compile-cfg-correct M = equiv-trans (compile-imp-correct M) (explicate-correct (compile-imp M))

compile-x86-correct : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (X86μᵢ.sem (compile-x86 M))
compile-x86-correct M = equiv-trans (compile-cfg-correct M) (select-correct (compile-cfg M))

{- in particular -}

compile-const : ∀ {A} (M : Tm [] A) → ∀ B k
  → Terminates (ISWIMμᵢ.sem M) (o-const B k) ⇔ Terminates (Clos5μᵢ.sem (compile M)) (o-const B k)
compile-const M B k = Equivalent.terminates (compile-correct M) (o-const B k)

compile-converges : ∀ {A} (M : Tm [] A)
  → Converges (Terminates (ISWIMμᵢ.sem M)) ⇔ Converges (Terminates (Clos5μᵢ.sem (compile M)))
compile-converges M =
    (λ { (o , a , t) → o , a , proj₁ (Equivalent.terminates E o) t })
  , (λ { (o , a , t) → o , a , proj₂ (Equivalent.terminates E o) t })
  where E = compile-correct M

compile-error : ∀ {A} (M : Tm [] A)
  → Terminates (ISWIMμᵢ.sem M) o-error ⇔ Terminates (Clos5μᵢ.sem (compile M)) o-error
compile-error M = Equivalent.terminates (compile-correct M) o-error

compile-diverges : ∀ {A} (M : Tm [] A) → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (Clos5μᵢ.sem (compile M))
compile-diverges M = Equivalent.diverges (compile-correct M)

{- for a main of type Int, as the other columns state it -}

compile-x86-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμᵢ.sem M) (o-const Int k) ⇔ Terminates (X86μᵢ.sem (compile-x86 M)) (o-const Int k)
compile-x86-const M k = Equivalent.terminates (compile-x86-correct M) (o-const Int k)

compile-x86-diverges : ∀ (M : Tm [] (base Int)) → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile-x86 M))
compile-x86-diverges M = Equivalent.diverges (compile-x86-correct M)
