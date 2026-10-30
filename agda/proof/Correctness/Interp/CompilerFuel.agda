{-

  Correctness of the typed compiler (Compiler/Pipeline.agda) by
  clocked interpreters: each pass is proved clock for clock (simplify
  clock-monotone), and the end theorems compose (equiv-trans), from
  untyped ISWIM to Clos5ᵀ (compile), Monᵀ run as Clos5ᵀ (compile-mon),
  Impᵀ, CFGᵀ and X86ᵀ. The only precondition is that the ISWIM program
  is closed.

-}

module proof.Correctness.Interp.CompilerFuel where

open import Language.ISWIM using (AST)
open import Language.Typed.Mon using (⌜_⌝ₚ)
open import Compiler.CaptureScope using (Closed)
open import Compiler.Simplify using (simplify)
open import Compiler.Cast using (cast-closed)
open import Compiler.Capture using (capture)
open import Compiler.Prune using (prune-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Split using (split-program)
open import Compiler.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import Semantics.Observation
open import proof.Semantics.Interp.Clock
import Semantics.Interp.ISWIM as ISWIMᵢ
import Semantics.Interp.Typed.Clos4 as Clos4ᵀᵢ
import Semantics.Interp.Typed.Clos5 as Clos5ᵀᵢ
import Semantics.Interp.Typed.Imp as Impᵀᵢ
import Semantics.Interp.Typed.CFG as CFGᵀᵢ
import Semantics.Interp.Typed.X86 as X86ᵀᵢ

open import proof.Correctness.Interp.SimplifyFuel using (simplify-correct)
open import proof.Correctness.Interp.CastFuel using (cast-correct)
open import proof.Correctness.Interp.CaptureFuel using (capture-correct)
open import proof.Correctness.Interp.PruneFuel using (prune-correct)
open import proof.Correctness.Interp.ConcretizeFuel using (concretize-correct)
open import proof.Correctness.Interp.SplitFuel using (split-correct)
open import proof.Correctness.Interp.HoistFuel using (hoist-correct)
open import proof.Correctness.Interp.RCOFuel using (rco-correct)
open import proof.Correctness.Interp.LiftLocalsFuel using (lift-locals-correct)
open import proof.Correctness.Interp.ExplicateFuel using (explicate-correct)
open import proof.Correctness.Interp.SelectFuel using (select-correct)

open import Data.Product using (_,_; proj₁; proj₂)

compile₄-correct : ∀ M → Closed M → Equivalent (ISWIMᵢ.sem M) (Clos4ᵀᵢ.sem (compile₄ M))
compile₄-correct M c =
  equiv-trans (simplify-correct M c) (equiv-trans (cast-correct (simplify M) (simplify-closed M c))
    (equiv-trans (capture-correct M₁) (equiv-trans (prune-correct M₂)
      (equiv-trans (concretize-correct M₃) (split-correct (concretize-program M₃))))))
  where M₁ = cast-closed (simplify M)
        M₂ = capture M₁
        M₃ = prune-program M₂

compile-correct : ∀ M → Closed M → Equivalent (ISWIMᵢ.sem M) (Clos5ᵀᵢ.sem (compile M))
compile-correct M c = equiv-trans (compile₄-correct M c) (hoist-correct (compile₄ M))

compile-mon-correct : ∀ M → Closed M → Equivalent (ISWIMᵢ.sem M) (Clos5ᵀᵢ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct M c = equiv-trans (compile-correct M c) (rco-correct (compile M))

compile-imp-correct : ∀ M → Closed M → Equivalent (ISWIMᵢ.sem M) (Impᵀᵢ.sem (compile-imp M))
compile-imp-correct M c = equiv-trans (compile-mon-correct M c) (lift-locals-correct (compile-mon M))

compile-cfg-correct : ∀ M → Closed M → Equivalent (ISWIMᵢ.sem M) (CFGᵀᵢ.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct (compile-imp M))

compile-x86-correct : ∀ M → Closed M → Equivalent (ISWIMᵢ.sem M) (X86ᵀᵢ.sem (compile-x86 M))
compile-x86-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct (compile-cfg M))

{- in particular -}

compile-const : ∀ M → Closed M → ∀ B k
  → Terminates (ISWIMᵢ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵀᵢ.sem (compile M)) (o-const B k)
compile-const M c B k = Equivalent.terminates (compile-correct M c) (o-const B k)

compile-converges : ∀ M → Closed M
  → Converges (Terminates (ISWIMᵢ.sem M)) ⇔ Converges (Terminates (Clos5ᵀᵢ.sem (compile M)))
compile-converges M c =
    (λ { (o , a , t) → o , a , proj₁ (Equivalent.terminates E o) t })
  , (λ { (o , a , t) → o , a , proj₂ (Equivalent.terminates E o) t })
  where E = compile-correct M c

compile-error : ∀ M → Closed M
  → Terminates (ISWIMᵢ.sem M) o-error ⇔ Terminates (Clos5ᵀᵢ.sem (compile M)) o-error
compile-error M c = Equivalent.terminates (compile-correct M c) o-error

compile-diverges : ∀ M → Closed M → Diverges (ISWIMᵢ.sem M) ⇔ Diverges (Clos5ᵀᵢ.sem (compile M))
compile-diverges M c = Equivalent.diverges (compile-correct M c)
