{-

  The FPC compiler (FPC/Compiler/Pipeline.agda) is correct by
  clocked interpreters, as the typed one
  (ISWIM/proof/Correctness/Interp/CompilerFuel.agda): each pass is proved
  clock for clock (simplify, which removes calls, clock-monotone), and the end
  theorems compose (equiv-trans), from FPC to PairClosμ (compile-to-PairClos),
  GlobalFunμ (compile-to-GlobalFun), Monμ run as GlobalFunμ (compile-to-Mon),
  Impμ, CFGμ and X86μ. A program is a closed term of any type; for a main of
  type Int, the interpreters of FPC and X86μ stop with the same constant, or
  both diverge (compile-const, compile-diverges), as in the other columns.

-}

module FPC.proof.Correctness.ClockedInterpreters.CompilerFuel where

open import Framework.Primitives using (Int)
open import FPC.Language.Type using (base)
open import FPC.Language.FPC using (Tm)
open import FPC.Language.Mon using (⌜_⌝ₚ)
open import FPC.Compiler.Simplify using (simplify)
open import FPC.Compiler.Capture using (capture)
open import FPC.Compiler.Prune using (prune-program)
open import FPC.Compiler.Concretize using (concretize-program)
open import FPC.Compiler.Pipeline using (compile-to-PairClos;
  compile-to-GlobalFun; compile-to-Mon; compile-to-Imp; compile-to-CFG; compile)
open import Semantics.Observation
open import proof.Semantics.Interp.Clock
import FPC.Semantics.ClockedInterpreters.FPC as FPCᵢ
import FPC.Semantics.ClockedInterpreters.PairClos as PairClosμᵢ
import FPC.Semantics.ClockedInterpreters.GlobalFun as GlobalFunμᵢ
import FPC.Semantics.ClockedInterpreters.Imp as Impμᵢ
import FPC.Semantics.ClockedInterpreters.CFG as CFGμᵢ
import FPC.Semantics.ClockedInterpreters.X86 as X86μᵢ

open import FPC.proof.Correctness.ClockedInterpreters.SimplifyFuel using
  (simplify-correct)
open import FPC.proof.Correctness.ClockedInterpreters.CaptureFuel using
  (capture-correct)
open import FPC.proof.Correctness.ClockedInterpreters.PruneFuel using
  (prune-correct)
open import FPC.proof.Correctness.ClockedInterpreters.ConcretizeFuel using
  (concretize-correct)
open import FPC.proof.Correctness.ClockedInterpreters.SplitFuel using
  (split-correct)
open import FPC.proof.Correctness.ClockedInterpreters.HoistFuel using
  (hoist-correct)
open import FPC.proof.Correctness.ClockedInterpreters.RCOFuel using
  (rco-correct)
open import FPC.proof.Correctness.ClockedInterpreters.LiftLocalsFuel using
  (lift-locals-correct)
open import FPC.proof.Correctness.ClockedInterpreters.ExplicateFuel using
  (explicate-correct)
open import FPC.proof.Correctness.ClockedInterpreters.SelectFuel using
  (select-correct)

open import Data.Integer using (ℤ)
open import Data.List using ([])

compile-to-PairClos-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCᵢ.sem M) (PairClosμᵢ.sem (compile-to-PairClos M))
compile-to-PairClos-correct M =
  equiv-trans (simplify-correct M)
    (equiv-trans (capture-correct (simplify M)) (equiv-trans (prune-correct M₁)
    (equiv-trans (concretize-correct M₂)
        (split-correct (concretize-program M₂)))))
  where M₁ = capture (simplify M)
        M₂ = prune-program M₁

compile-to-GlobalFun-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCᵢ.sem M) (GlobalFunμᵢ.sem (compile-to-GlobalFun M))
compile-to-GlobalFun-correct M =
  equiv-trans (compile-to-PairClos-correct M)
  (hoist-correct (compile-to-PairClos M))

compile-to-Mon-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCᵢ.sem M) (GlobalFunμᵢ.sem ⌜ compile-to-Mon M ⌝ₚ)
compile-to-Mon-correct M =
  equiv-trans (compile-to-GlobalFun-correct M)
  (rco-correct (compile-to-GlobalFun M))

compile-to-Imp-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCᵢ.sem M) (Impμᵢ.sem (compile-to-Imp M))
compile-to-Imp-correct M =
  equiv-trans (compile-to-Mon-correct M)
  (lift-locals-correct (compile-to-Mon M))

compile-to-CFG-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCᵢ.sem M) (CFGμᵢ.sem (compile-to-CFG M))
compile-to-CFG-correct M =
  equiv-trans (compile-to-Imp-correct M) (explicate-correct (compile-to-Imp M))

compile-correct : ∀ {A} (M : Tm [] A)
  → Equivalent (FPCᵢ.sem M) (X86μᵢ.sem (compile M))
compile-correct M =
  equiv-trans (compile-to-CFG-correct M) (select-correct (compile-to-CFG M))

{- for a main of type Int, as the other columns state it -}

compile-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (FPCᵢ.sem M) (o-const Int k)
    ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const Int k)
compile-const M k = Equivalent.terminates (compile-correct M) (o-const Int k)

compile-diverges : ∀ (M : Tm [] (base Int))
  → Diverges (FPCᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile M))
compile-diverges M = Equivalent.diverges (compile-correct M)
