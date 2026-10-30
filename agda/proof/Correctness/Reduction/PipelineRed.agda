{-

  The typed compiler (Compiler/Pipeline.agda) is correct on the
  reduction semantics, for closed programs: each pass is Equivalent
  (proof/Correctness/Reduction/*Red.agda) and equivalence composes.
  Simplify's proof is the untyped one; Impᵀ, CFGᵀ and X86ᵀ have no
  binders and keep their machines, with the CEK column's proofs of
  explicate control and select instructions.

-}

module proof.Correctness.Reduction.PipelineRed where

open import Compiler.CaptureScope using (Closed)
open import Compiler.Simplify using (simplify)
open import Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Language.Typed.Mon using (⌜_⌝ₚ)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import Semantics.Observation
open import Semantics.Reduction.Smallstep using (Equivalent; Terminates; Diverges)
open import proof.Framework.Simulation Obs using (equiv-trans)
open import proof.Correctness.Reduction.SimplifyRed using (simplify-correct)
open import proof.Correctness.Reduction.CastRed using (cast-correct)
open import proof.Correctness.Reduction.CaptureRed using (capture-correct)
open import proof.Correctness.Reduction.PruneRed using (prune-correct)
open import proof.Correctness.Reduction.ConcretizeRed using (concretize-correct)
open import proof.Correctness.Reduction.SplitRed using (split-correct)
open import proof.Correctness.Reduction.HoistRed using (hoist-correct)
open import proof.Correctness.Reduction.RCORed using (rco-correct)
open import proof.Correctness.Reduction.LiftLocalsRed using (lift-locals-correct)
open import proof.Correctness.CEK.ExplicateSim using (explicate-correct)
open import proof.Correctness.CEK.SelectSim using (select-correct)
import Semantics.Reduction.ISWIM as S
import Semantics.Reduction.Typed.Clos5 as T
import Semantics.CEK.Typed.Imp as Impᵀₘ
import Semantics.CEK.Typed.CFG as CFGᵀₘ
import Semantics.CEK.Typed.X86 as X86ᵀₘ

open import Data.Product using (_,_; proj₁; proj₂)

compile-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile M))
compile-correct M c =
  equiv-trans (simplify-correct M c) (equiv-trans (cast-correct (simplify M) (simplify-closed M c))
    (equiv-trans (capture-correct _) (equiv-trans (prune-correct _) (equiv-trans (concretize-correct _)
      (equiv-trans (split-correct _) (hoist-correct _))))))

compile-mon-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct M c = equiv-trans (compile-correct M c) (rco-correct _)

compile-imp-correct : ∀ M → Closed M → Equivalent (S.sem M) (Impᵀₘ.sem (compile-imp M))
compile-imp-correct M c = equiv-trans (compile-mon-correct M c) (lift-locals-correct _)

compile-cfg-correct : ∀ M → Closed M → Equivalent (S.sem M) (CFGᵀₘ.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct _)

compile-x86-correct : ∀ M → Closed M → Equivalent (S.sem M) (X86ᵀₘ.sem (compile-x86 M))
compile-x86-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct _)

{- in particular, for compile -}

compile-const : ∀ M → Closed M → ∀ B k
  → Terminates (S.sem M) (o-const B k) ⇔ Terminates (T.sem (compile M)) (o-const B k)
compile-const M c B k = Equivalent.terminates (compile-correct M c) (o-const B k)

compile-converges : ∀ M → Closed M
  → Converges (Terminates (S.sem M)) ⇔ Converges (Terminates (T.sem (compile M)))
compile-converges M c =
    (λ { (o , a , t) → o , a , proj₁ (Equivalent.terminates E o) t })
  , (λ { (o , a , t) → o , a , proj₂ (Equivalent.terminates E o) t })
  where E = compile-correct M c

compile-error : ∀ M → Closed M → Terminates (S.sem M) o-error ⇔ Terminates (T.sem (compile M)) o-error
compile-error M c = Equivalent.terminates (compile-correct M c) o-error

compile-diverges : ∀ M → Closed M → Diverges (S.sem M) ⇔ Diverges (T.sem (compile M))
compile-diverges M c = Equivalent.diverges (compile-correct M c)
