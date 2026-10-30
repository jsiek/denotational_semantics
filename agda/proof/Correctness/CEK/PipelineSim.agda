{-

  The typed compiler (Compiler/Pipeline.agda) is correct on the
  machines, for closed programs: the ISWIM machine on M and the machine
  of each later language on its compilation are Equivalent, by composing
  the passes (simplify untyped, cast insertion on the simplified closed
  program, proof/Compiler/CastScope.agda, then the typed passes).

-}

module proof.Correctness.CEK.PipelineSim where

open import Language.ISWIM using (AST)
open import Compiler.CaptureScope using (Closed)
open import Compiler.Simplify using (simplify)
open import Compiler.Cast using (cast-closed)
open import Compiler.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Language.Typed.Mon using (⌜_⌝ₚ)
open import proof.Compiler.SimplifyScope using (closed-ws; simplify-closed)
open import proof.Compiler.CastScope using (cast-closed-≡)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import proof.Correctness.CEK.SimplifySim using (simplify-correct)
open import proof.Correctness.CEK.CastSim renaming (cast-correct to cast-ws-correct)
open import proof.Correctness.CEK.CaptureSim using (capture-correct)
open import proof.Correctness.CEK.PruneSim using (prune-correct)
open import proof.Correctness.CEK.ConcretizeSim using (concretize-correct)
open import proof.Correctness.CEK.DelaySim using (delay-correct)
open import proof.Correctness.CEK.GlobalizeSim using (globalize-correct)
open import proof.Correctness.CEK.RCOSim using (rco-correct)
open import proof.Correctness.CEK.LiftLocalsSim using (lift-locals-correct)
open import proof.Correctness.CEK.ExplicateSim using (explicate-correct)
open import proof.Correctness.CEK.SelectSim using (select-correct)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.ISWIM as ISWIMᵀₘ
import Semantics.CEK.Typed.Clos4 as Clos4ᵀₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
import Semantics.CEK.Typed.Imp as Impᵀₘ
import Semantics.CEK.Typed.CFG as CFGᵀₘ
import Semantics.CEK.Typed.X86 as X86ᵀₘ

open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

{- cast insertion, for closed programs -}
cast-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (ISWIMᵀₘ.sem (cast-closed M))
cast-correct M c = subst (λ T → Equivalent _ (ISWIMᵀₘ.sem T)) (sym (cast-closed-≡ M w)) (cast-ws-correct M w)
  where w = closed-ws {M} c

compile₄-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (Clos4ᵀₘ.sem (compile₄ M))
compile₄-correct M c =
  equiv-trans (simplify-correct M c) (equiv-trans (cast-correct (simplify M) (simplify-closed M c))
    (equiv-trans (capture-correct _) (equiv-trans (prune-correct _) (equiv-trans (concretize-correct _) (delay-correct _)))))

compile-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (Clos5ᵀₘ.sem (compile M))
compile-correct M c = equiv-trans (compile₄-correct M c) (globalize-correct _)

compile-mon-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (Clos5ᵀₘ.sem ⌜ compile-mon M ⌝ₚ)
compile-mon-correct M c = equiv-trans (compile-correct M c) (rco-correct _)

compile-imp-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (Impᵀₘ.sem (compile-imp M))
compile-imp-correct M c = equiv-trans (compile-mon-correct M c) (lift-locals-correct _)

compile-cfg-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (CFGᵀₘ.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct _)

compile-x86-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (X86ᵀₘ.sem (compile-x86 M))
compile-x86-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct _)

{- in particular, for compile -}

compile-const : ∀ M → Closed M → ∀ B k
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
compile-const M c B k = Equivalent.terminates (compile-correct M c) (o-const B k)

compile-converges : ∀ M → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
compile-converges M c =
    (λ { (o , a , t) → o , a , proj₁ (Equivalent.terminates E o) t })
  , (λ { (o , a , t) → o , a , proj₂ (Equivalent.terminates E o) t })
  where E = compile-correct M c

compile-error : ∀ M → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) o-error
compile-error M c = Equivalent.terminates (compile-correct M c) o-error

compile-diverges : ∀ M → Closed M → Diverges (ISWIMₘ.sem M) ⇔ Diverges (Clos5ᵀₘ.sem (compile M))
compile-diverges M c = Equivalent.diverges (compile-correct M c)
