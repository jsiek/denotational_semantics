{-

  Correctness of the whole closure-conversion compiler, by CEK machines and
  forward simulations:

    ISWIM --simplify--> ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  Each pass is proved by a forward simulation, which, since all the
  machines are deterministic and total, gives its end theorem
  (Equivalent). These end theorems compose (equiv-trans): the compiled
  program terminates with the same observation as the original,
  errors exactly when it does, and diverges exactly when it does.

  The compiler is Untyped.Compiler.Pipeline.compile, the one of the
  denotational end-to-end theorem (CompilerCorrect), and it is
  definitionally the composition of the passes as the simulations state
  them. The only precondition is that of enclose: the ISWIM program is
  closed; enclose then produces a well-scoped program, as optimize needs
  (enclose-closed).

-}

module Untyped.proof.Correctness.CEK.CompilerSim where

open import Untyped.Compiler.Pipeline using (compile)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import Untyped.proof.Compiler.EncloseScope using (Closed; enclose-closed)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import Compiler.Simplify using (simplify)
open import proof.Correctness.CEK.SimplifySim using (simplify-correct)
open import Untyped.proof.Correctness.CEK.EncloseSim using (enclose-correct)
open import Untyped.proof.Correctness.CEK.OptimizeSim using (optimize-correct)
open import Untyped.proof.Correctness.CEK.ConcretizeSim using (concretize-correct)
open import Untyped.proof.Correctness.CEK.DelaySim using (delay-correct)
open import Untyped.proof.Correctness.CEK.GlobalizeSim using (globalize-correct)
import Semantics.CEK.ISWIM as S
import Untyped.Semantics.CEK.Clos5 as T

open import Data.Product using (_,_; proj₁; proj₂)

{- The end theorem -------------------------------------------------------------}

compile-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile M))
compile-correct M c =
  equiv-trans (simplify-correct M c)
    (equiv-trans (enclose-correct _ c') (equiv-trans (optimize-correct _ (enclose-closed (simplify M) c'))
      (equiv-trans (concretize-correct _) (equiv-trans (delay-correct _) (globalize-correct _)))))
  where c' = simplify-closed M c

{- in particular -}

compile-const : ∀ M → Closed M → ∀ B k
  → Terminates (S.sem M) (o-const B k) ⇔ Terminates (T.sem (compile M)) (o-const B k)
compile-const M c B k = Equivalent.terminates (compile-correct M c) (o-const B k)

compile-converges : ∀ M → Closed M
  → Converges (Terminates (S.sem M)) ⇔ Converges (Terminates (T.sem (compile M)))
compile-converges M c =
    (λ { (o , a , t) → o , a , proj₁ (Equivalent.terminates E o) t })
  , (λ { (o , a , t) → o , a , proj₂ (Equivalent.terminates E o) t })
  where E = compile-correct M c

compile-error : ∀ M → Closed M
  → Terminates (S.sem M) o-error ⇔ Terminates (T.sem (compile M)) o-error
compile-error M c = Equivalent.terminates (compile-correct M c) o-error

compile-diverges : ∀ M → Closed M → Diverges (S.sem M) ⇔ Diverges (T.sem (compile M))
compile-diverges M c = Equivalent.diverges (compile-correct M c)
