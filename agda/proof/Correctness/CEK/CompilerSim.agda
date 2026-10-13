{-

  Correctness of the whole closure-conversion compiler, by CEK machines and
  forward simulations:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  Each pass is proved by a forward simulation, which, since all the
  machines are deterministic and total, gives its end theorem
  (Equivalent). These end theorems compose (equiv-trans): the compiled
  program terminates with the same observation as the original, goes
  wrong exactly when it does, and diverges exactly when it does.

  The compiler is Compiler.Pipeline.compile, the one of the
  denotational end-to-end theorem (CompilerCorrect), and it is
  definitionally the composition of the passes as the simulations state
  them. The only precondition is that of enclose: the ISWIM program is
  closed; enclose then produces a well-scoped program, as optimize needs
  (enclose-closed).

-}

module proof.Correctness.CEK.CompilerSim where

open import Compiler.Pipeline using (compile)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Compiler.EncloseScope using (Closed; enclose-closed)
open import proof.Correctness.CEK.EncloseSim using (enclose-correct)
open import proof.Correctness.CEK.OptimizeSim using (optimize-correct)
open import proof.Correctness.CEK.ConcretizeSim using (concretize-correct)
open import proof.Correctness.CEK.DelaySim using (delay-correct)
open import proof.Correctness.CEK.GlobalizeSim using (globalize-correct)
import Semantics.CEK.ISWIM as S
import Semantics.CEK.Clos5 as T

open import Data.Product using (_,_; proj₁; proj₂)

{- The end theorem -------------------------------------------------------------}

compile-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile M))
compile-correct M c =
  equiv-trans (enclose-correct M c) (equiv-trans (optimize-correct _ (enclose-closed M c))
    (equiv-trans (concretize-correct _) (equiv-trans (delay-correct _) (globalize-correct _))))

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

compile-wrong : ∀ M → Closed M
  → Terminates (S.sem M) o-wrong ⇔ Terminates (T.sem (compile M)) o-wrong
compile-wrong M c = Equivalent.terminates (compile-correct M c) o-wrong

compile-diverges : ∀ M → Closed M → Diverges (S.sem M) ⇔ Diverges (T.sem (compile M))
compile-diverges M c = Equivalent.diverges (compile-correct M c)
