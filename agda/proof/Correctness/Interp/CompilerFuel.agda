{-

  Correctness of the whole closure-conversion compiler, by clocked
  interpreters:

    ISWIM --simplify--> ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  Each pass is proved clock for clock, which gives its end theorem
  (Equivalent). These end theorems compose (equiv-trans): the compiled
  program terminates with the same observation as the original, goes
  wrong exactly when it does, and diverges exactly when it does.

  The compiler is Compiler.Pipeline.compile, the one of the
  denotational end-to-end theorem (CompilerCorrect) and of the
  simulation one (CompilerSim), and it is definitionally the
  composition of the passes as the per-pass theorems state them. The
  only precondition is that of enclose: the ISWIM program is closed.

-}

module proof.Correctness.Interp.CompilerFuel where

open import Compiler.Pipeline using (compile)
open import Semantics.Observation
open import Compiler.Enclose using (enclose)
open import proof.Compiler.EncloseScope using (Closed)
open import Compiler.Optimize using (optimize-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Delay using (delay)
open import proof.Semantics.Interp.Clock
open import Compiler.Simplify using (simplify)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import proof.Correctness.Interp.SimplifyFuel using (simplify-correct)
open import proof.Correctness.Interp.OptimizeFuel using (enclose-optimize-correct)
open import proof.Correctness.Interp.ConcretizeFuel using (concretize-correct)
open import proof.Correctness.Interp.DelayFuel using (delay-correct)
open import proof.Correctness.Interp.GlobalizeFuel using (globalize-correct)
import Semantics.Interp.ISWIM as S
import Semantics.Interp.Clos5 as T

open import Data.Product using (_,_; proj₁; proj₂)

{- The end theorem -------------------------------------------------------------}

compile-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile M))
compile-correct M c =
  equiv-trans (simplify-correct M c) (equiv-trans (enclose-optimize-correct (simplify M) (simplify-closed M c))
    (equiv-trans (concretize-correct M₂) (equiv-trans (delay-correct M₃) (globalize-correct M₄))))
  where M₂ = optimize-program (enclose (simplify M))
        M₃ = concretize-program M₂
        M₄ = delay M₃

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
