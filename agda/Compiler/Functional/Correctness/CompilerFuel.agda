{-

  Correctness of the whole closure-conversion compiler, CakeML style:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  Each pass is proved clock for clock, which gives its end theorem
  (Equivalent). These end theorems compose (equiv-trans): the compiled
  program terminates with the same observation as the original, goes
  wrong exactly when it does, and diverges exactly when it does.

  The compiler is Compiler.Compile.Pipeline.compile, the one of the
  denotational end-to-end theorem (CompilerCorrect) and of the
  CompCert-style one (CompilerSim), and it is definitionally the
  composition of the passes as the per-pass theorems state them. The
  only precondition is that of enclose: the ISWIM program is closed.

-}

module Compiler.Functional.Correctness.CompilerFuel where

open import Compiler.Compile.Pipeline using (compile)
open import Compiler.Observation
open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Compile.EncloseScope using (Closed)
open import Compiler.Compile.Optimize using (optimize-program)
open import Compiler.Compile.Concretize using (concretize-program)
open import Compiler.Compile.Delay using (delay)
open import Compiler.Functional.Clock
open import Compiler.Functional.Correctness.OptimizeFuel using (enclose-optimize-correct)
open import Compiler.Functional.Correctness.ConcretizeFuel using (concretize-correct)
open import Compiler.Functional.Correctness.DelayFuel using (delay-correct)
open import Compiler.Functional.Correctness.GlobalizeFuel using (globalize-correct)
import Compiler.Functional.Interp.ISWIM as S
import Compiler.Functional.Interp.Clos5 as T

open import Data.Product using (_,_; proj₁; proj₂)

{- The end theorem -------------------------------------------------------------}

compile-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile M))
compile-correct M c =
  equiv-trans (enclose-optimize-correct M c)
    (equiv-trans (concretize-correct M₂) (equiv-trans (delay-correct M₃) (globalize-correct M₄)))
  where M₂ = optimize-program (enclose M)
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
