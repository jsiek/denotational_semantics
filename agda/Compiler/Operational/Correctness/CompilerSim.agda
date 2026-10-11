{-

  Correctness of the whole closure-conversion compiler, CompCert style:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  The forward simulations of the five passes compose into one from the
  ISWIM machine to the Clos5 machine, and since both machines are
  deterministic and total, the compiled program terminates with the same
  observation as the original, goes wrong exactly when it does, and
  diverges exactly when it does.

  The compiler is the one of the denotational end-to-end theorem
  (Compiler.Model.Graph.Correctness.CompilerCorrect), and it is
  definitionally the composition of the passes as the simulations state
  them. The only precondition is that of enclose: the ISWIM program is
  closed; enclose then produces a well-scoped program, as optimize needs
  (enclose-closed).

-}

module Compiler.Operational.Correctness.CompilerSim where

open import Compiler.Model.Graph.Correctness.CompilerCorrect using (compile)
open import Compiler.Operational.Observation
open import Compiler.Operational.Smallstep
open import Compiler.Operational.Simulation
open import Compiler.Operational.Correctness.EncloseSim using (Closed)
open import Compiler.Operational.Correctness.OptimizeSim using (enclose-optimize-fsim)
open import Compiler.Operational.Correctness.ConcretizeSim using (concretize-fsim)
open import Compiler.Operational.Correctness.DelaySim using (delay-fsim)
open import Compiler.Operational.Correctness.GlobalizeSim using (globalize-fsim)
import Compiler.Operational.Machine.ISWIM as S
import Compiler.Operational.Machine.Clos5 as T

open import Data.Product using (_,_; proj₁; proj₂)

{- The end theorem -------------------------------------------------------------}

compile-fsim : ∀ M → Closed M → FSim (S.sem M) (T.sem (compile M))
compile-fsim M c =
  compose (enclose-optimize-fsim M c)
    (compose (concretize-fsim _) (compose (delay-fsim _) (globalize-fsim _)))

compile-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile M))
compile-correct M c =
  equivalent (compile-fsim M c) machine-det machine-progress machine-det machine-progress

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
