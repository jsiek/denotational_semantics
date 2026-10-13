{-

  Correctness of the whole closure-conversion compiler, by reduction
  semantics and forward simulations:

    ISWIM --simplify--> ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5

  Each pass is proved by a forward simulation, which gives its end
  theorem (Equivalent); these compose (equiv-trans). The compiler is
  Compiler.Pipeline.compile, the one of the other proofs. The
  only precondition is that of enclose, a closed ISWIM program: enclose
  then produces a well-scoped program, as optimize needs
  (enclose-closed), and optimize keeps it well scoped, as concretize
  needs (optimize-closed).

-}

module proof.Correctness.Reduction.CompilerRed where

open import Compiler.Pipeline using (compile)
open import Compiler.Enclose using (enclose)
open import Semantics.Observation
open import Semantics.Reduction.Smallstep using (Equivalent; Terminates; Diverges)
open import proof.Framework.Simulation Obs using (equiv-trans)
open import proof.Compiler.EncloseScope using (Closed; enclose-closed)
open import proof.Compiler.PipelineScope using (module Opt)
open import Compiler.Simplify using (simplify)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import proof.Correctness.Reduction.SimplifyRed using (simplify-correct)
open import proof.Correctness.Reduction.EncloseRed using (enclose-correct)
open import proof.Correctness.Reduction.OptimizeRed using (optimize-correct)
open import proof.Correctness.Reduction.ConcretizeRed using (concretize-correct)
open import proof.Correctness.Reduction.DelayRed using (delay-correct)
open import proof.Correctness.Reduction.GlobalizeRed using (globalize-correct)
import Semantics.Reduction.ISWIM as S
import Semantics.Reduction.Clos5 as T

open import Data.Product using (_,_; proj₁; proj₂)

{- The end theorem -------------------------------------------------------------}

compile-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile M))
compile-correct M c =
  equiv-trans (simplify-correct M c) (equiv-trans (enclose-correct _ c') (equiv-trans (optimize-correct _ w)
    (equiv-trans (concretize-correct _ (Opt.optimize-closed (enclose (simplify M)) w))
      (equiv-trans (delay-correct _) (globalize-correct _)))))
  where c' = simplify-closed M c
        w = enclose-closed (simplify M) c'

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
