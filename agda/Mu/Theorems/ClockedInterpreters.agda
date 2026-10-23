{-

  The correctness of the ISWIMμ compiler by clocked interpreters and
  value relations: the statement of Theorem F.1 (correctness, clocked
  interpreters) of the paper. The proofs (clock for clock; for
  simplify, which removes calls, clock-monotone) are in
  Mu/proof/Correctness/ClockedInterpreters/; each theorem here is one of
  them, with its type written out.

  compile (Mu/Compiler/Pipeline.agda) is the composition of the ten
  passes. Each language has an interpreter with a
  clock (here Lᵢ.sem for language L, Mu/Semantics/ClockedInterpreters/);
  those of ISWIMμ and X86μ are the ones these statements use. A program
  terminates with an observation (Semantics/Observation.agda) when, for
  some clock, it returns a value observed as o, and diverges when it
  times out for every clock. Two programs are Equivalent
  (Framework/Clocked.agda) when each terminates with o exactly when the
  other does, and one diverges exactly when the other does.

  To read them: the languages (Mu/Language/), the passes (Mu/Compiler/),
  the interpreters of ISWIMμ and X86μ, and the observations.

-}

module Mu.Theorems.ClockedInterpreters where

open import Framework.Primitives using (Int)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges; Equivalent)

open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
open import Mu.Compiler.Pipeline using (compile)

import Mu.Semantics.ClockedInterpreters.ISWIM as ISWIMμᵢ
import Mu.Semantics.ClockedInterpreters.X86 as X86μᵢ

import Mu.proof.Correctness.ClockedInterpreters.CompilerFuel as CompilerFuel

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Theorem F.1 (Correctness, clocked interpreters) ----------------------------}

{- for a closed ISWIMμ term M of type Int, and every integer n: the
   interpreter of ISWIMμ on M terminates with n if and only if the
   interpreter of X86μ on compile M does -}
compile-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (n : ℤ)
  → Terminates (ISWIMμᵢ.sem M) (o-const Int n) ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const Int n)
compile-const = CompilerFuel.compile-const

{- and one diverges if and only if the other does -}
compile-diverges : ∀ (M : ISWIMμ.Tm [] (base Int))
  → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile M))
compile-diverges = CompilerFuel.compile-diverges

{- more generally, the two interpreters are equivalent for every closed
   term M -}
compile-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵢ.sem M) (X86μᵢ.sem (compile M))
compile-correct = CompilerFuel.compile-correct
