{-

  The correctness of the ISWIMμ compiler by reduction semantics and
  simulations: the statement of Theorem F.3 (correctness, reduction
  semantics) of the paper. The proofs (forward simulations) are in
  Mu/proof/Correctness/ReductionSemantics/ (explicate control and select
  instructions: the abstract-machine proofs,
  Mu/proof/Correctness/AbstractMachines/, shared); each theorem here is
  one of them, with its type written out.

  compile (Mu/Compiler/Pipeline.agda) is the composition of the ten
  passes. Each language with binders has a
  reduction semantics by substitution (here Lᵣ.sem for language L,
  Mu/Semantics/ReductionSemantics/). Impμ, CFGμ and X86μ have no binders
  and keep their machines (here Lₘ.sem, Mu/Semantics/AbstractMachines/).
  A semantics terminates with an observation (Semantics/Observation.agda)
  or diverges. Two semantics are Equivalent (Framework/Smallstep.agda)
  when each terminates with o exactly when the other does, and one
  diverges exactly when the other does.

  To read them: the languages (Mu/Language/), the passes (Mu/Compiler/),
  the reduction semantics of ISWIMμ, the machine of X86μ, and the
  observations.

-}

module Mu.Theorems.ReductionSemantics where

open import Framework.Primitives using (Int)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Reduction.Smallstep using (Terminates; Diverges; Equivalent)

open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
open import Mu.Compiler.Pipeline using (compile)

import Mu.Semantics.ReductionSemantics.ISWIM as ISWIMμᵣ
import Mu.Semantics.AbstractMachines.X86 as X86μₘ

import Mu.proof.Correctness.ReductionSemantics.PipelineRed as PipelineRed

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Theorem F.3 (Correctness, reduction semantics) -----------------------------}

{- for a closed ISWIMμ term M of type Int, and every integer n: the
   reduction semantics of ISWIMμ on M terminates with n if and only if
   the machine of X86μ on compile M does -}
compile-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (n : ℤ)
  → Terminates (ISWIMμᵣ.sem M) (o-const Int n) ⇔ Terminates (X86μₘ.sem (compile M)) (o-const Int n)
compile-const = PipelineRed.compile-const

{- and one diverges if and only if the other does -}
compile-diverges : ∀ (M : ISWIMμ.Tm [] (base Int))
  → Diverges (ISWIMμᵣ.sem M) ⇔ Diverges (X86μₘ.sem (compile M))
compile-diverges = PipelineRed.compile-diverges

{- more generally, the two are equivalent for every closed term M -}
compile-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμᵣ.sem M) (X86μₘ.sem (compile M))
compile-correct = PipelineRed.compile-correct
