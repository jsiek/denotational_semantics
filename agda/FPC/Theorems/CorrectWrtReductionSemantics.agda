{-

  The correctness of the FPC compiler by reduction semantics and
  simulations: the statement of Proposition F.3 (correctness, reduction
  semantics) of the paper. The proofs (forward simulations) are in
  FPC/proof/Correctness/ReductionSemantics/ (explicate control and select
  instructions: the abstract-machine proofs,
  FPC/proof/Correctness/AbstractMachines/, shared); each theorem here is
  one of them, with its type written out.

  compile (FPC/Compiler/Pipeline.agda) is the composition of the ten
  passes. Each language with binders has a
  reduction semantics by substitution (here Lᵣ.sem for language L,
  FPC/Semantics/ReductionSemantics/). Impμ, CFGμ and X86μ have no binders
  and keep their machines (here Lₘ.sem, FPC/Semantics/AbstractMachines/).
  A semantics terminates with an observation (Semantics/Observation.agda)
  or diverges. Two semantics are Equivalent (Framework/Smallstep.agda)
  when each terminates with o exactly when the other does, and one
  diverges exactly when the other does.

  To read them: the languages (FPC/Language/), the passes (FPC/Compiler/),
  the reduction semantics of FPC, the machine of X86μ, and the
  observations.

-}

module FPC.Theorems.CorrectWrtReductionSemantics where

open import Framework.Primitives using (Int)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Reduction.Smallstep using (Terminates; Diverges;
  Equivalent)

open import FPC.Language.Type using (base)
import FPC.Language.FPC as FPC
open import FPC.Compiler.Pipeline using (compile)

import FPC.Semantics.ReductionSemantics.FPC as FPCᵣ
import FPC.Semantics.AbstractMachines.X86 as X86μₘ

import FPC.proof.Correctness.ReductionSemantics.PipelineRed as PipelineRed

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Proposition F.3 (Correctness, reduction semantics) ------------------------}

{- for a closed FPC term M of type Int, and every integer n: the
   reduction semantics of FPC on M terminates with n if and only if
   the machine of X86μ on compile M does -}
compile-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → Terminates (FPCᵣ.sem M) (o-const Int n)
    ⇔ Terminates (X86μₘ.sem (compile M)) (o-const Int n)
compile-const = PipelineRed.compile-const

{- and one diverges if and only if the other does -}
compile-diverges : ∀ (M : FPC.Tm [] (base Int))
  → Diverges (FPCᵣ.sem M) ⇔ Diverges (X86μₘ.sem (compile M))
compile-diverges = PipelineRed.compile-diverges

{- more generally, the two are equivalent for every closed term M -}
compile-correct : ∀ {A} (M : FPC.Tm [] A)
  → Equivalent (FPCᵣ.sem M) (X86μₘ.sem (compile M))
compile-correct = PipelineRed.compile-correct
