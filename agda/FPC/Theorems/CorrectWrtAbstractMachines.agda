{-

  The correctness of the FPC compiler by abstract machines (CEK
  machines) and simulations: the statement of Proposition F.2 (correctness,
  abstract machines) of the paper. The proofs (forward simulations) are
  in FPC/proof/Correctness/AbstractMachines/; each theorem here is one of
  them, with its type written out.

  compile (FPC/Compiler/Pipeline.agda) is the composition of the ten
  passes. Each language has a small-step machine
  (here Lₘ.sem for language L, FPC/Semantics/AbstractMachines/); those of
  FPC and X86μ are the ones these statements use. A machine
  terminates with an observation (Semantics/Observation.agda) or
  diverges. Two machines are Equivalent (Framework/Smallstep.agda) when
  each terminates with o exactly when the other does, and one diverges
  exactly when the other does.

  To read them: the languages (FPC/Language/), the passes (FPC/Compiler/),
  the machines of FPC and X86μ, and the observations.

-}

module FPC.Theorems.CorrectWrtAbstractMachines where

open import Framework.Primitives using (Int)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges; Equivalent)

open import FPC.Language.Type using (base)
import FPC.Language.FPC as FPC
open import FPC.Compiler.Pipeline using (compile)

import FPC.Semantics.AbstractMachines.FPC as FPCₘ
import FPC.Semantics.AbstractMachines.X86 as X86μₘ

import FPC.proof.Correctness.AbstractMachines.PipelineSim as PipelineSim

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Proposition F.2 (Correctness, abstract machines) --------------------------}

{- for a closed FPC term M of type Int, and every integer n: the
   machine of FPC on M terminates with n if and only if the machine of
   X86μ on compile M does -}
compile-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → Terminates (FPCₘ.sem M) (o-const Int n) ⇔ Terminates (X86μₘ.sem (compile M)) (o-const Int n)
compile-const = PipelineSim.compile-const

{- and one diverges if and only if the other does -}
compile-diverges : ∀ (M : FPC.Tm [] (base Int))
  → Diverges (FPCₘ.sem M) ⇔ Diverges (X86μₘ.sem (compile M))
compile-diverges = PipelineSim.compile-diverges

{- more generally, the two machines are equivalent for every closed
   term M -}
compile-correct : ∀ {A} (M : FPC.Tm [] A) → Equivalent (FPCₘ.sem M) (X86μₘ.sem (compile M))
compile-correct = PipelineSim.compile-correct
