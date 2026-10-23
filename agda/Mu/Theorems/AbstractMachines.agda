{-

  The correctness of the ISWIMμ compiler by abstract machines (CEK
  machines) and simulations: the statement of Theorem F.2 (correctness,
  abstract machines) of the paper. The proofs (forward simulations) are
  in Mu/proof/Correctness/AbstractMachines/; each theorem here is one of
  them, with its type written out.

  The paper's compile is compile-x86 (Mu/Compiler/Pipeline.agda), the
  composition of the ten passes. Each language has a small-step machine
  (here Lₘ.sem for language L, Mu/Semantics/AbstractMachines/); those of
  ISWIMμ and X86μ are the ones these statements use. A machine
  terminates with an observation (Semantics/Observation.agda) or
  diverges. Two machines are Equivalent (Framework/Smallstep.agda) when
  each terminates with o exactly when the other does, and one diverges
  exactly when the other does.

  To read them: the languages (Mu/Language/), the passes (Mu/Compiler/),
  the machines of ISWIMμ and X86μ, and the observations.

-}

module Mu.Theorems.AbstractMachines where

open import Framework.Primitives using (Int)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges; Equivalent)

open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
open import Mu.Compiler.Pipeline using (compile-x86)

import Mu.Semantics.AbstractMachines.ISWIM as ISWIMμₘ
import Mu.Semantics.AbstractMachines.X86 as X86μₘ

import Mu.proof.Correctness.AbstractMachines.PipelineSim as PipelineSim

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Theorem F.2 (Correctness, abstract machines) -------------------------------}

{- for a closed ISWIMμ term M of type Int, and every integer n: the
   machine of ISWIMμ on M terminates with n if and only if the machine of
   X86μ on compile M does -}
compile-x86-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (n : ℤ)
  → Terminates (ISWIMμₘ.sem M) (o-const Int n) ⇔ Terminates (X86μₘ.sem (compile-x86 M)) (o-const Int n)
compile-x86-const = PipelineSim.compile-x86-const

{- and one diverges if and only if the other does -}
compile-x86-diverges : ∀ (M : ISWIMμ.Tm [] (base Int))
  → Diverges (ISWIMμₘ.sem M) ⇔ Diverges (X86μₘ.sem (compile-x86 M))
compile-x86-diverges = PipelineSim.compile-x86-diverges

{- more generally, the two machines are equivalent for every closed
   term M -}
compile-x86-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → Equivalent (ISWIMμₘ.sem M) (X86μₘ.sem (compile-x86 M))
compile-x86-correct = PipelineSim.compile-x86-correct
