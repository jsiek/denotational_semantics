{-

  The adequacy of the graph model for the abstract machines (CEK
  machines) of FPC and X86μ: the analogue, for the machines, of
  Theorem 4.5 (adequacy) of the paper (Mu/Theorems/Adequacy.agda, for
  the clocked interpreters), and the consequence drawn from it with
  Theorem 4.1, the theorem the operational proofs state. It is an
  alternative to Mu/Theorems/Adequacy.agda, reported separately. The
  proofs are in Mu/proof/Adequacy/AbstractMachines/.

  compile is Mu/Compiler/Pipeline.agda's. The X86μ statements are for
  the programs the compiler produces, so that their preconditions (in
  Mu/proof/) need not be audited.

  A machine terminates with an observation when a run from its start
  state reaches a final state with that observation, and it diverges
  when it has a run of every length (Framework/Smallstep.agda); these
  replace the interpreters' clocked Terminates and Diverges
  (Semantics/Interp/Clock.agda). The statements are otherwise those of
  Mu/Theorems/Adequacy.agda.

  To read them: those of Mu/Theorems/GraphModel.agda, the machines of
  FPC and X86μ (Mu/Semantics/AbstractMachines/FPC.agda and X86.agda),
  their transition systems (Semantics/CEK/Smallstep.agda,
  Framework/Smallstep.agda) and the observations
  (Semantics/Observation.agda).

-}

module Mu.Theorems.AbstractMachinesAdequacy where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (const)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Mu.Language.Type using (base)
import Mu.Language.FPC as FPC
open import Mu.Compiler.Pipeline using (compile)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Mu.Semantics.GraphModel.FPC using (⟦_⟧)
open import Mu.Semantics.GraphModel.X86 using (⟦_⟧ₜ)
import Mu.Semantics.AbstractMachines.FPC as FPCₘ
import Mu.Semantics.AbstractMachines.X86 as X86μₘ

import Mu.proof.Adequacy.AbstractMachines.FPC as AdequacyFPC
import Mu.proof.Adequacy.AbstractMachines.X86 as AdequacyX86
import Mu.proof.Adequacy.AbstractMachines.EndToEnd as EndToEnd

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Relation.Nullary using (¬_)

{- Adequacy, abstract machines ------------------------------------------------}

{- for a closed FPC term M (of any type), and every constant c:
   c ∈ ⟦ M ⟧ if and only if the machine of FPC terminates on M with c -}
fpc-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (FPCₘ.sem M) (o-const B k)
fpc-const-iff = AdequacyFPC.const-iff

{- and ⟦ M ⟧ is empty if and only if the machine diverges on M -}
fpc-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → Diverges (FPCₘ.sem M) ⇔ (¬ nonempty (⟦ M ⟧ ρ₀))
fpc-diverges-iff = AdequacyFPC.diverges-iff

{- the same holds for X86μ and compile M -}

x86-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ compile M ⟧ₜ) ⇔ Terminates (X86μₘ.sem (compile M)) (o-const B k)
x86-const-iff = AdequacyX86.x86-const-iff

x86-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → Diverges (X86μₘ.sem (compile M)) ⇔ (¬ nonempty ⟦ compile M ⟧ₜ)
x86-diverges-iff = AdequacyX86.x86-diverges-iff

{- With Theorem 4.1: the compiler, observed through the machines ------------}

{- for a program of type Int, the theorem the operational proofs state
   (Theorem F.2): the machines of FPC and X86μ terminate with the same
   integer, or both diverge -}

end-to-end-x86-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → Terminates (FPCₘ.sem M) (o-const Int n) ⇔ Terminates (X86μₘ.sem (compile M)) (o-const Int n)
end-to-end-x86-const = EndToEnd.end-to-end-x86-const

end-to-end-x86-diverges : ∀ (M : FPC.Tm [] (base Int))
  → Diverges (FPCₘ.sem M) ⇔ Diverges (X86μₘ.sem (compile M))
end-to-end-x86-diverges = EndToEnd.end-to-end-x86-diverges
