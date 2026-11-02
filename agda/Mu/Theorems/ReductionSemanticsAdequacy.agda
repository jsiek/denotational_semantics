{-

  The adequacy of the graph model for the reduction semantics of FPC:
  the analogue, for reduction, of Proposition 5.1 (adequacy) of the paper
  (Mu/Theorems/Adequacy.agda, for the clocked interpreters), and the
  consequence drawn from it with Theorem 4.1, for the pair the reduction
  column's theorem relates (Mu/Theorems/ReductionSemantics.agda): the
  reduction semantics of FPC and the machine of X86μ. It is an
  alternative to Mu/Theorems/Adequacy.agda, reported separately. The
  proofs are in Mu/proof/Adequacy/ReductionSemantics/ (and, for X86μ,
  Mu/proof/Adequacy/AbstractMachines/, as in
  Mu/Theorems/AbstractMachinesAdequacy.agda).

  compile is Mu/Compiler/Pipeline.agda's. The reduction semantics
  terminates with an observation when a run of reductions from M
  reaches a term that stops with that observation, and it diverges
  when it has a run of every length (Framework/Smallstep.agda), as in
  Mu/Theorems/ReductionSemantics.agda.

  To read them: those of Mu/Theorems/GraphModel.agda and of
  Mu/Theorems/ReductionSemantics.agda.

-}

module Mu.Theorems.ReductionSemanticsAdequacy where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (const)
open import Semantics.Observation using (o-const; _⇔_)
import Semantics.Reduction.Smallstep as R
import Semantics.CEK.Smallstep as C
open import Mu.Language.Type using (base)
import Mu.Language.FPC as FPC
open import Mu.Compiler.Pipeline using (compile)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Mu.Semantics.GraphModel.FPC using (⟦_⟧)
import Mu.Semantics.ReductionSemantics.FPC as FPCᵣ
import Mu.Semantics.AbstractMachines.X86 as X86μₘ

import Mu.proof.Adequacy.ReductionSemantics.FPC as AdequacyFPC
import Mu.proof.Adequacy.ReductionSemantics.EndToEnd as EndToEnd

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Relation.Nullary using (¬_)

{- Adequacy, reduction semantics ------------------------------------------------}

{- for a closed FPC term M (of any type), and every constant c:
   c ∈ ⟦ M ⟧ if and only if M reduces to c -}
fpc-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ R.Terminates (FPCᵣ.sem M) (o-const B k)
fpc-const-iff = AdequacyFPC.const-iff

{- and ⟦ M ⟧ is empty if and only if the reduction of M diverges -}
fpc-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → R.Diverges (FPCᵣ.sem M) ⇔ (¬ nonempty (⟦ M ⟧ ρ₀))
fpc-diverges-iff = AdequacyFPC.diverges-iff

{- With Theorem 4.1: the compiler, observed through reduction and the X86μ machine -}

{- for a program of type Int, the theorem the reduction column states
   (Proposition F.3): the reduction semantics of FPC and the machine of
   X86μ terminate with the same integer, or both diverge -}

end-to-end-x86-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → R.Terminates (FPCᵣ.sem M) (o-const Int n) ⇔ C.Terminates (X86μₘ.sem (compile M)) (o-const Int n)
end-to-end-x86-const = EndToEnd.end-to-end-x86-const

end-to-end-x86-diverges : ∀ (M : FPC.Tm [] (base Int))
  → R.Diverges (FPCᵣ.sem M) ⇔ C.Diverges (X86μₘ.sem (compile M))
end-to-end-x86-diverges = EndToEnd.end-to-end-x86-diverges
