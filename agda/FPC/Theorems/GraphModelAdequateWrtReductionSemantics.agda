{-

  The adequacy of the graph model for the reduction semantics of FPC:
  the analogue, for reduction, of Proposition 5.1 (adequacy) of the paper
  (FPC/Theorems/GraphModelAdequateWrtClockedInterpreters.agda, for the clocked
  interpreters), and the consequence drawn from it with Theorem 4.1, for the
  pair the reduction column's theorem relates
  (FPC/Theorems/CorrectWrtReductionSemantics.agda): the reduction semantics of
  FPC and the machine of X86μ. It is an alternative to
  FPC/Theorems/GraphModelAdequateWrtClockedInterpreters.agda, reported
  separately. The proofs are in FPC/proof/Adequacy/ReductionSemantics/ (and, for
  X86μ, FPC/proof/Adequacy/AbstractMachines/, as in
  FPC/Theorems/GraphModelAdequateWrtAbstractMachines.agda).

  compile is FPC/Compiler/Pipeline.agda's. The reduction semantics
  terminates with an observation when a run of reductions from M
  reaches a term that stops with that observation, and it diverges
  when it has a run of every length (Framework/Smallstep.agda), as in
  FPC/Theorems/CorrectWrtReductionSemantics.agda.

  To read them: those of FPC/Theorems/CorrectWrtGraphModel.agda and of
  FPC/Theorems/CorrectWrtReductionSemantics.agda.

-}

module FPC.Theorems.GraphModelAdequateWrtReductionSemantics where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; ∅; _≃_)
open import Framework.GraphModel.Domain using (const)
open import Semantics.Observation using (o-const; _⇔_)
import Semantics.Reduction.Smallstep as R
import Semantics.CEK.Smallstep as C
open import FPC.Language.Type using (base)
import FPC.Language.FPC as FPC
open import FPC.Compiler.Pipeline using (compile)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import FPC.Semantics.GraphModel.FPC using (⟦_⟧)
import FPC.Semantics.ReductionSemantics.FPC as FPCᵣ
import FPC.Semantics.AbstractMachines.X86 as X86μₘ

open import proof.Framework.Iff using (⇔∘)
open import proof.Framework.GraphModel.SetsAsPredicates using (¬nonempty⇔≃∅)
import FPC.proof.Adequacy.ReductionSemantics.FPC as AdequacyFPC
import FPC.proof.Adequacy.ReductionSemantics.EndToEnd as EndToEnd

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Adequacy, reduction semantics ----------------------------------------------}

{- for a closed FPC term M (of any type), and every constant c:
   c ∈ ⟦ M ⟧ if and only if M reduces to c -}
fpc-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ R.Terminates (FPCᵣ.sem M) (o-const B k)
fpc-const-iff = AdequacyFPC.const-iff

{- and ⟦ M ⟧ is empty if and only if the reduction of M diverges -}
fpc-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → R.Diverges (FPCᵣ.sem M) ⇔ (⟦ M ⟧ ρ₀ ≃ ∅)
fpc-diverges-iff M = ⇔∘ (AdequacyFPC.diverges-iff M) ¬nonempty⇔≃∅

{- With Theorem 4.1: the compiler, observed through reduction and the X86μ
   machine -}

{- for a program of type Int, the theorem the reduction column states
   (Proposition F.3): the reduction semantics of FPC and the machine of
   X86μ terminate with the same integer, or both diverge -}

end-to-end-x86-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → R.Terminates (FPCᵣ.sem M) (o-const Int n)
    ⇔ C.Terminates (X86μₘ.sem (compile M)) (o-const Int n)
end-to-end-x86-const = EndToEnd.end-to-end-x86-const

end-to-end-x86-diverges : ∀ (M : FPC.Tm [] (base Int))
  → R.Diverges (FPCᵣ.sem M) ⇔ C.Diverges (X86μₘ.sem (compile M))
end-to-end-x86-diverges = EndToEnd.end-to-end-x86-diverges
