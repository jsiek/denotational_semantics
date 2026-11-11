{-

  The adequacy of the graph model for the clocked interpreters of FPC
  and X86μ: the statement of the graph-model half of Proposition 5.1
  (adequacy) of the paper, and
  the consequence the paper draws from it with Theorem 4.1, the
  theorem the operational proofs state. The proofs are in
  FPC/proof/Adequacy/.

  compile is FPC/Compiler/Pipeline.agda's. The
  X86μ statements are for the programs the compiler produces, so that
  their preconditions (in FPC/proof/) need not be audited.

  To read them: those of FPC/Theorems/CorrectWrtGraphModel.agda, the FPC
  interpreter (FPC/Semantics/ClockedInterpreters/FPC.agda), the X86μ
  interpreter (FPC/Semantics/ClockedInterpreters/X86.agda), the clocked
  semantics (Semantics/Interp/Clock.agda) and the observations
  (Semantics/Observation.agda).

-}

module FPC.Theorems.GraphModelAdequateWrtClockedInterpreters where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; ∅; _≃_)
open import Framework.GraphModel.Domain using (const)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges)
open import FPC.Language.Type using (base)
import FPC.Language.FPC as FPC
open import FPC.Compiler.Pipeline using (compile)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import FPC.Semantics.GraphModel.FPC using (⟦_⟧)
open import FPC.Semantics.GraphModel.X86 using (⟦_⟧ₜ)
import FPC.Semantics.ClockedInterpreters.FPC as FPCᵢ
import FPC.Semantics.ClockedInterpreters.X86 as X86μᵢ

open import proof.Framework.Iff using (⇔∘)
open import proof.Framework.GraphModel.SetsAsPredicates using (¬nonempty⇔≃∅)
import FPC.proof.Adequacy.FPC as AdequacyFPC
import FPC.proof.Adequacy.X86 as AdequacyX86
import FPC.proof.Adequacy.EndToEnd as EndToEnd

open import Data.Integer using (ℤ)
open import Data.List using ([])

{- Proposition 5.1 (Adequacy) -------------------------------------------------}

{- for a closed FPC term M (of any type), and every constant c:
   c ∈ ⟦ M ⟧ if and only if the interpreter of FPC terminates on M
   with c -}
fpc-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (FPCᵢ.sem M) (o-const B k)
fpc-const-iff = AdequacyFPC.const-iff

{- and ⟦ M ⟧ is empty if and only if the interpreter diverges on M -}
fpc-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → Diverges (FPCᵢ.sem M) ⇔ (⟦ M ⟧ ρ₀ ≃ ∅)
fpc-diverges-iff M = ⇔∘ (AdequacyFPC.diverges-iff M) ¬nonempty⇔≃∅

{- the same holds for X86μ and compile M -}

x86-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ compile M ⟧ₜ)
    ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const B k)
x86-const-iff = AdequacyX86.x86-const-iff

x86-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → Diverges (X86μᵢ.sem (compile M)) ⇔ (⟦ compile M ⟧ₜ ≃ ∅)
x86-diverges-iff M = ⇔∘ (AdequacyX86.x86-diverges-iff M) ¬nonempty⇔≃∅

{- With Theorem 4.1: the compiler, observed through the interpreters ---------}

{- for a program of type Int, the theorem the operational proofs state
   (Proposition F.1): the interpreters of FPC and X86μ terminate with the
   same integer, or both diverge -}

end-to-end-x86-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → Terminates (FPCᵢ.sem M) (o-const Int n)
    ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const Int n)
end-to-end-x86-const = EndToEnd.compile-const

end-to-end-x86-diverges : ∀ (M : FPC.Tm [] (base Int))
  → Diverges (FPCᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile M))
end-to-end-x86-diverges = EndToEnd.compile-diverges
