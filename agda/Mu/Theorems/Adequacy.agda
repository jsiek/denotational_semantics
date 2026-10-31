{-

  The adequacy of the graph model for the clocked interpreters of FPC
  and X86μ: the statement of Theorem 4.5 (adequacy) of the paper, and
  the consequence the paper draws from it with Theorem 4.1, the
  theorem the operational proofs state. The proofs are in
  Mu/proof/Adequacy/.

  compile is Mu/Compiler/Pipeline.agda's. The
  X86μ statements are for the programs the compiler produces, so that
  their preconditions (in Mu/proof/) need not be audited.

  To read them: those of Mu/Theorems/GraphModel.agda, the FPC
  interpreter (Mu/Semantics/ClockedInterpreters/FPC.agda), the X86μ
  interpreter (Mu/Semantics/ClockedInterpreters/X86.agda), the clocked
  semantics (Semantics/Interp/Clock.agda) and the observations
  (Semantics/Observation.agda).

-}

module Mu.Theorems.Adequacy where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (const)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges)
open import Mu.Language.Type using (base)
import Mu.Language.FPC as FPC
open import Mu.Compiler.Pipeline using (compile)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Mu.Semantics.GraphModel.FPC using (⟦_⟧)
open import Mu.Semantics.GraphModel.X86 using (⟦_⟧ₜ)
import Mu.Semantics.ClockedInterpreters.FPC as FPCᵢ
import Mu.Semantics.ClockedInterpreters.X86 as X86μᵢ

import Mu.proof.Adequacy.FPC as AdequacyFPC
import Mu.proof.Adequacy.X86 as AdequacyX86
import Mu.proof.Adequacy.EndToEnd as EndToEnd

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Relation.Nullary using (¬_)

{- Theorem 4.5 (Adequacy) -----------------------------------------------------}

{- for a closed FPC term M (of any type), and every constant c:
   c ∈ ⟦ M ⟧ if and only if the interpreter of FPC terminates on M
   with c -}
fpc-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (FPCᵢ.sem M) (o-const B k)
fpc-const-iff = AdequacyFPC.const-iff

{- and ⟦ M ⟧ is empty if and only if the interpreter diverges on M -}
fpc-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → Diverges (FPCᵢ.sem M) ⇔ (¬ nonempty (⟦ M ⟧ ρ₀))
fpc-diverges-iff = AdequacyFPC.diverges-iff

{- the same holds for X86μ and compile M -}

x86-const-iff : ∀ {A} (M : FPC.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ compile M ⟧ₜ) ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const B k)
x86-const-iff = AdequacyX86.x86-const-iff

x86-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → Diverges (X86μᵢ.sem (compile M)) ⇔ (¬ nonempty ⟦ compile M ⟧ₜ)
x86-diverges-iff = AdequacyX86.x86-diverges-iff

{- With Theorem 4.1: the compiler, observed through the interpreters ---------}

{- for a program of type Int, the theorem the operational proofs state
   (Theorem F.1): the interpreters of FPC and X86μ terminate with the
   same integer, or both diverge -}

end-to-end-x86-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → Terminates (FPCᵢ.sem M) (o-const Int n) ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const Int n)
end-to-end-x86-const = EndToEnd.compile-const

end-to-end-x86-diverges : ∀ (M : FPC.Tm [] (base Int))
  → Diverges (FPCᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile M))
end-to-end-x86-diverges = EndToEnd.compile-diverges
