{-

  Soundness and adequacy of the graph model with respect to the clocked
  interpreters of ISWIMμ and X86μ, and the ISWIMμ compiler's
  correctness observed through the interpreters: the public statements.
  The proofs are in Mu/proof/Adequacy/.

  The end-to-end theorem for a main program of type Int is the one the
  operational styles state (Mu/Theorems/Simulation.agda,
  Interpreter.agda and Reduction.agda: compile-x86-const and
  compile-x86-diverges), here from the graph model's
  (Mu/Theorems/Denotational.agda) through adequacy, about the same
  interpreters as Mu/Theorems/Interpreter.agda's.

  To read them: those of Mu/Theorems/Denotational.agda, the ISWIMμ
  interpreter (Mu/Semantics/Interp/ISWIM.agda), the X86μ interpreter
  (Mu/Semantics/Interp/X86.agda), the clocked semantics
  (Semantics/Interp/Clock.agda) and the observations
  (Semantics/Observation.agda). The X86μ statements are for the programs
  the compiler produces, so that their preconditions (in Mu/proof/) need
  not be audited.

-}

module Mu.Theorems.Adequacy where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (const)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges)
open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
open import Mu.Compiler.Pipeline using (compile-x86)
open import Mu.Theorems.Denotational using (ρ₀)
open import Mu.Semantics.Graph.ISWIM using (⟦_⟧)
open import Mu.Semantics.Graph.X86 using (⟦_⟧ₜ)
import Mu.Semantics.Interp.ISWIM as ISWIMμᵢ
import Mu.Semantics.Interp.X86 as X86μᵢ

import Mu.proof.Adequacy.ISWIM as AdequacyISWIM
import Mu.proof.Adequacy.X86 as AdequacyX86
import Mu.proof.Adequacy.EndToEnd as EndToEnd

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Relation.Nullary using (¬_)

{- The ISWIMμ interpreter, for closed programs of any type --------------------}

iswim-const-iff : ∀ {A} (M : ISWIMμ.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMμᵢ.sem M) (o-const B k)
iswim-const-iff = AdequacyISWIM.const-iff

iswim-diverges-iff : ∀ {A} (M : ISWIMμ.Tm [] A)
  → Diverges (ISWIMμᵢ.sem M) ⇔ (¬ nonempty (⟦ M ⟧ ρ₀))
iswim-diverges-iff = AdequacyISWIM.diverges-iff

{- The X86μ interpreter, for the programs compile-x86 produces ----------------}

x86-const-iff : ∀ {A} (M : ISWIMμ.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (X86μᵢ.sem (compile-x86 M)) (o-const B k)
x86-const-iff = AdequacyX86.x86-const-iff

x86-diverges-iff : ∀ {A} (M : ISWIMμ.Tm [] A)
  → Diverges (X86μᵢ.sem (compile-x86 M)) ⇔ (¬ nonempty ⟦ compile-x86 M ⟧ₜ)
x86-diverges-iff = AdequacyX86.x86-diverges-iff

{- End to end: the compiler, observed through the interpreters only ----------}

{- for a main program of type Int, the theorem of the operational styles:
   the interpreters of ISWIMμ and X86μ stop with the same constant, or
   both diverge -}

end-to-end-x86-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμᵢ.sem M) (o-const Int k) ⇔ Terminates (X86μᵢ.sem (compile-x86 M)) (o-const Int k)
end-to-end-x86-const = EndToEnd.compile-x86-const

end-to-end-x86-diverges : ∀ (M : ISWIMμ.Tm [] (base Int))
  → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile-x86 M))
end-to-end-x86-diverges = EndToEnd.compile-x86-diverges
