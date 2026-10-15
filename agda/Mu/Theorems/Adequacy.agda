{-

  Soundness and adequacy of the graph model with respect to the machines
  of ISWIMμ and X86μ, and the ISWIMμ compiler's correctness observed
  through the machines: the public statements. The proofs are in
  Mu/proof/Adequacy/ (and, for the machines' never stopping with an
  error, Mu/proof/Semantics/CEK/NoError.agda).

  The end-to-end theorem for a main program of type Int is the one the
  operational styles state (Mu/Theorems/Simulation.agda,
  Interpreter.agda and Reduction.agda: compile-x86-const and
  compile-x86-diverges), here from the graph model's
  (Mu/Theorems/Denotational.agda) through adequacy.

  To read them: those of Mu/Theorems/Denotational.agda, the ISWIMμ
  machine (Mu/Semantics/CEK/ISWIM.agda), the X86μ machine
  (Mu/Semantics/CEK/X86.agda), and the observations
  (Semantics/Observation.agda). The X86μ statements are for the programs
  the compiler produces, so that their preconditions (in Mu/proof/) need
  not be audited.

-}

module Mu.Theorems.Adequacy where

open import Framework.Primitives using (base-rep; Int)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (Value; const)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.X86 as X86μ
open import Mu.Compiler.Pipeline using (compile-x86)
open import Mu.Theorems.Denotational using (ρ₀)
open import Mu.Semantics.Graph.ISWIM using (⟦_⟧)
open import Mu.Semantics.Graph.X86 using (⟦_⟧ₜ)
import Mu.Semantics.CEK.ISWIM as ISWIMμₘ
import Mu.Semantics.CEK.X86 as X86μₘ

import Mu.proof.Adequacy.ISWIM as AdequacyISWIM
import Mu.proof.Adequacy.X86 as AdequacyX86
import Mu.proof.Adequacy.EndToEnd as EndToEnd
import Mu.proof.Semantics.CEK.NoError as NoError

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Relation.Nullary using (¬_)

{- The ISWIMμ machine, for closed programs of any type ----------------------}

iswim-const-iff : ∀ {A} (M : ISWIMμ.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMμₘ.sem M) (o-const B k)
iswim-const-iff = AdequacyISWIM.const-iff

iswim-nonempty-iff : ∀ {A} (M : ISWIMμ.Tm [] A)
  → nonempty (⟦ M ⟧ ρ₀) ⇔ Converges (Terminates (ISWIMμₘ.sem M))
iswim-nonempty-iff = AdequacyISWIM.nonempty-iff

iswim-diverges-empty : ∀ {A} (M : ISWIMμ.Tm [] A) → Diverges (ISWIMμₘ.sem M)
  → ∀ (d : Value) → ¬ (d ∈ ⟦ M ⟧ ρ₀)
iswim-diverges-empty = AdequacyISWIM.diverges-empty

{- The X86μ machine, for the programs compile-x86 produces -------------------}

x86-const-iff : ∀ {A} (M : ISWIMμ.Tm [] A) {B} {k : base-rep B}
  → (const k ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (X86μₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff = AdequacyX86.x86-const-iff

x86-nonempty-iff : ∀ {A} (M : ISWIMμ.Tm [] A)
  → nonempty ⟦ compile-x86 M ⟧ₜ ⇔ Converges (Terminates (X86μₘ.sem (compile-x86 M)))
x86-nonempty-iff = AdequacyX86.x86-nonempty-iff

{- Neither machine stops with an error ---------------------------------------}

iswim-no-error : ∀ {A} (M : ISWIMμ.Tm [] A) → ¬ Terminates (ISWIMμₘ.sem M) o-error
iswim-no-error = NoError.iswim-no-error

x86-no-error : ∀ {A} (P : X86μ.Program A) → ¬ Terminates (X86μₘ.sem P) o-error
x86-no-error = NoError.x86-no-error

{- End to end: the compiler, observed through the machines only -------------}

end-to-end-x86-converges : ∀ {A} (M : ISWIMμ.Tm [] A)
  → Converges (Terminates (ISWIMμₘ.sem M)) ⇔ Converges (Terminates (X86μₘ.sem (compile-x86 M)))
end-to-end-x86-converges = EndToEnd.end-to-end-x86-converges

{- for a main program of type Int, the theorem of the operational styles:
   the machines of ISWIMμ and X86μ stop with the same constant, or both
   diverge -}

end-to-end-x86-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμₘ.sem M) (o-const Int k) ⇔ Terminates (X86μₘ.sem (compile-x86 M)) (o-const Int k)
end-to-end-x86-const = EndToEnd.end-to-end-x86-const

end-to-end-x86-diverges : ∀ (M : ISWIMμ.Tm [] (base Int))
  → Diverges (ISWIMμₘ.sem M) ⇔ Diverges (X86μₘ.sem (compile-x86 M))
end-to-end-x86-diverges = EndToEnd.end-to-end-x86-diverges
