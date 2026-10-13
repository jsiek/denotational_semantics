{-

  The graph model with errors (a pilot): the public statements. The
  proofs are in proof/Semantics/GraphErr/, proof/Correctness/GraphErr/
  and proof/Adequacy/GraphErr/; each theorem here is one of them, with
  its type written out, so that it can be read without opening proof/.

  The graph model with errors (Semantics/GraphErr/) is the graph model
  in which a program that stops with an error denotes a set that holds
  the error value ω (Framework/GraphModel/Domain.agda), while one that
  diverges denotes the empty set; its operators propagate ω in the
  machines' evaluation order (Framework/GraphModel/ErrorOps.agda). It
  is defined for ISWIM and Clos2–Clos4, the languages of simplify,
  enclose, concretize and delay (optimize, Clos2 → Clos2, is not yet
  proved in it).

  To read them: the languages (Language/), the passes (Compiler/), the
  semantics (Semantics/GraphErr/) and the domain and operators they are
  built from (Framework/GraphModel/{Domain,OpsBase,ErrorOps}.agda); and,
  for adequacy, the ISWIM machine (Semantics/CEK/ISWIM.agda) and the
  observations (Semantics/Observation.agda).

-}

module Theorems.GraphErrors where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; ω; const)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.ISWIM as ISWIMₘ

import Language.ISWIM as ISWIM
import Language.Clos2 as Clos2
import Language.Clos3 as Clos3
open import Compiler.Concretize using (concretize-program)
open import Compiler.Delay using (delay)
open import Framework.GraphModel.ErrorOps using (val∈)
open import Compiler.Simplify using (simplify)
open import Compiler.Enclose using (enclose)
open import Compiler.EncloseScope using (Closed)

open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Semantics.GraphErr.Clos3 using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Semantics.GraphErr.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄)

import proof.Correctness.GraphErr.SimplifyCorrect as SimplifyCorrect
import proof.Correctness.GraphErr.EncloseCorrect as EncloseCorrect
import proof.Correctness.GraphErr.ConcretizeCorrect as ConcretizeCorrect
import proof.Correctness.GraphErr.DelayPreserve as DelayCorrect
import proof.Adequacy.GraphErr.ISWIM as Adequacy
import proof.Adequacy.GraphErr.Simplify as SimplifyMachine

open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

{- The environment of a closed program: every variable denotes {ω}, an
   error, as a free variable is in the machines -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

{- Each pass preserves the meaning of a closed program exactly, errors
   included ------------------------------------------------------------------}

simplify-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = SimplifyCorrect.simplify-correct

enclose-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct = EncloseCorrect.enclose-correct

{- (optimize, Clos2 → Clos2, between enclose and concretize, is not yet
   proved in this model) -}

concretize-correct : ∀ (M : Clos2.AST) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct = ConcretizeCorrect.concretize-correct-closed

{- delay changes how closures are represented, so it is not an equation:
   it preserves and reflects an error, the constants a program produces,
   and whether it produces a value (an element other than ω) -}
delay-correct-error : ∀ (M : Clos3.AST)
  → (ω ∈ ⟦ M ⟧₃ ρ₀ → ω ∈ ⟦ delay M ⟧₄ ρ₀) × (ω ∈ ⟦ delay M ⟧₄ ρ₀ → ω ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-error = DelayCorrect.delay-correct-error

delay-correct-const : ∀ (M : Clos3.AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ delay M ⟧₄ ρ₀)
  × (const c ∈ ⟦ delay M ⟧₄ ρ₀ → const c ∈ ⟦ M ⟧₃ ρ₀)
delay-correct-const = DelayCorrect.delay-correct-const

delay-correct-val : ∀ (M : Clos3.AST)
  → (val∈ (⟦ M ⟧₃ ρ₀) → val∈ (⟦ delay M ⟧₄ ρ₀)) × (val∈ (⟦ delay M ⟧₄ ρ₀) → val∈ (⟦ M ⟧₃ ρ₀))
delay-correct-val = DelayCorrect.delay-correct-val

{- Adequacy for the ISWIM machine: the denotation of a closed program
   tells all three outcomes of its run apart ---------------------------------}

{- ω ∈ ⟦ M ⟧ ρ₀ exactly when the machine stops with an error -}
iswim-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) o-error
iswim-error-iff = Adequacy.error-iff

{- ⟦ M ⟧ ρ₀ contains the constant k exactly when the machine terminates
   with it -}
iswim-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) (o-const B k)
iswim-const-iff = Adequacy.const-iff

{- ⟦ M ⟧ ρ₀ has an element other than ω exactly when the machine
   terminates with an answer -}
iswim-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω) ⇔ Converges (Terminates (ISWIMₘ.sem M))
iswim-converges-iff = Adequacy.converges-iff

{- ⟦ M ⟧ ρ₀ is empty exactly when the machine diverges -}
iswim-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ (∀ (d : Value) → ¬ (d ∈ ⟦ M ⟧ ρ₀))
iswim-diverges-iff = Adequacy.diverges-iff

{- So, observed through the machine, simplify preserves and reflects
   errors, constants, answers and divergence -}
simplify-machine-error : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (ISWIMₘ.sem (simplify M)) o-error
simplify-machine-error = SimplifyMachine.simplify-error

simplify-machine-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (ISWIMₘ.sem (simplify M)) (o-const B k)
simplify-machine-const = SimplifyMachine.simplify-const

simplify-machine-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (ISWIMₘ.sem (simplify M)))
simplify-machine-converges = SimplifyMachine.simplify-converges

simplify-machine-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ Diverges (ISWIMₘ.sem (simplify M))
simplify-machine-diverges = SimplifyMachine.simplify-diverges
