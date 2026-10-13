{-

  The monadic graph model with errors (a pilot): the public statements.
  The proofs are in proof/Semantics/GraphErrM/,
  proof/Correctness/GraphErrM/ and proof/Adequacy/GraphErrM/.

    ISWIM --simplify--> ISWIM --enclose--> Clos2

  The semantics (Semantics/GraphErrM/) is that of the graph model with
  errors (Theorems/GraphErrors.agda), with its operators built from an
  error monad on 𝒫 Value and the graph model's operators as kernels
  (Framework/GraphModel/ErrorMonad.agda). As there, a program that stops
  with an error denotes a set that holds ω, one that diverges the empty
  set, and the denotation of a closed program tells all three outcomes
  of the ISWIM machine apart.

  To read them: the languages (Language/), the passes (Compiler/), the
  semantics (Semantics/GraphErrM/) and the domain and operators they are
  built from (Framework/GraphModel/{Domain,OpsBase,Ops,ErrorMonad}.agda);
  and, for adequacy, the machine (Semantics/CEK/ISWIM.agda) and the
  observations (Semantics/Observation.agda).

-}

module Theorems.GraphErrorsMonad where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; ω; const)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.ISWIM as ISWIMₘ
import Language.ISWIM as ISWIM
open import Compiler.Simplify using (simplify)
open import Compiler.Enclose using (enclose)
open import Compiler.EncloseScope using (Closed)

open import Semantics.GraphErrM.ISWIM using (⟦_⟧)
open import Semantics.GraphErrM.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)
import proof.Correctness.GraphErrM.SimplifyCorrect as SimplifyCorrect
import proof.Correctness.GraphErrM.EncloseCorrect as EncloseCorrect
import proof.Adequacy.GraphErrM.ISWIM as Adequacy
import proof.Adequacy.GraphErrM.Simplify as SimplifyMachine

open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

{- the environment of a closed program: every variable denotes {ω} -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

simplify-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct = SimplifyCorrect.simplify-correct

enclose-correct : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct = EncloseCorrect.enclose-correct

{- adequacy for the ISWIM machine, on all three outcomes -}
iswim-error-iff : ∀ (M : ISWIM.AST) → Closed M
  → (ω ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) o-error
iswim-error-iff = Adequacy.error-iff

iswim-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) (o-const B k)
iswim-const-iff = Adequacy.const-iff

iswim-converges-iff : ∀ (M : ISWIM.AST) → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω) ⇔ Converges (Terminates (ISWIMₘ.sem M))
iswim-converges-iff = Adequacy.converges-iff

iswim-diverges-iff : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMₘ.sem M) ⇔ (∀ d → ¬ (d ∈ ⟦ M ⟧ ρ₀))
iswim-diverges-iff = Adequacy.diverges-iff

{- simplify, observed through the machine -}
simplify-error : ∀ M → Closed M → Terminates (ISWIMₘ.sem M) o-error ⇔ Terminates (ISWIMₘ.sem (simplify M)) o-error
simplify-error = SimplifyMachine.simplify-error

simplify-diverges : ∀ M → Closed M → Diverges (ISWIMₘ.sem M) ⇔ Diverges (ISWIMₘ.sem (simplify M))
simplify-diverges = SimplifyMachine.simplify-diverges
