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
  is defined for ISWIM and Clos2, the languages of the first two passes,
  simplify and enclose.

  To read them: the languages (Language/), the passes (Compiler/), the
  semantics (Semantics/GraphErr/) and the domain and operators they are
  built from (Framework/GraphModel/{Domain,OpsBase,ErrorOps}.agda); and,
  for adequacy, the ISWIM machine (Semantics/CEK/ISWIM.agda) and the
  observations (Semantics/Observation.agda).

-}

module Theorems.GraphErrors where

open import Framework.GraphModel.SetsAsPredicates using (𝒫; ⌈_⌉; _∈_; _≃_)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.Domain using (Value; ω)

import Language.ISWIM as ISWIM
open import Compiler.Simplify using (simplify)
open import Compiler.Enclose using (enclose)
open import Compiler.EncloseScope using (Closed)

open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.Clos2 using () renaming (⟦_⟧ to ⟦_⟧₂)

import proof.Correctness.GraphErr.SimplifyCorrect as SimplifyCorrect
import proof.Correctness.GraphErr.EncloseCorrect as EncloseCorrect

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
