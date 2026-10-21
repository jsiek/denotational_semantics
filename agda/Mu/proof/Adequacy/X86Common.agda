{-

  Shared by the soundness and adequacy proofs for the X86μ interpreter
  (see Mu/proof/Adequacy/X86.agda), as Mu/proof/Adequacy/CEK/X86Common.agda
  is for the X86μ machine: how the open closure is related to its slot
  (OpR). The interpreter keeps the types η of its environment and the
  environment, which are those of the closure in the slot.

-}

module Mu.proof.Adequacy.X86Common where

open import Mu.Language.Type
open import Mu.Language.X86 using (DSig; Open; opened)
open import Mu.Semantics.Interp.Clos5 using (module Vals)
open import Mu.Semantics.Interp.X86 using (Opened; size; env-of)
open import Mu.Framework.AllUtil using (lookup)

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)

{- the open closure is that of its slot: η and the environment are its own -}
data OpR {Σ : List DSig} {Δ} (φ : Vals.Env Σ Δ) : (O : Maybe (Open Δ)) (η : Ctx) → Opened Σ η O → Set where
  none : ∀ {η} → OpR φ nothing η tt
  agree : ∀ {A B} {x : Δ ∋ A ⇒ B} → OpR φ (just (opened x)) (size (lookup φ x)) (env-of (lookup φ x))
