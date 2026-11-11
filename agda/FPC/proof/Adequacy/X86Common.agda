{-

  Shared by the soundness and adequacy proofs for the X86μ interpreter
  (see FPC/proof/Adequacy/X86.agda), as
  FPC/proof/Adequacy/AbstractMachines/X86Common.agda is for the X86μ machine:
  how the open closure is related to its slot (OpR). The interpreter keeps the
  types η of its environment and the environment, which are those of the closure
  in the slot. The slot is initialized, as load fst requires, and stays so
  until a slot write, which closes the closure.

-}

module FPC.proof.Adequacy.X86Common where

open import FPC.Language.Type
open import FPC.Language.X86 using (DSig; Open; opened; Inits; _∈_)
open import FPC.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import FPC.Semantics.ClockedInterpreters.X86 using (Opened; size; env-of)
open import FPC.Semantics.Slots using (Slots; read)

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)

{- the open closure is that of its slot: η and the environment are its own -}
data OpR {Σ : List DSig} {Δ} {I : Inits Δ} (φ : Slots (Vals.Val Σ) Δ I)
  : (O : Maybe (Open Δ)) (η : Ctx) → Opened Σ η O → Set where
  none : ∀ {η} → OpR φ nothing η tt
  agree : ∀ {A B} {x : Δ ∋ A ⇒ B} .(i : x ∈ I)
    → OpR φ (just (opened x)) (size (read φ x i)) (env-of (read φ x i))
