{-

  A machine for CFGᵀ (Language/Typed/CFG.agda), with the values, frames
  and simple expressions of the Impᵀ machine (Semantics/CEK/Typed/Imp.agda).
  A state runs a tail in a frame, with the blocks it may jump to (those
  of its body for the start of a body, and those older than block l for
  block l):
    exec t φ bs κ
  One step runs a statement:
  * return s: the value of s goes to the continuation (cont);
  * seq p s t: slot k := the value of s (k the length of Δ', p : Δ' ⊑ Δ,
    forgetting the newer slots), then t;
  * goto l: block l, with the blocks older than it (block);
  * case a p l₁ l₂: slot k := the payload of the injection a, then
    block l₁ or l₂.
  A simple expression fails or calls as in Impᵀ. A call runs the start
  of the definition's body in a frame of its argument and environment,
  under seqK (the caller's seq, which assigns the result and continues)
  or retK (the caller's return, which returns the result).

-}

module Semantics.CEK.Typed.CFG where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_)
open import Language.Typed.CFG
open import Framework.Lookup using (_!_; forget)
open import Semantics.Observation using (o-error)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Semantics.CEK.Typed.Imp
  using (Val; code; pack; Frame; obs; choose; atom; Res; value; fail; call; run) public

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)

data Cont (Σ : List ℕ) : Set where
  halt : Cont Σ
  seqK : ∀ {Bs Δ Δ'} → Δ' ⊑ Δ → Frame Σ Δ → Tail Σ Bs (Any ∷ Δ') → Blocks Σ Bs → Cont Σ → Cont Σ
  retK : Cont Σ → Cont Σ

data State (Σ : List ℕ) : Set where
  exec : ∀ {Bs Δ} → Tail Σ Bs Δ → Frame Σ Δ → Blocks Σ Bs → Cont Σ → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List ℕ} (ds : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) Σ) where

  {- run a block -}
  go : ∀ {Δ} → Blk Σ Δ → Frame Σ Δ → Cont Σ → State Σ
  go (blk bs t) φ κ = exec t φ bs κ

  {- call a closure with the argument w -}
  enter : Val Σ ⟪ fun ⟫ → Val Σ Any → Cont Σ → Next (State Σ)
  enter (pack (code f) e) w κ = next (exec (Body.start (ds ! f)) (w ∷ e ∷ []) (Body.blocks (ds ! f)) κ)

  cont : Val Σ Any → Cont Σ → Next (State Σ)
  cont v halt = stop (obs v)
  cont v (seqK p φ t bs κ) = next (exec t (v ∷ forget p φ) bs κ)
  cont v (retK κ) = cont v κ

  {- the result of return s -}
  retn : Cont Σ → Res Any → Next (State Σ)
  retn κ (value v) = cont v κ
  retn κ fail = stop o-error
  retn κ (call f w) = enter f w (retK κ)

  {- the result of seq p s t -}
  assign : ∀ {Bs Δ Δ' A} → Δ' ⊑ Δ → Frame Σ Δ → Tail Σ Bs (A ∷ Δ') → Blocks Σ Bs → Cont Σ → Res A
    → Next (State Σ)
  assign p φ t bs κ (value v) = next (exec t (v ∷ forget p φ) bs κ)
  assign p φ t bs κ fail = stop o-error
  assign p φ t bs κ (call f w) = enter f w (seqK p φ t bs κ)

  step : State Σ → Next (State Σ)
  step (exec (return s) φ bs κ) = retn κ (run s φ)
  step (exec (seq p s t) φ bs κ) = assign p φ t bs κ (run s φ)
  step (exec (goto l) φ bs κ) = next (go (block bs l) φ κ)
  step (exec (case a p l₁ l₂) φ bs κ) =
    next (choose (atom φ a) (λ v → go (block bs l₁) (v ∷ forget p φ) κ) (λ v → go (block bs l₂) (v ∷ forget p φ) κ))

{- a program starts with the start of main, in the empty frame -}
sem : Program → Machine
sem (program ds (body bs t)) = machine (State _) (step ds) (exec t [] bs halt)
