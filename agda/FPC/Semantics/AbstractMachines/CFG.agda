{-

  A machine for CFGμ (FPC/Language/CFG.agda), with the values, frames
  and simple expressions of the Impμ machine
  (FPC/Semantics/AbstractMachines/Imp.agda), as the CFGᵀ machine
  (ISWIM/Semantics/CEK/Typed/CFG.agda). A state runs a tail in a fixed
  frame that holds a value for each initialized slot, with the blocks it
  may jump to:
    exec t φ bs κ
  One step runs a statement:
  * return s: the value of s goes to the continuation (cont);
  * seq x s p t: slot x := the value of s, then t, in the frame without
    the slots that t does not start with (restrict p);
  * goto l: block l, with the blocks older than it (block);
  * case a x y l₁ l₂: slot x := the payload of the injection a, then
    block l₁, or slot y := the payload, then block l₂.
  A call runs the start of the definition's body in a frame of its
  argument and environment (params), under seqK (the caller's seq,
  which writes the result to its slot and continues) or retK (the
  caller's return). A continuation is typed by the type of the value it
  takes.

-}

module FPC.Semantics.AbstractMachines.CFG where

open import FPC.Language.Type
open import FPC.Language.CFG
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup)
open import FPC.Framework.Slots using (write; restrict; empty; params)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import FPC.Semantics.AbstractMachines.Imp using (Val; code; pack; Frame;
  obs; choose; atom; Res; value; call; run) public

open import Data.List using (List; []; _∷_)

data Cont (Σ : List DSig) : Type → Set where
  halt : ∀ {A} → Cont Σ A
  {- x := □, then t, in the frame φ -}
  seqK : ∀ {R Δ Bs I J A} (x : Δ ∋ A) → .(J ⊆ I ⊕ x) → Frame Σ Δ I
    → Tail Σ R Δ Bs J → Blocks Σ R Δ Bs → Cont Σ R → Cont Σ A
  retK : ∀ {A} → Cont Σ A → Cont Σ A

data State (Σ : List DSig) : Set where
  exec : ∀ {R Δ Bs I} → Tail Σ R Δ Bs I → Frame Σ Δ I → Blocks Σ R Δ Bs
    → Cont Σ R → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List DSig}
  (ds : All (λ s → Body Σ (DSig.cod s) (Args s)) Σ) where

  {- run a block -}
  go : ∀ {R Δ I} → Blk Σ R Δ I → Frame Σ Δ I → Cont Σ R → State Σ
  go (blk bs t) φ κ = exec t φ bs κ

  {- the start of a body, with its environment e and argument w -}
  start : ∀ {Δ A B} → Body Σ B (A ∷ tup Δ ∷ []) → Val Σ (tup Δ) → Val Σ A
    → Cont Σ B → State Σ
  start (body Δ p bs t) e w κ = exec t (params p e w) bs κ

  {- call a closure with the argument w -}
  enter : ∀ {A B} → Val Σ (A ⇒ B) → Val Σ A → Cont Σ B → Next (State Σ)
  enter (pack (code f) e) w κ = next (start (lookup ds f) e w κ)

  cont : ∀ {A} → Val Σ A → Cont Σ A → Next (State Σ)
  cont v halt = stop (obs v)
  cont v (seqK x p φ t bs κ) = next (exec t (restrict p (write φ x v)) bs κ)
  cont v (retK κ) = cont v κ

  {- the result of return s -}
  retn : ∀ {A} → Cont Σ A → Res A → Next (State Σ)
  retn κ (value v) = cont v κ
  retn κ (call f w) = enter f w (retK κ)

  {- the result of seq x s p t -}
  assign : ∀ {R Δ Bs I J A} (x : Δ ∋ A) → .(J ⊆ I ⊕ x) → Frame Σ Δ I
    → Tail Σ R Δ Bs J → Blocks Σ R Δ Bs → Cont Σ R → Res A
    → Next (State Σ)
  assign x p φ t bs κ (value v) =
    next (exec t (restrict p (write φ x v)) bs κ)
  assign x p φ t bs κ (call f w) = enter f w (seqK x p φ t bs κ)

  step : State Σ → Next (State Σ)
  step (exec (return s) φ bs κ) = retn κ (run s φ)
  step (exec (seq x s p t) φ bs κ) = assign x p φ t bs κ (run s φ)
  step (exec (goto l) φ bs κ) = next (go (block bs l) φ κ)
  step (exec (case a x y l₁ l₂) φ bs κ) =
    next
      (choose (atom φ a) (λ v → go (block bs l₁) (write φ x v) κ)
        (λ v → go (block bs l₂) (write φ y v) κ))

{- a program starts with the start of main, in its frame with no slot
   initialized -}
sem : ∀ {A} → Program A → Machine
sem (program ds (body Δ p bs t)) =
  machine (State _) (step ds) (exec t (empty Δ) bs halt)
