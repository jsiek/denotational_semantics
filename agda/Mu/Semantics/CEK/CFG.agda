{-

  A machine for CFGμ (Mu/Language/CFG.agda), with the values, frames
  and simple expressions of the Impμ machine (Mu/Semantics/CEK/Imp.agda),
  as the CFGᵀ machine (Semantics/CEK/Typed/CFG.agda). A state runs a
  tail in a frame, with the blocks it may jump to:
    exec t φ bs κ
  One step runs a statement:
  * return s: the value of s goes to the continuation (cont);
  * seq p s t: slot k := the value of s (k the length of Δ', p : Δ' ⊑ Δ,
    forgetting the newer slots), then t;
  * goto l: block l, with the blocks older than it (block);
  * case a p l₁ l₂: slot k := the payload of the injection a, then
    block l₁ or l₂.
  A call runs the start of the definition's body in a frame of its
  argument and environment, under seqK (the caller's seq, which assigns
  the result and continues) or retK (the caller's return). A
  continuation is typed by the type of the value it takes.

-}

module Mu.Semantics.CEK.CFG where

open import Mu.Language.Type
open import Framework.Membership using (_⊑_)
open import Mu.Language.CFG
open import Framework.Lookup using (forget)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Mu.Semantics.CEK.Imp
  using (Val; code; pack; Frame; obs; choose; atom; Res; value; call; run) public

open import Data.List using (List; []; _∷_)

data Cont (Σ : List DSig) : Type → Set where
  halt : ∀ {A} → Cont Σ A
  seqK : ∀ {R Bs Δ Δ' A} → Δ' ⊑ Δ → Frame Σ Δ → Tail Σ R Bs (A ∷ Δ') → Blocks Σ R Bs → Cont Σ R → Cont Σ A
  retK : ∀ {A} → Cont Σ A → Cont Σ A

data State (Σ : List DSig) : Set where
  exec : ∀ {R Bs Δ} → Tail Σ R Bs Δ → Frame Σ Δ → Blocks Σ R Bs → Cont Σ R → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (Args s)) Σ) where

  {- run a block -}
  go : ∀ {R Δ} → Blk Σ R Δ → Frame Σ Δ → Cont Σ R → State Σ
  go (blk bs t) φ κ = exec t φ bs κ

  {- call a closure with the argument w -}
  enter : ∀ {A B} → Val Σ (A ⇒ B) → Val Σ A → Cont Σ B → Next (State Σ)
  enter (pack (code f) e) w κ = next (exec (Body.start (lookup ds f)) (w ∷ e ∷ []) (Body.blocks (lookup ds f)) κ)

  cont : ∀ {A} → Val Σ A → Cont Σ A → Next (State Σ)
  cont v halt = stop (obs v)
  cont v (seqK p φ t bs κ) = next (exec t (v ∷ forget p φ) bs κ)
  cont v (retK κ) = cont v κ

  {- the result of return s -}
  retn : ∀ {A} → Cont Σ A → Res A → Next (State Σ)
  retn κ (value v) = cont v κ
  retn κ (call f w) = enter f w (retK κ)

  {- the result of seq p s t -}
  assign : ∀ {R Bs Δ Δ' A} → Δ' ⊑ Δ → Frame Σ Δ → Tail Σ R Bs (A ∷ Δ') → Blocks Σ R Bs → Cont Σ R → Res A
    → Next (State Σ)
  assign p φ t bs κ (value v) = next (exec t (v ∷ forget p φ) bs κ)
  assign p φ t bs κ (call f w) = enter f w (seqK p φ t bs κ)

  step : State Σ → Next (State Σ)
  step (exec (return s) φ bs κ) = retn κ (run s φ)
  step (exec (seq p s t) φ bs κ) = assign p φ t bs κ (run s φ)
  step (exec (goto l) φ bs κ) = next (go (block bs l) φ κ)
  step (exec (case a p l₁ l₂) φ bs κ) =
    next (choose (atom φ a) (λ v → go (block bs l₁) (v ∷ forget p φ) κ) (λ v → go (block bs l₂) (v ∷ forget p φ) κ))

{- a program starts with the start of main, in the empty frame -}
sem : ∀ {A} → Program A → Machine
sem (program ds (body bs t)) = machine (State _) (step ds) (exec t [] bs halt)
