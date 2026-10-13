{-

  A CEK-style abstract machine for CFG (Language/CFG.agda), as for Imp
  (Semantics/CEK/Imp.agda), whose values, frames of slots and simple
  expressions (Frm, first, resume) it shares. A tail runs in a frame,
  with the blocks it may jump to: those of its body for the start of a
  body, and those older than block l for block l. The states are
    exec t φ bs κ   run the tail t in the frame φ, with the blocks bs
    eval a φ κ      evaluate the operand a in the frame φ
    ret v φ κ       return v, with the frame φ, to κ
  x := s; t evaluates s under seqK x t bs, which assigns the value to slot
  x and runs t; return s evaluates s under the continuation of the body.
  goto l runs block l of bs, with the blocks older than it (block); a
  jump to a label that is not one of them goes wrong. case a x l₁ l₂
  evaluates a under caseK x l₁ l₂ bs, which assigns the payload to slot
  x and jumps to l₁ or l₂. Reading or assigning a slot beyond the frame
  goes wrong.

  A call app f e a checks, after its three operands, that f is code k,
  and runs the start of the body of definition k, with its blocks, in a
  fresh frame as in Imp, under callK φ κ, which returns the result to κ
  in the caller's frame φ (κ holds the caller's tail and blocks). main
  runs in a fresh frame of zeros. See the design note in Smallstep.agda.

-}

module Semantics.CEK.CFG where

open import Language.CFG
open import Semantics.Observation
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Semantics.CEK.Imp
  using (Val; inl; inr; obs; Frame; Frm; atom; _[_]≔_; zeros; Res; operand; value; apply; first; resume)
  public
open import Framework.ListUtil using (_‼_)

open import Data.List using (List; _∷_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _∸_)
open import Data.Product using (_×_; _,_)

data Cont : Set where
  halt : Cont
  frm : Frm → Cont → Cont
  seqK : ℕ → Tail → List Tail → Cont → Cont       {- x := □; t -}
  caseK : ℕ → ℕ → ℕ → List Tail → Cont → Cont     {- x := the payload; goto l₁ or l₂ -}
  callK : Frame → Cont → Cont                      {- return to the caller's frame -}

data State : Set where
  exec : Tail → Frame → List Tail → Cont → State
  eval : Atm → Frame → Cont → State
  ret : Val → Frame → Cont → State

{- definition k, counting from the oldest -}
global : List Body → ℕ → Maybe Body
global ds k = reverse ds ‼ k

{- run a tail, with its blocks, in the frame, if there are both -}
jump : Maybe Frame → Maybe (Tail × List Tail) → Cont → Next State
jump (just φ) (just (t , bs)) κ = next (exec t φ bs κ)
jump _ _ κ = stop o-wrong

{- run the start of a body, if there is one, in a fresh frame with e and a;
   the caller's frame is φ -}
call : Maybe Body → Val → Val → Frame → Cont → Next State
call (just (body n bs t)) e a φ κ = next (exec t (e ∷ a ∷ zeros (n ∸ 2)) bs (callK φ κ))
call nothing e a φ κ = stop o-wrong

{- the machine for a program with global definitions ds -}
res : List Body → Res → Frame → Cont → Next State
res ds (operand a f) φ κ = next (eval a φ (frm f κ))
res ds (value (just v)) φ κ = next (ret v φ κ)
res ds (value nothing) φ κ = stop o-wrong
res ds (apply k e a) φ κ = call (global ds k) e a φ κ

step : List Body → State → Next State
step ds (exec (return s) φ bs κ) = res ds (first φ s) φ κ
step ds (exec (seq x s t) φ bs κ) = res ds (first φ s) φ (seqK x t bs κ)
step ds (exec (goto l) φ bs κ) = jump (just φ) (block bs l) κ
step ds (exec (case a x l₁ l₂) φ bs κ) = next (eval a φ (caseK x l₁ l₂ bs κ))
step ds (eval a φ κ) = res ds (value (atom φ a)) φ κ
step ds (ret v φ halt) = stop (obs v)
step ds (ret v φ (frm f κ)) = res ds (resume v f) φ κ
step ds (ret v φ (seqK x t bs κ)) = jump (φ [ x ]≔ v) (just (t , bs)) κ
step ds (ret (inl v) φ (caseK x l₁ l₂ bs κ)) = jump (φ [ x ]≔ v) (block bs l₁) κ
step ds (ret (inr v) φ (caseK x l₁ l₂ bs κ)) = jump (φ [ x ]≔ v) (block bs l₂) κ
step ds (ret _ φ (caseK x l₁ l₂ bs κ)) = stop o-wrong
step ds (ret v φ (callK φ' κ)) = next (ret v φ' κ)

{- a program starts with the start of its main body, in a frame of zeros -}
sem : Program → Machine
sem (program ds (body n bs t)) = machine State (step ds) (exec t (zeros n) bs halt)
