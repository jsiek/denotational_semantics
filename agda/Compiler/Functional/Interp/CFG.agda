{-

  A clocked interpreter for CFG (Lang/CFG.agda), the output of explicate
  control. A tail runs in a frame and returns a value: x := s; t
  evaluates the simple expression s as Imp does (Interp/Imp.agda),
  assigns its value to slot x and runs t; return s returns the value of
  s; case a x l₁ l₂ assigns the payload of a to slot x and jumps to l₁
  or l₂. The values, frames and calls are those of Imp; a call runs the
  start of the callee's body in a fresh frame.

  As in Imp, only calls tick the clock (see the design note in
  Clock.agda); a jump does not. A tail runs with the blocks it may jump
  to: the start of a body with all its blocks, block l with the blocks
  older than it. A jump to l walks that list (newest first) to the block
  with l older blocks and runs it with those older blocks, so the list
  shrinks at each jump and the interpreter is structurally recursive on
  the clock, then the list of blocks, then the tail. A jump to a label
  not in the list, in particular from block l to a label ≥ l, goes
  wrong, as CFG prescribes.

-}

module Compiler.Functional.Interp.CFG where

open import Compiler.Lang.CFG
open import ListUtil using (_‼_)
open import Compiler.Functional.Clock
open import Compiler.Functional.Interp.Clos5 using (Val; code; obs)
open import Compiler.Functional.Interp.Imp using (Frame; zero-val; atom; eval-simple; inj?; set)

open import Data.List using (List; []; _∷_; reverse; replicate; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≟_)
open import Data.Sum using ([_,_])
open import Relation.Nullary using (yes; no)

{- the interpreter for a program with global definitions ds -}
module _ (ds : List Body) where

  {- the definition a code pointer refers to, counting from the oldest -}
  code? : Val → Maybe Body
  code? (code k) = reverse ds ‼ k
  code? _ = nothing

  {- t, which may jump to the blocks bs -}
  tail : ℕ → List Tail → Frame → Tail → Result Val
  {- goto l, among the blocks bs -}
  jump : ℕ → List Tail → Frame → ℕ → Result Val
  call : ℕ → Maybe Body → Val → Val → Result Val

  tail ck bs φ (return s) = eval-simple (λ f → call ck (code? f)) φ s
  tail ck bs φ (seq x s t) = do v ← eval-simple (λ f → call ck (code? f)) φ s; set φ x v λ φ' → tail ck bs φ' t
  tail ck bs φ (goto l) = jump ck bs φ l
  tail ck bs φ (case a x l₁ l₂) =
    do v ← atom φ a; inj? v >>= [ (λ w → set φ x w λ φ' → jump ck bs φ' l₁) , (λ w → set φ x w λ φ' → jump ck bs φ' l₂) ]

  jump ck [] φ l = wrong
  jump ck (t ∷ bs) φ l with l ≟ length bs
  ... | yes _ = tail ck bs φ t
  ... | no _ = jump ck bs φ l

  call ck nothing e w = wrong
  call zero (just b) e w = timeout
  call (suc ck) (just (body n bs t)) e w = tail ck bs (e ∷ w ∷ replicate (n ∸ 2) zero-val) t

{- a program starts with main, in a frame of zeros -}
sem : Program → Semantics
sem (program ds (body n bs t)) = semantics Val obs (λ ck → tail ds ck bs (replicate n zero-val) t)
