{-

  A CEK-style abstract machine for Imp (Language/Imp.agda), as for Clos5
  except for the frame: an expression runs in a frame of local slots,
  and both kinds of state carry it,
    eval e φ κ   evaluate e in the frame φ, then continue with κ
    ret v φ κ    return v, with the frame φ as e left it, to κ
  so the frame is threaded through the computation: an assignment is
  seen by everything after it. Values are those of the Clos5 machine.

  The operands of a simple expression are atoms, evaluated left to right
  in a step each (eval (simple (atm a)) φ κ), collecting their values in
  continuation frames (Frm) as in Clos5. A variable reads its slot of
  the frame, and errors beyond the frame. What a simple expression
  does at its start (first) and when an operand's value comes back
  (resume) does not depend on the language, and the CFG machine
  (Semantics/CEK/CFG.agda) shares it: evaluate another operand, return a value
  (or error), or call a definition.

  x := e₁; e₂ evaluates e₁ under assignK x e₂, which assigns the value to
  slot x and runs e₂; case assigns the payload to slot x and runs a
  branch. Assigning a slot beyond the frame errors.

  A call app f e a checks, after its three operands, that f is code k,
  and runs the body of definition k in a fresh frame of max(2, locals)
  slots: e in slot 0, a in slot 1, and the integer 0 in the others,
  under callK φ κ, which returns the result to κ in the caller's frame φ.
  main runs in a fresh frame of zeros. See the design note in
  Smallstep.agda.

-}

module Semantics.CEK.Imp where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
open import Language.Imp
open import Semantics.Observation
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; next?; machine)
open import Semantics.CEK.Values using (Val; code; pair; const; tup; inl; inr; obs; prim?) public
open import Framework.ListUtil using (_‼_; proj)

open import Data.Fin using (Fin)
open import Data.Integer using (0ℤ)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _∸_)

Frame : Set
Frame = List Val

{- the frames of a simple expression, waiting for an operand -}
data Frm : Set where
  appF : Atm → Atm → Frm       {- evaluating the code; next env, arg -}
  appE : Val → Atm → Frm       {- evaluating the environment -}
  appA : Val → Val → Frm       {- evaluating the argument -}
  pairL : Atm → Frm
  pairR : Val → Frm
  fstK sndK : Frm
  tupK : List Val → List Atm → Frm
  getK : ∀ {n} → Fin n → Frm
  inlK inrK : Frm
  primL : Prim → Atm → Frm
  primR : Prim → Val → Frm

data Cont : Set where
  halt : Cont
  frm : Frm → Cont → Cont
  caseK : ℕ → Exp → Exp → Cont → Cont  {- x := the payload; a branch -}
  assignK : ℕ → Exp → Cont → Cont      {- x := □; e₂ -}
  callK : Frame → Cont → Cont          {- return to the caller's frame -}

data State : Set where
  eval : Exp → Frame → Cont → State
  ret : Val → Frame → Cont → State

{- the value of an atom in the frame -}
atom : Frame → Atm → Maybe Val
atom φ (var x) = φ ‼ x
atom φ (lit B k) = just (const B k)
atom φ (fun-ref k) = just (code k)

{- the frame with slot x set to v, if x is in the frame -}
_[_]≔_ : Frame → ℕ → Val → Maybe Frame
[] [ x ]≔ v = nothing
(u ∷ φ) [ zero ]≔ v = just (v ∷ φ)
(u ∷ φ) [ suc x ]≔ v = map (u ∷_) (φ [ x ]≔ v)

zeros : ℕ → Frame
zeros n = replicate n (const Int 0ℤ)

{- what a simple expression does next -}
data Res : Set where
  operand : Atm → Frm → Res        {- evaluate an operand, under a frame -}
  value : Maybe Val → Res         {- return a value, or error -}
  apply : ℕ → Val → Val → Res     {- call definition k with e and a -}

tuple-next : List Val → List Atm → Res
tuple-next vs [] = value (just (tup (reverse vs)))
tuple-next vs (a ∷ as) = operand a (tupK vs as)

{- at its start -}
first : Frame → Simple → Res
first φ (atm a) = value (atom φ a)
first φ (app f e a) = operand f (appF e a)
first φ (pair a b) = operand a (pairL b)
first φ (fst a) = operand a fstK
first φ (snd a) = operand a sndK
first φ (tuple as) = tuple-next [] as
first φ (get i a) = operand a (getK i)
first φ (inl a) = operand a inlK
first φ (inr a) = operand a inrK
first φ (prim p a b) = operand a (primL p b)

{- when the value of an operand comes back to its frame -}
resume : Val → Frm → Res
resume f (appF e a) = operand e (appE f a)
resume e (appE f a) = operand a (appA f e)
resume a (appA (code k) e) = apply k e a
resume a (appA _ e) = value nothing
resume v (pairL b) = operand b (pairR v)
resume w (pairR v) = value (just (pair v w))
resume (pair v w) fstK = value (just v)
resume _ fstK = value nothing
resume (pair v w) sndK = value (just w)
resume _ sndK = value nothing
resume v (tupK vs as) = tuple-next (v ∷ vs) as
resume (tup vs) (getK i) = value (proj i vs)
resume _ (getK i) = value nothing
resume v inlK = value (just (inl v))
resume v inrK = value (just (inr v))
resume v (primL p b) = operand b (primR p v)
resume w (primR p v) = value (prim? p v w)

ret? : Maybe Val → Frame → Cont → Next State
ret? mv φ κ = next? o-error (λ v → ret v φ κ) mv

{- run e in the frame, if there is one -}
goto : Maybe Frame → Exp → Cont → Next State
goto (just φ) e κ = next (eval e φ κ)
goto nothing e κ = stop o-error

{- run a body, if there is one, in a fresh frame with e and a; the caller's
   frame is φ -}
call : Maybe Body → Val → Val → Frame → Cont → Next State
call (just (body n b)) e a φ κ = next (eval b (e ∷ a ∷ zeros (n ∸ 2)) (callK φ κ))
call nothing e a φ κ = stop o-error

{- the machine for a program with global definitions ds -}
res : List Body → Res → Frame → Cont → Next State
res ds (operand a f) φ κ = next (eval (simple (atm a)) φ (frm f κ))
res ds (value mv) φ κ = ret? mv φ κ
res ds (apply k e a) φ κ = call (global ds k) e a φ κ

step : List Body → State → Next State
step ds (eval (simple s) φ κ) = res ds (first φ s) φ κ
step ds (eval (case a x e₁ e₂) φ κ) = next (eval (simple (atm a)) φ (caseK x e₁ e₂ κ))
step ds (eval (assign x e₁ e₂) φ κ) = next (eval e₁ φ (assignK x e₂ κ))
step ds (ret v φ halt) = stop (obs v)
step ds (ret v φ (frm f κ)) = res ds (resume v f) φ κ
step ds (ret (inl v) φ (caseK x e₁ e₂ κ)) = goto (φ [ x ]≔ v) e₁ κ
step ds (ret (inr v) φ (caseK x e₁ e₂ κ)) = goto (φ [ x ]≔ v) e₂ κ
step ds (ret _ φ (caseK x e₁ e₂ κ)) = stop o-error
step ds (ret v φ (assignK x e κ)) = goto (φ [ x ]≔ v) e κ
step ds (ret v φ (callK φ' κ)) = next (ret v φ' κ)

{- a program starts with its main body, in a frame of zeros -}
sem : Program → Machine
sem (program ds (body n e)) = machine State (step ds) (eval e (zeros n) halt)
