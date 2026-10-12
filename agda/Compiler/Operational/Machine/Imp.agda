{-

  A CEK-style abstract machine for Imp (Lang/Imp.agda), as for Clos5
  except for the frame: an expression runs in a frame of local slots,
  and both kinds of state carry it,
    eval e φ κ   evaluate e in the frame φ, then continue with κ
    ret v φ κ    return v, with the frame φ as e left it, to κ
  so the frame is threaded through the computation: an assignment is
  seen by everything after it. Values are those of the Clos5 machine.

  The operands of a construct are atoms, evaluated left to right in a
  step each (eval (atm a) φ κ), collecting their values in continuation
  frames as in Clos5. A variable reads its slot of the frame, and goes
  wrong beyond the frame. x := e₁; e₂ evaluates e₁ under assignK x e₂,
  which assigns the value to slot x and runs e₂; case assigns the
  payload to slot x and runs a branch. Assigning a slot beyond the frame
  goes wrong.

  A call app f e a checks, after its three operands, that f is code k,
  and runs the body of definition k in a fresh frame of max(2, locals)
  slots: e in slot 0, a in slot 1, and the integer 0 in the others,
  under callK φ κ, which returns the result to κ in the caller's frame φ.
  main runs in a fresh frame of zeros. See the design note in
  Smallstep.agda.

-}

module Compiler.Operational.Machine.Imp where

open import Primitives using (Int)
open import Compiler.Lang.Prim using (Prim)
open import Compiler.Lang.Imp
open import Compiler.Observation
open import Compiler.Operational.Smallstep using (Machine; Next; next; stop; machine)
open import Compiler.Operational.Machine.Clos5 using (Val; code; pair; const; tup; inl; inr; obs; prim?) public
open import Compiler.Lang.ListUtil using (_‼_; proj)

open import Data.Fin using (Fin)
open import Data.Integer using (0ℤ)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _∸_)

Frame : Set
Frame = List Val

data Cont : Set where
  halt : Cont
  appF : Atm → Atm → Cont → Cont       {- evaluating the code; next env, arg -}
  appE : Val → Atm → Cont → Cont       {- evaluating the environment -}
  appA : Val → Val → Cont → Cont       {- evaluating the argument -}
  pairL : Atm → Cont → Cont
  pairR : Val → Cont → Cont
  fstK : Cont → Cont
  sndK : Cont → Cont
  tupK : List Val → List Atm → Cont → Cont
  getK : ∀ {n} → Fin n → Cont → Cont
  inlK : Cont → Cont
  inrK : Cont → Cont
  caseK : ℕ → Exp → Exp → Cont → Cont  {- x := the payload; a branch -}
  primL : Prim → Atm → Cont → Cont
  primR : Prim → Val → Cont → Cont
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

ret? : Maybe Val → Frame → Cont → Next State
ret? (just v) φ κ = next (ret v φ κ)
ret? nothing φ κ = stop o-wrong

{- run e in the frame, if there is one -}
goto : Maybe Frame → Exp → Cont → Next State
goto (just φ) e κ = next (eval e φ κ)
goto nothing e κ = stop o-wrong

tuple-next : List Val → List Atm → Frame → Cont → State
tuple-next vs [] φ κ = ret (tup (reverse vs)) φ κ
tuple-next vs (a ∷ as) φ κ = eval (atm a) φ (tupK vs as κ)

{- run a body, if there is one, in a fresh frame with e and a; the caller's
   frame is φ -}
call : Maybe Body → Val → Val → Frame → Cont → Next State
call (just (body n b)) e a φ κ = next (eval b (e ∷ a ∷ zeros (n ∸ 2)) (callK φ κ))
call nothing e a φ κ = stop o-wrong

{- the machine for a program with global definitions ds -}
step : List Body → State → Next State
step ds (eval (atm a) φ κ) = ret? (atom φ a) φ κ
step ds (eval (app f e a) φ κ) = next (eval (atm f) φ (appF e a κ))
step ds (eval (pair a b) φ κ) = next (eval (atm a) φ (pairL b κ))
step ds (eval (fst a) φ κ) = next (eval (atm a) φ (fstK κ))
step ds (eval (snd a) φ κ) = next (eval (atm a) φ (sndK κ))
step ds (eval (tuple as) φ κ) = next (tuple-next [] as φ κ)
step ds (eval (get i a) φ κ) = next (eval (atm a) φ (getK i κ))
step ds (eval (inl a) φ κ) = next (eval (atm a) φ (inlK κ))
step ds (eval (inr a) φ κ) = next (eval (atm a) φ (inrK κ))
step ds (eval (prim p a b) φ κ) = next (eval (atm a) φ (primL p b κ))
step ds (eval (case a x e₁ e₂) φ κ) = next (eval (atm a) φ (caseK x e₁ e₂ κ))
step ds (eval (assign x e₁ e₂) φ κ) = next (eval e₁ φ (assignK x e₂ κ))
step ds (ret v φ halt) = stop (obs v)
step ds (ret f φ (appF e a κ)) = next (eval (atm e) φ (appE f a κ))
step ds (ret e φ (appE f a κ)) = next (eval (atm a) φ (appA f e κ))
step ds (ret a φ (appA (code k) e κ)) = call (global ds k) e a φ κ
step ds (ret a φ (appA _ e κ)) = stop o-wrong
step ds (ret v φ (pairL b κ)) = next (eval (atm b) φ (pairR v κ))
step ds (ret w φ (pairR v κ)) = next (ret (pair v w) φ κ)
step ds (ret (pair v w) φ (fstK κ)) = next (ret v φ κ)
step ds (ret _ φ (fstK κ)) = stop o-wrong
step ds (ret (pair v w) φ (sndK κ)) = next (ret w φ κ)
step ds (ret _ φ (sndK κ)) = stop o-wrong
step ds (ret v φ (tupK vs as κ)) = next (tuple-next (v ∷ vs) as φ κ)
step ds (ret (tup vs) φ (getK i κ)) = ret? (proj i vs) φ κ
step ds (ret _ φ (getK i κ)) = stop o-wrong
step ds (ret v φ (inlK κ)) = next (ret (inl v) φ κ)
step ds (ret v φ (inrK κ)) = next (ret (inr v) φ κ)
step ds (ret (inl v) φ (caseK x e₁ e₂ κ)) = goto (φ [ x ]≔ v) e₁ κ
step ds (ret (inr v) φ (caseK x e₁ e₂ κ)) = goto (φ [ x ]≔ v) e₂ κ
step ds (ret _ φ (caseK x e₁ e₂ κ)) = stop o-wrong
step ds (ret v φ (primL p b κ)) = next (eval (atm b) φ (primR p v κ))
step ds (ret w φ (primR p v κ)) = ret? (prim? p v w) φ κ
step ds (ret v φ (assignK x e κ)) = goto (φ [ x ]≔ v) e κ
step ds (ret v φ (callK φ' κ)) = next (ret v φ' κ)

{- a program starts with its main body, in a frame of zeros -}
sem : Program → Machine
sem (program ds (body n e)) = machine State (step ds) (eval e (zeros n) halt)
