{-

  A clocked interpreter for Imp (Lang/Imp.agda), the output of lift
  locals. An expression runs in a frame, the list of the values of its
  slots, and returns a value and the frame as it left it, so the frame
  is threaded through evaluation: x := e₁; e₂ runs e₁, assigns its value
  to slot x of the frame e₁ left, and runs e₂ in the result; case a x
  e₁ e₂ assigns the payload to slot x and runs a branch. Reading or
  assigning a slot beyond the frame goes wrong. The values are those of
  Clos5 (Interp/Clos5.agda), as are the operations on them.

  A call app f e a, with f the code pointer code k, runs the body of
  definition k in a fresh frame of max(2, locals) slots, e in slot 0, a
  in slot 1 and the integer 0 in the others, and keeps the caller's
  frame. main runs in a fresh frame of zeros. As in Clos5, the operator
  is checked to be code at the call, after the operands, and only calls
  tick the clock. See the design note in Clock.agda.

-}

module Compiler.Functional.Interp.Imp where

open import Primitives using (Int)
open import Compiler.Lang.Imp
open import Compiler.Lang.ListUtil using (_‼_)
open import Compiler.Functional.Clock
open import Compiler.Functional.Interp.Clos5
  using (Val; code; pair; const; tup; inl; inr; obs; prim?; project; first; second)

open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

Frame : Set
Frame = List Val

{- the initial value of a slot -}
zero-val : Val
zero-val = const Int (+ 0)

{- the frame with slot x assigned v, if it has slot x -}
_[_]≔_ : Frame → ℕ → Val → Maybe Frame
[] [ x ]≔ v = nothing
(u ∷ φ) [ zero ]≔ v = just (v ∷ φ)
(u ∷ φ) [ suc x ]≔ v = map (u ∷_) (φ [ x ]≔ v)

{- a value, in the frame φ -}
here : Frame → Result Val → Result (Val × Frame)
here φ r = r >>= λ v → ret (v , φ)

{- the value, without its frame -}
value : Result (Val × Frame) → Result Val
value r = r >>= λ p → ret (proj₁ p)

{- the value of an atom -}
atom : Frame → Atm → Result Val
atom φ (var x) = from-maybe (φ ‼ x)
atom φ (lit B k) = ret (const B k)
atom φ (fun-ref k) = ret (code k)

{- the values of the atoms, onto vs in reverse, as Clos5's eval-args -}
atoms : Frame → List Val → List Atm → Result (List Val)
atoms φ vs [] = ret vs
atoms φ vs (a ∷ as) = atom φ a >>= λ v → atoms φ (v ∷ vs) as

{- the interpreter for a program with global definitions ds -}
module _ (ds : List Body) where

  eval : ℕ → Frame → Exp → Result (Val × Frame)
  code? : Val → Maybe Body
  call : ℕ → Maybe Body → Val → Val → Result Val
  branch : ℕ → Frame → ℕ → Exp → Exp → Val → Result (Val × Frame)
  put : ℕ → Frame → ℕ → Val → Exp → Result (Val × Frame)

  eval ck φ (atm a) = here φ (atom φ a)
  eval ck φ (app f e a) =
    atom φ f >>= λ f → atom φ e >>= λ e → atom φ a >>= λ w → here φ (call ck (code? f) e w)
  eval ck φ (pair a b) = atom φ a >>= λ v → atom φ b >>= λ w → ret (pair v w , φ)
  eval ck φ (fst a) = atom φ a >>= λ v → here φ (first v)
  eval ck φ (snd a) = atom φ a >>= λ v → here φ (second v)
  eval ck φ (tuple as) = atoms φ [] as >>= λ vs → ret (tup (reverse vs) , φ)
  eval ck φ (get i a) = atom φ a >>= λ v → here φ (project i v)
  eval ck φ (inl a) = atom φ a >>= λ v → ret (inl v , φ)
  eval ck φ (inr a) = atom φ a >>= λ v → ret (inr v , φ)
  eval ck φ (prim p a b) = atom φ a >>= λ v → atom φ b >>= λ w → here φ (from-maybe (prim? p v w))
  eval ck φ (case a x e₁ e₂) = atom φ a >>= branch ck φ x e₁ e₂
  eval ck φ (assign x e₁ e₂) = eval ck φ e₁ >>= λ p → put ck (proj₂ p) x (proj₁ p) e₂

  {- the definition a code pointer refers to -}
  code? (code k) = global ds k
  code? _ = nothing

  call ck nothing e w = wrong
  call zero (just b) e w = timeout
  call (suc ck) (just (body n x)) e w = value (eval ck (e ∷ w ∷ replicate (n ∸ 2) zero-val) x)

  branch ck φ x e₁ e₂ (inl v) = put ck φ x v e₁
  branch ck φ x e₁ e₂ (inr v) = put ck φ x v e₂
  branch ck φ x e₁ e₂ _ = wrong

  {- x := v, then e -}
  put ck φ x v e = from-maybe (φ [ x ]≔ v) >>= λ φ' → eval ck φ' e

{- a program starts with main, in a frame of zeros -}
sem : Program → Semantics
sem (program ds (body n e)) = semantics Val obs (λ ck → value (eval ds ck (replicate n zero-val) e))
