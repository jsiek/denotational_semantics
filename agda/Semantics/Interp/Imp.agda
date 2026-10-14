{-

  A clocked interpreter for Imp (Language/Imp.agda), the output of lift
  locals. An expression runs in a frame, the list of the values of its
  slots, and returns a value and the frame as it left it, so the frame
  is threaded through evaluation: x := e₁; e₂ runs e₁, assigns its value
  to slot x of the frame e₁ left, and runs e₂ in the result; case a x
  e₁ e₂ assigns the payload to slot x and runs a branch. Reading or
  assigning a slot beyond the frame errors. The values are those of
  Clos5 (Semantics/Interp/Clos5.agda), as are the operations on them.

  A call app f e a, with f the code pointer code k, runs the body of
  definition k in a fresh frame of max(2, locals) slots, e in slot 0, a
  in slot 1 and the integer 0 in the others, and keeps the caller's
  frame. main runs in a fresh frame of zeros. As in Clos5, the operator
  is checked to be code at the call, after the operands, and only calls
  tick the clock. See the design note in Clock.agda.

-}

module Semantics.Interp.Imp where

open import Framework.Primitives using (Int)
open import Language.Imp
open import Framework.ListUtil using (_‼_)
open import Semantics.Interp.Clock
open import Semantics.Interp.Clos5
  using (Val; code; pair; const; tup; inl; inr; obs; prim?; project; first; second)
open import Semantics.Interp.Values using (Frame; zero-val; _[_]≔_) public

open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])

{- a value, in the frame φ -}
here : Frame → Result Val → Result (Val × Frame)
here φ r = do v ← r; ret (v , φ)

{- the value, without its frame -}
value : Result (Val × Frame) → Result Val
value r = do p ← r; ret (proj₁ p)

{- the value of an atom -}
atom : Frame → Atm → Result Val
atom φ (var x) = from-maybe (φ ‼ x)
atom φ (lit B k) = ret (const B k)
atom φ (fun-ref k) = ret (code k)

{- the values of the atoms, onto vs in reverse, as Clos5's eval-args -}
atoms : Frame → List Val → List Atm → Result (List Val)
atoms φ vs [] = ret vs
atoms φ vs (a ∷ as) = do v ← atom φ a; atoms φ (v ∷ vs) as

{- the value of a simple expression, which leaves the frame as it is;
   call f e w calls the operator f, shared with CFG (Semantics/Interp/CFG.agda) -}
eval-simple : (Val → Val → Val → Result Val) → Frame → Simple → Result Val
eval-simple call φ (atm a) = atom φ a
eval-simple call φ (app f e a) = do f ← atom φ f; e ← atom φ e; w ← atom φ a; call f e w
eval-simple call φ (pair a b) = do v ← atom φ a; w ← atom φ b; ret (pair v w)
eval-simple call φ (fst a) = atom φ a >>= first
eval-simple call φ (snd a) = atom φ a >>= second
eval-simple call φ (tuple as) = do vs ← atoms φ [] as; ret (tup (reverse vs))
eval-simple call φ (get i a) = atom φ a >>= project i
eval-simple call φ (inl a) = do v ← atom φ a; ret (inl v)
eval-simple call φ (inr a) = do v ← atom φ a; ret (inr v)
eval-simple call φ (prim p a b) = do v ← atom φ a; w ← atom φ b; from-maybe (prim? p v w)

{- the payload of an injection, on the left for inl -}
inj? : Val → Result (Val ⊎ Val)
inj? (inl v) = ret (inj₁ v)
inj? (inr v) = ret (inj₂ v)
inj? _ = error

{- x := v, then k -}
set : ∀ {A : Set} → Frame → ℕ → Val → (Frame → Result A) → Result A
set φ x v k = from-maybe (φ [ x ]≔ v) >>= k

{- the interpreter for a program with global definitions ds -}
module _ (ds : List Body) where

  {- the definition a code pointer refers to -}
  code? : Val → Maybe Body
  code? (code k) = global ds k
  code? _ = nothing

  eval : ℕ → Frame → Exp → Result (Val × Frame)
  call : ℕ → Maybe Body → Val → Val → Result Val
  put : ℕ → Frame → ℕ → Val → Exp → Result (Val × Frame)

  eval ck φ (simple s) = here φ (eval-simple (λ f → call ck (code? f)) φ s)
  eval ck φ (case a x e₁ e₂) = do v ← atom φ a; inj? v >>= [ (λ w → put ck φ x w e₁) , (λ w → put ck φ x w e₂) ]
  eval ck φ (assign x e₁ e₂) = do p ← eval ck φ e₁; put ck (proj₂ p) x (proj₁ p) e₂

  call ck nothing e w = error
  call zero (just b) e w = timeout
  call (suc ck) (just (body n x)) e w = value (eval ck (e ∷ w ∷ replicate (n ∸ 2) zero-val) x)

  put ck φ x v e = set φ x v λ φ' → eval ck φ' e

{- a program starts with main, in a frame of zeros -}
sem : Program → Semantics
sem (program ds (body n e)) = semantics Val obs (λ ck → value (eval ds ck (replicate n zero-val) e))
