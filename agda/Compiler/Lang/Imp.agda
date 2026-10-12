module Compiler.Lang.Imp where
{-

 Imp, the imperative language after the lift-locals pass
 (Compile/LiftLocals.agda), after Essentials of Compilation.

 There are no binders. Each function body runs in its own frame of
 local slots, numbered from 0, which it declares up front; a variable
 names a slot of the current frame. let has become an assignment,
 x := e₁; e₂, and case assigns the payload of the injection to a slot
 before running a branch. The operands of every construct are atoms, as
 in monadic normal form (Lang/Mon.agda).

 Informally, the semantics: an expression runs in a frame and produces a
 value and the frame as it left it, so assignments are seen by what runs
 after them (also after the expression that contains them); reading or
 assigning a slot beyond the frame goes wrong. A call app f e a, with f
 a reference to global definition k, runs the body of definition k in a
 fresh frame of the size it declares (at least two), with the tuple of
 free variables e in slot 0 and the argument a in slot 1 and the other
 slots holding 0; the caller's frame is untouched by the call. main runs
 in a fresh frame whose slots hold 0. Otherwise the constructs behave as
 in Clos5, and the operator of app is checked to be code at the call.

-}

open import Framework.Primitives using (Base; base-rep)
open import Compiler.Lang.Prim using (Prim)
open import Framework.ListUtil using (_‼_)

open import Data.Fin using (Fin)
open import Data.List using (List; reverse)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)

data Atm : Set where
  var : ℕ → Atm                          {- a slot of the current frame -}
  lit : (B : Base) → base-rep B → Atm
  fun-ref : ℕ → Atm

{- the expressions without control flow or assignment, shared with CFG
   (Lang/CFG.agda) -}
data Simple : Set where
  atm : Atm → Simple
  app : Atm → Atm → Atm → Simple           {- code, free variables, argument -}
  pair : Atm → Atm → Simple
  fst snd : Atm → Simple
  tuple : List Atm → Simple
  get : ∀ {n} → Fin n → Atm → Simple
  inl inr : Atm → Simple
  prim : Prim → Atm → Atm → Simple

data Exp : Set where
  simple : Simple → Exp
  case : Atm → ℕ → Exp → Exp → Exp        {- case a: x := the payload; a branch -}
  assign : ℕ → Exp → Exp → Exp            {- x := e₁; e₂ -}

{- a function body or main: the number of slots of its frame -}
record Body : Set where
  constructor body
  field
    locals : ℕ
    exp : Exp

{- the global definitions are listed newest first, as in Clos5 -}
record Program : Set where
  constructor program
  field
    defs : List Body
    main : Body

{- definition k, counting from the oldest -}
global : List Body → ℕ → Maybe Body
global ds k = reverse ds ‼ k
