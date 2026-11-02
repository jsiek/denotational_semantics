{-

  A CEK-style abstract machine for ISWIM (call by value, left to right).
  A function value is a closure of the function's body and the whole
  environment it was created in. See the design note in Smallstep.agda.

-}

module Semantics.CEK.ISWIM where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; int; bool)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_)
open import Language.ISWIM
open import Semantics.Observation
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; next?; machine)
open import Framework.ListUtil

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing; map)

data Val : Set where
  clo : AST → List Val → Val           {- body (under one binder), environment -}
  const : (B : Base) → base-rep B → Val
  tup : List Val → Val
  inl : Val → Val
  inr : Val → Val

Env : Set
Env = List Val

data Cont : Set where
  halt : Cont
  appL : AST → Env → Cont → Cont       {- evaluating the function; next the argument -}
  appR : Val → Cont → Cont             {- evaluating the argument of this function -}
  tupK : List Val → List AST → Env → Cont → Cont   {- values so far (reversed), rest -}
  getK : ∀ {n} → Fin n → Cont → Cont
  inlK : Cont → Cont
  inrK : Cont → Cont
  caseK : AST → AST → Env → Cont → Cont
  primL : Prim → AST → Env → Cont → Cont   {- evaluating the first operand -}
  primR : Prim → Val → Cont → Cont         {- evaluating the second operand -}
  letK : AST → Env → Cont → Cont           {- evaluating the bound term; next the body -}

data State : Set where
  eval : AST → Env → Cont → State
  ret : Val → Cont → State

obs : Val → Obs
obs-list : List Val → List Obs
obs (clo N ρ) = o-fun
obs (const B k) = o-const B k
obs (tup vs) = o-tuple (obs-list vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs-list [] = []
obs-list (v ∷ vs) = obs v ∷ obs-list vs

{- evaluate the rest of a tuple's components, or build it -}
tuple-next : List Val → List AST → Env → Cont → State
tuple-next vs [] ρ κ = ret (tup (reverse vs)) κ
tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

{- return a value, if there is one -}
{- the value of a primitive's result -}
out : Out → Val
out (int n) = const Int n
out (bool true) = inl (tup [])
out (bool false) = inr (tup [])

{- a primitive on two values, if they are integers -}
prim? : Prim → Val → Val → Maybe Val
prim? p v w = map out (δ? p (obs v) (obs w))

ret? : Maybe Val → Cont → Next State
ret? mv κ = next? o-error (λ v → ret v κ) mv

step : State → Next State
step (eval (` x) ρ κ) = ret? (ρ ‼ x) κ
step (eval (lam ⦅ ⟩ N ,, Nil ⦆) ρ κ) = next (ret (clo N ρ) κ)
step (eval (app ⦅ L ,, M ,, Nil ⦆) ρ κ) = next (eval L ρ (appL M ρ κ))
step (eval (lit B k ⦅ Nil ⦆) ρ κ) = next (ret (const B k) κ)
step (eval (tuple n ⦅ args ⦆) ρ κ) = next (tuple-next [] (args→list args) ρ κ)
step (eval (get i ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (getK i κ))
step (eval (inl-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inlK κ))
step (eval (inr-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inrK κ))
step (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ κ) = next (eval L ρ (caseK M N ρ κ))
step (eval (prim p ⦅ L ,, M ,, Nil ⦆) ρ κ) = next (eval L ρ (primL p M ρ κ))
step (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ρ κ) = next (eval M ρ (letK N ρ κ))
step (ret v halt) = stop (obs v)
{- the operator is checked before the argument is evaluated, so that
   split, which takes the operator apart first, preserves errors
   (as in Clos2 and Clos3). Clos4 and Clos5 check that the operator is
   code only at the call, after all three operands, like an indirect call
   instruction: split's fst of the closure has already stopped with an error on a
   non-closure, so on its output that late check always passes -}
step (ret v@(clo _ _) (appL M ρ κ)) = next (eval M ρ (appR v κ))
step (ret _ (appL M ρ κ)) = stop o-error
step (ret w (appR (clo N ρ) κ)) = next (eval N (w ∷ ρ) κ)
step (ret w (appR _ κ)) = stop o-error
step (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
step (ret (tup vs) (getK i κ)) = ret? (proj i vs) κ
step (ret _ (getK i κ)) = stop o-error
step (ret v (inlK κ)) = next (ret (inl v) κ)
step (ret v (inrK κ)) = next (ret (inr v) κ)
step (ret (inl v) (caseK M N ρ κ)) = next (eval M (v ∷ ρ) κ)
step (ret (inr v) (caseK M N ρ κ)) = next (eval N (v ∷ ρ) κ)
step (ret _ (caseK M N ρ κ)) = stop o-error
step (ret v (primL p M ρ κ)) = next (eval M ρ (primR p v κ))
step (ret w (primR p v κ)) = ret? (prim? p v w) κ
step (ret v (letK N ρ κ)) = next (eval N (v ∷ ρ) κ)

{- a program starts in the empty environment with the empty continuation -}
sem : AST → Machine
sem M = machine State step (eval M [] halt)
