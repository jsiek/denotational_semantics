{-

  A CEK-style abstract machine for Clos3 (call by value, left to right).
  A closure clos-op n ⦅ ∁ (x. y. N) , fv₁ , ... , fvₙ ⦆ evaluates the
  tuple of its free variables, as a tuple fv₁ , ... , fvₙ would be (tupK),
  and then builds a closure value of N and that tuple (closK). Applying
  it runs N in the environment y, x: the argument is variable 0 and the
  tuple is variable 1, so a free variable is read by get i ⦅ ` 1 ⦆, which
  goes wrong unless the tuple has exactly n components. See the design
  note in Smallstep.agda.

-}

module Compiler.Operational.Machine.Clos3 where

open import Primitives using (Base; base-rep; Int)
open import Compiler.Lang.Prim using (Prim; Out; int; bool)
open import NewSyntaxUtil using (_,,_; ⟩_,,_)
open import Compiler.Lang.Clos3
open import Compiler.Observation
open import Compiler.Operational.Smallstep using (Machine; Next; next; stop; machine)
open import ListUtil

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing; map)

data Val : Set where
  clos : AST → Val → Val                {- body, tuple of its free variables -}
  const : (B : Base) → base-rep B → Val
  tup : List Val → Val
  inl : Val → Val
  inr : Val → Val

Env : Set
Env = List Val

data Cont : Set where
  halt : Cont
  appL : AST → Env → Cont → Cont
  appR : Val → Cont → Cont
  tupK : List Val → List AST → Env → Cont → Cont
  closK : AST → Cont → Cont             {- evaluating the tuple of free variables -}
  getK : ∀ {n} → Fin n → Cont → Cont
  inlK : Cont → Cont
  inrK : Cont → Cont
  caseK : AST → AST → Env → Cont → Cont
  primL : Prim → AST → Env → Cont → Cont   {- evaluating the first operand -}
  primR : Prim → Val → Cont → Cont         {- evaluating the second operand -}

data State : Set where
  eval : AST → Env → Cont → State
  ret : Val → Cont → State

obs : Val → Obs
obs-list : List Val → List Obs
obs (clos N v) = o-fun
obs (const B k) = o-const B k
obs (tup vs) = o-tuple (obs-list vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs-list [] = []
obs-list (v ∷ vs) = obs v ∷ obs-list vs

tuple-next : List Val → List AST → Env → Cont → State
tuple-next vs [] ρ κ = ret (tup (reverse vs)) κ
tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

{- the value of a primitive's result -}
out : Out → Val
out (int n) = const Int n
out (bool true) = inl (tup [])
out (bool false) = inr (tup [])

{- a primitive on two values, if they are integers -}
prim? : Prim → Val → Val → Maybe Val
prim? p v w = map out (δ? p (obs v) (obs w))

ret? : Maybe Val → Cont → Next State
ret? (just v) κ = next (ret v κ)
ret? nothing κ = stop o-wrong

step : State → Next State
step (eval (` x) ρ κ) = ret? (ρ ‼ x) κ
step (eval (clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) ρ κ) =
  next (tuple-next [] (args→list fvs) ρ (closK N κ))
step (eval (app ⦅ L ,, M ,, Nil ⦆) ρ κ) = next (eval L ρ (appL M ρ κ))
step (eval (lit B k ⦅ Nil ⦆) ρ κ) = next (ret (const B k) κ)
step (eval (tuple n ⦅ args ⦆) ρ κ) = next (tuple-next [] (args→list args) ρ κ)
step (eval (get i ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (getK i κ))
step (eval (inl-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inlK κ))
step (eval (inr-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inrK κ))
step (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ κ) = next (eval L ρ (caseK M N ρ κ))
step (eval (prim p ⦅ L ,, M ,, Nil ⦆) ρ κ) = next (eval L ρ (primL p M ρ κ))
step (ret v halt) = stop (obs v)
step (ret v@(clos _ _) (appL M ρ κ)) = next (eval M ρ (appR v κ))
step (ret _ (appL M ρ κ)) = stop o-wrong
step (ret w (appR (clos N v) κ)) = next (eval N (w ∷ v ∷ []) κ)
step (ret w (appR _ κ)) = stop o-wrong
step (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
step (ret v (closK N κ)) = next (ret (clos N v) κ)
step (ret (tup vs) (getK i κ)) = ret? (proj i vs) κ
step (ret _ (getK i κ)) = stop o-wrong
step (ret v (inlK κ)) = next (ret (inl v) κ)
step (ret v (inrK κ)) = next (ret (inr v) κ)
step (ret (inl v) (caseK M N ρ κ)) = next (eval M (v ∷ ρ) κ)
step (ret (inr v) (caseK M N ρ κ)) = next (eval N (v ∷ ρ) κ)
step (ret _ (caseK M N ρ κ)) = stop o-wrong
step (ret v (primL p M ρ κ)) = next (eval M ρ (primR p v κ))
step (ret w (primR p v κ)) = ret? (prim? p v w) κ

sem : AST → Machine
sem M = machine State step (eval M [] halt)
