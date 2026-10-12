{-

  A CEK-style abstract machine for Clos2 (call by value, left to right).
  A closure clos-op n ⦅ ∁ (x₁ ... xₙ y. N) , fv₁ , ... , fvₙ ⦆ evaluates
  its free variables fv₁ ... fvₙ left to right and builds a closure value
  of N and their values only; N cannot see the surrounding environment.
  Applying it runs N in the environment y, xₙ, ..., x₁, so the values are
  collected in reverse, as an environment. See the design note in
  Smallstep.agda.

-}

module Compiler.Operational.Machine.Clos2 where

open import Primitives using (Base; base-rep; Int)
open import Compiler.Lang.Prim using (Prim; Out; int; bool)
open import NewSigUtil using (ν-n)
open import NewSyntaxUtil using (_,,_; ⟩_,,_)
open import Compiler.Lang.Clos2
open import Compiler.Observation
open import Compiler.Operational.Smallstep using (Machine; Next; next; stop; machine)
open import ListUtil

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (zero; suc)

data Val : Set where
  clos : AST → List Val → Val           {- body, values of its free variables -}
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
  closK : AST → List Val → List AST → Env → Cont → Cont  {- body, values so far, rest -}
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
obs (clos N vs) = o-fun
obs (const B k) = o-const B k
obs (tup vs) = o-tuple (obs-list vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs-list [] = []
obs-list (v ∷ vs) = obs v ∷ obs-list vs

{- the body of a closure, under its n free variables and its parameter -}
body : ∀ n → Arg (ν-n n (ν ■)) → AST
body zero (bind (ast N)) = N
body (suc n) (bind a) = body n a

tuple-next : List Val → List AST → Env → Cont → State
tuple-next vs [] ρ κ = ret (tup (reverse vs)) κ
tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

{- evaluate the rest of a closure's free variables, or build it -}
clos-next : AST → List Val → List AST → Env → Cont → State
clos-next N vs [] ρ κ = ret (clos N vs) κ
clos-next N vs (M ∷ Ms) ρ κ = eval M ρ (closK N vs Ms ρ κ)

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
step (eval (clos-op n ⦅ cons (clear a) fvs ⦆) ρ κ) =
  next (clos-next (body n a) [] (args→list fvs) ρ κ)
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
step (ret w (appR (clos N vs) κ)) = next (eval N (w ∷ vs) κ)
step (ret w (appR _ κ)) = stop o-wrong
step (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
step (ret v (closK N vs Ms ρ κ)) = next (clos-next N (v ∷ vs) Ms ρ κ)
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
