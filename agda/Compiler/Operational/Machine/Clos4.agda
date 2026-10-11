{-

  A CEK-style abstract machine for Clos4 (call by value, left to right).
  The code of a function, fun-op ⦅ ∁ (x. y. N) ⦆, is closed, so its value
  is just N (fun N). A closure is a pair of code and the tuple of its free
  variables, taken apart by fst and snd, and app ⦅ L , M , N ⦆ evaluates
  the code L, the environment M and the argument N, then runs the code in
  the environment y, x: the argument is variable 0 and the environment
  variable 1. See the design note in Smallstep.agda.

  Observations: Obs has no pairs, and Clos4 uses a pair only to represent
  a closure (delay makes one only from a Clos3 closure), so a pair, like
  bare code, is observed as a function (o-fun), as source functions are.

-}

module Compiler.Operational.Machine.Clos4 where

open import Primitives using (Base; base-rep)
open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos4
open import Compiler.Operational.Observation
open import Compiler.Operational.Smallstep using (Semantics; Next; next; stop; machine)
open import Compiler.Operational.Machine.Common

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; replicate; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)

data Val : Set where
  fun : AST → Val                       {- code, under the environment and argument -}
  pair : Val → Val → Val
  const : (B : Base) → base-rep B → Val
  tup : List Val → Val
  inl : Val → Val
  inr : Val → Val

Env : Set
Env = List Val

data Cont : Set where
  halt : Cont
  appF : AST → AST → Env → Cont → Cont  {- evaluating the code; next env, arg -}
  appE : Val → AST → Env → Cont → Cont  {- evaluating the environment -}
  appA : Val → Val → Cont → Cont        {- evaluating the argument -}
  pairL : AST → Env → Cont → Cont
  pairR : Val → Cont → Cont
  fstK : Cont → Cont
  sndK : Cont → Cont
  tupK : List Val → List AST → Env → Cont → Cont
  getK : ∀ {n} → Fin n → Cont → Cont
  inlK : Cont → Cont
  inrK : Cont → Cont
  caseK : AST → AST → Env → Cont → Cont
  letK : AST → Env → Cont → Cont

data State : Set where
  eval : AST → Env → Cont → State
  ret : Val → Cont → State

obs : Val → Obs
obs-list : List Val → List Obs
obs (fun N) = o-fun
obs (pair v w) = o-fun
obs (const B k) = o-const B k
obs (tup vs) = o-tuple (obs-list vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs-list [] = []
obs-list (v ∷ vs) = obs v ∷ obs-list vs

args→list : ∀ {n} → Args (replicate n ■) → List AST
args→list {zero} Nil = []
args→list {suc n} (M ,, args) = M ∷ args→list args

tuple-next : List Val → List AST → Env → Cont → State
tuple-next vs [] ρ κ = ret (tup (reverse vs)) κ
tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

ret? : Maybe Val → Cont → Next State
ret? (just v) κ = next (ret v κ)
ret? nothing κ = stop o-wrong

step : State → Next State
step (eval (` x) ρ κ) = ret? (ρ ‼ x) κ
step (eval (fun-op ⦅ cons (clear (bind (bind (ast N)))) Nil ⦆) ρ κ) = next (ret (fun N) κ)
step (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) ρ κ) = next (eval L ρ (appF M N ρ κ))
step (eval (lit B k ⦅ Nil ⦆) ρ κ) = next (ret (const B k) κ)
step (eval (pair-op ⦅ L ,, M ,, Nil ⦆) ρ κ) = next (eval L ρ (pairL M ρ κ))
step (eval (fst-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (fstK κ))
step (eval (snd-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (sndK κ))
step (eval (tuple n ⦅ args ⦆) ρ κ) = next (tuple-next [] (args→list args) ρ κ)
step (eval (get i ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (getK i κ))
step (eval (inl-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inlK κ))
step (eval (inr-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inrK κ))
step (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ κ) = next (eval L ρ (caseK M N ρ κ))
step (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ρ κ) = next (eval M ρ (letK N ρ κ))
step (ret v halt) = stop (obs v)
step (ret f@(fun _) (appF M N ρ κ)) = next (eval M ρ (appE f N ρ κ))
step (ret _ (appF M N ρ κ)) = stop o-wrong
step (ret e (appE f N ρ κ)) = next (eval N ρ (appA f e κ))
step (ret w (appA (fun N) e κ)) = next (eval N (w ∷ e ∷ []) κ)
step (ret w (appA _ e κ)) = stop o-wrong
step (ret v (pairL M ρ κ)) = next (eval M ρ (pairR v κ))
step (ret w (pairR v κ)) = next (ret (pair v w) κ)
step (ret (pair v w) (fstK κ)) = next (ret v κ)
step (ret _ (fstK κ)) = stop o-wrong
step (ret (pair v w) (sndK κ)) = next (ret w κ)
step (ret _ (sndK κ)) = stop o-wrong
step (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
step (ret (tup vs) (getK i κ)) = ret? (proj i vs) κ
step (ret _ (getK i κ)) = stop o-wrong
step (ret v (inlK κ)) = next (ret (inl v) κ)
step (ret v (inrK κ)) = next (ret (inr v) κ)
step (ret (inl v) (caseK M N ρ κ)) = next (eval M (v ∷ ρ) κ)
step (ret (inr v) (caseK M N ρ κ)) = next (eval N (v ∷ ρ) κ)
step (ret _ (caseK M N ρ κ)) = stop o-wrong
step (ret v (letK N ρ κ)) = next (eval N (v ∷ ρ) κ)

sem : AST → Semantics
sem M = machine State step (eval M [] halt)
