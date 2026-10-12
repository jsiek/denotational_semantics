{-

  A clocked interpreter for Clos4 (call by value, left to right), which
  follows the CEK machine (Operational/Machine/Clos4.agda). The code of a
  function, fun-op ⦅ ∁ (x. y. N) ⦆, is closed, so its value is just N
  (fun N). app ⦅ L , M , N ⦆ evaluates the code L, the environment M
  and the argument N, then checks that L's value is code and runs it in
  the environment y, x. As in the machine, a pair, like bare code, is
  observed as a function. See the design note in Clock.agda.

-}

module Compiler.Functional.Interp.Clos4 where

open import Primitives using (Base; base-rep; Int)
open import Compiler.Lang.Prim using (Prim; Out; int; bool)
open import NewSyntaxUtil using (_,,_; ⟩_,,_)
open import Compiler.Lang.Clos4
open import Compiler.Observation
open import ListUtil using (_‼_; proj)
open import Compiler.Functional.Clock

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; map)
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

{- the value of a primitive's result; eq gives inl ⟨⟩ or inr ⟨⟩ -}
out : Out → Val
out (int n) = const Int n
out (bool true) = inl (tup [])
out (bool false) = inr (tup [])

prim? : Prim → Val → Val → Maybe Val
prim? p v w = map out (δ? p (obs v) (obs w))

project : ∀ {n} → Fin n → Val → Result Val
project i (tup vs) = from-maybe (proj i vs)
project i _ = wrong

first second : Val → Result Val
first (pair v w) = ret v
first _ = wrong
second (pair v w) = ret w
second _ = wrong

eval : ℕ → Env → AST → Result Val
eval-args : ∀ {n} → ℕ → Env → List Val → Args (replicate n ■) → Result (List Val)
{- apply code to the environment M and the argument N -}
apply : ℕ → Env → AST → AST → Val → Result Val
{- call code f, going wrong (before the clock is consulted) if f is not code -}
call : Val → ℕ → Env → Result Val
branch : ℕ → Env → AST → AST → Val → Result Val

eval ck ρ (` x) = from-maybe (ρ ‼ x)
eval ck ρ (fun-op ⦅ cons (clear (bind (bind (ast N)))) Nil ⦆) = ret (fun N)
eval ck ρ (app ⦅ L ,, M ,, N ,, Nil ⦆) = eval ck ρ L >>= apply ck ρ M N
eval ck ρ (lit B k ⦅ Nil ⦆) = ret (const B k)
eval ck ρ (pair-op ⦅ L ,, M ,, Nil ⦆) =
  eval ck ρ L >>= λ v → eval ck ρ M >>= λ w → ret (pair v w)
eval ck ρ (fst-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= first
eval ck ρ (snd-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= second
eval ck ρ (tuple n ⦅ args ⦆) = eval-args ck ρ [] args >>= λ vs → ret (tup (reverse vs))
eval ck ρ (get i ⦅ M ,, Nil ⦆) = eval ck ρ M >>= project i
eval ck ρ (inl-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= λ v → ret (inl v)
eval ck ρ (inr-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= λ v → ret (inr v)
eval ck ρ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = eval ck ρ L >>= branch ck ρ M N
eval ck ρ (prim p ⦅ L ,, M ,, Nil ⦆) =
  eval ck ρ L >>= λ v → eval ck ρ M >>= λ w → from-maybe (prim? p v w)
eval ck ρ (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = eval ck ρ M >>= λ v → eval ck (v ∷ ρ) N

eval-args {zero} ck ρ vs Nil = ret vs
eval-args {suc n} ck ρ vs (M ,, args) = eval ck ρ M >>= λ v → eval-args ck ρ (v ∷ vs) args

apply ck ρ M N f = eval ck ρ M >>= λ e → eval ck ρ N >>= λ w → call f ck (w ∷ e ∷ [])

call (fun N) zero ρ = timeout
call (fun N) (suc ck) ρ = eval ck ρ N
call _ ck ρ = wrong

branch ck ρ M N (inl v) = eval ck (v ∷ ρ) M
branch ck ρ M N (inr v) = eval ck (v ∷ ρ) N
branch ck ρ M N _ = wrong

sem : AST → Semantics
sem M = semantics Val obs (λ ck → eval ck [] M)
