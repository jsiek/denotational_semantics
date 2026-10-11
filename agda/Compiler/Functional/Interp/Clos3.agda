{-

  A clocked interpreter for Clos3 (call by value, left to right), which
  follows the CEK machine (Operational/Machine/Clos3.agda). A closure
  clos-op n ⦅ ∁ (x. y. N) , fv₁ , ... , fvₙ ⦆ evaluates the tuple of its
  free variables and builds a closure value of N and that tuple. Applying
  it runs N in the environment y, x. See the design note in Clock.agda.

-}

module Compiler.Functional.Interp.Clos3 where

open import Primitives using (Base; base-rep)
open import NewSyntaxUtil using (_,,_; ⟩_,,_)
open import Compiler.Lang.Clos3
open import Compiler.Operational.Observation
open import Compiler.Operational.Machine.Common using (_‼_; proj)
open import Compiler.Functional.Clock

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Nat using (ℕ; zero; suc)

data Val : Set where
  clos : AST → Val → Val                {- body, tuple of its free variables -}
  const : (B : Base) → base-rep B → Val
  tup : List Val → Val
  inl : Val → Val
  inr : Val → Val

Env : Set
Env = List Val

obs : Val → Obs
obs-list : List Val → List Obs
obs (clos N v) = o-fun
obs (const B k) = o-const B k
obs (tup vs) = o-tuple (obs-list vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs-list [] = []
obs-list (v ∷ vs) = obs v ∷ obs-list vs

project : ∀ {n} → Fin n → Val → Result Val
project i (tup vs) = from-maybe (proj i vs)
project i _ = wrong

eval : ℕ → Env → AST → Result Val
eval-args : ∀ {n} → ℕ → Env → List Val → Args (replicate n ■) → Result (List Val)
apply : ℕ → Env → AST → Val → Result Val
call : ℕ → AST → Env → Result Val
branch : ℕ → Env → AST → AST → Val → Result Val

eval ck ρ (` x) = from-maybe (ρ ‼ x)
eval ck ρ (clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) =
  eval-args ck ρ [] fvs >>= λ vs → ret (clos N (tup (reverse vs)))
eval ck ρ (app ⦅ L ,, M ,, Nil ⦆) = eval ck ρ L >>= apply ck ρ M
eval ck ρ (lit B k ⦅ Nil ⦆) = ret (const B k)
eval ck ρ (tuple n ⦅ args ⦆) = eval-args ck ρ [] args >>= λ vs → ret (tup (reverse vs))
eval ck ρ (get i ⦅ M ,, Nil ⦆) = eval ck ρ M >>= project i
eval ck ρ (inl-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= λ v → ret (inl v)
eval ck ρ (inr-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= λ v → ret (inr v)
eval ck ρ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = eval ck ρ L >>= branch ck ρ M N

eval-args {zero} ck ρ vs Nil = ret vs
eval-args {suc n} ck ρ vs (M ,, args) = eval ck ρ M >>= λ v → eval-args ck ρ (v ∷ vs) args

apply ck ρ M (clos N v) = eval ck ρ M >>= λ w → call ck N (w ∷ v ∷ [])
apply ck ρ M _ = wrong

call zero N ρ = timeout
call (suc ck) N ρ = eval ck ρ N

branch ck ρ M N (inl v) = eval ck (v ∷ ρ) M
branch ck ρ M N (inr v) = eval ck (v ∷ ρ) N
branch ck ρ M N _ = wrong

sem : AST → Semantics
sem M = semantics Val obs (λ ck → eval ck [] M)
