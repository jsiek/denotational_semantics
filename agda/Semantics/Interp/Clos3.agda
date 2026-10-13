{-

  A clocked interpreter for Clos3 (call by value, left to right), which
  follows the CEK machine (Semantics/CEK/Clos3.agda). A closure
  clos-op n ⦅ ∁ (x. y. N) , fv₁ , ... , fvₙ ⦆ evaluates the tuple of its
  free variables and builds a closure value of N and that tuple. Applying
  it runs N in the environment y, x. See the design note in Clock.agda.

-}

module Semantics.Interp.Clos3 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; int; bool)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_)
open import Language.Clos3
open import Semantics.Observation
open import Framework.ListUtil using (_‼_; proj)
open import Semantics.Interp.Clock

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; map)
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

eval : ℕ → Env → AST → Result Val
eval-args : ∀ {n} → ℕ → Env → List Val → Args (replicate n ■) → Result (List Val)
apply : ℕ → Env → AST → Val → Result Val
call : ℕ → AST → Env → Result Val
branch : ℕ → Env → AST → AST → Val → Result Val

eval ck ρ (` x) = from-maybe (ρ ‼ x)
eval ck ρ (clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) =
  do vs ← eval-args ck ρ [] fvs; ret (clos N (tup (reverse vs)))
eval ck ρ (app ⦅ L ,, M ,, Nil ⦆) = eval ck ρ L >>= apply ck ρ M
eval ck ρ (lit B k ⦅ Nil ⦆) = ret (const B k)
eval ck ρ (tuple n ⦅ args ⦆) = do vs ← eval-args ck ρ [] args; ret (tup (reverse vs))
eval ck ρ (get i ⦅ M ,, Nil ⦆) = eval ck ρ M >>= project i
eval ck ρ (inl-op ⦅ M ,, Nil ⦆) = do v ← eval ck ρ M; ret (inl v)
eval ck ρ (inr-op ⦅ M ,, Nil ⦆) = do v ← eval ck ρ M; ret (inr v)
eval ck ρ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = eval ck ρ L >>= branch ck ρ M N
eval ck ρ (prim p ⦅ L ,, M ,, Nil ⦆) =
  do v ← eval ck ρ L; w ← eval ck ρ M; from-maybe (prim? p v w)

eval-args {zero} ck ρ vs Nil = ret vs
eval-args {suc n} ck ρ vs (M ,, args) = do v ← eval ck ρ M; eval-args ck ρ (v ∷ vs) args

apply ck ρ M (clos N v) = do w ← eval ck ρ M; call ck N (w ∷ v ∷ [])
apply ck ρ M _ = wrong

call zero N ρ = timeout
call (suc ck) N ρ = eval ck ρ N

branch ck ρ M N (inl v) = eval ck (v ∷ ρ) M
branch ck ρ M N (inr v) = eval ck (v ∷ ρ) N
branch ck ρ M N _ = wrong

sem : AST → Semantics
sem M = semantics Val obs (λ ck → eval ck [] M)
