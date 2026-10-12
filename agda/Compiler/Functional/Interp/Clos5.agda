{-

  A clocked interpreter for Clos5 (call by value, left to right), which
  follows the CEK machine (Operational/Machine/Clos5.agda): as for Clos4,
  except that a program runs with its table of global definitions, a
  reference fun-ref k evaluates to a code pointer (code k), and calling
  code k looks up definition k in the table, going wrong if there is
  none. As in Clos4, the operator is checked to be code at the call,
  after the operands and before the clock is consulted. See the design
  note in Clock.agda.

-}

module Compiler.Functional.Interp.Clos5 where

open import Primitives using (Base; base-rep; Int)
open import Compiler.Lang.Prim using (Prim; Out; int; bool)
open import NewSyntaxUtil using (_,,_; ⟩_,,_)
open import Compiler.Lang.Clos5
open import Compiler.Observation
open import Compiler.Lang.ListUtil using (_‼_; proj)
open import Compiler.Functional.Clock

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)

data Val : Set where
  code : ℕ → Val                        {- a reference to a global definition -}
  pair : Val → Val → Val
  const : (B : Base) → base-rep B → Val
  tup : List Val → Val
  inl : Val → Val
  inr : Val → Val

Env : Set
Env = List Val

obs : Val → Obs
obs-list : List Val → List Obs
obs (code k) = o-fun
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

{- the interpreter for a program with global definitions ds -}
module _ (ds : List AST) where

  eval : ℕ → Env → AST → Result Val
  eval-args : ∀ {n} → ℕ → Env → List Val → Args (replicate n ■) → Result (List Val)
  apply : ℕ → Env → AST → AST → Val → Result Val
  code? : Val → Maybe AST
  call : ℕ → Maybe AST → Env → Result Val
  branch : ℕ → Env → AST → AST → Val → Result Val

  eval ck ρ (` x) = from-maybe (ρ ‼ x)
  eval ck ρ (fun-ref k ⦅ Nil ⦆) = ret (code k)
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

  apply ck ρ M N f = eval ck ρ M >>= λ e → eval ck ρ N >>= λ w → call ck (code? f) (w ∷ e ∷ [])

  {- the definition a code pointer refers to -}
  code? (code k) = global ds k
  code? _ = nothing

  call ck nothing ρ = wrong
  call zero (just N) ρ = timeout
  call (suc ck) (just N) ρ = eval ck ρ N

  branch ck ρ M N (inl v) = eval ck (v ∷ ρ) M
  branch ck ρ M N (inr v) = eval ck (v ∷ ρ) N
  branch ck ρ M N _ = wrong

{- a program starts with its main expression -}
sem : Program → Semantics
sem (program ds M) = semantics Val obs (λ ck → eval ds ck [] M)
