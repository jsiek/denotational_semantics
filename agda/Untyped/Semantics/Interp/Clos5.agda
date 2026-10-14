{-

  A clocked interpreter for Clos5 (call by value, left to right), which
  follows the CEK machine (Semantics/CEK/Clos5.agda): as for Clos4,
  except that a program runs with its table of global definitions, a
  reference fun-ref k evaluates to a code pointer (code k), and calling
  code k looks up definition k in the table, stopping with an error if there is
  none. As in Clos4, the operator is checked to be code at the call,
  after the operands and before the clock is consulted. See the design
  note in Clock.agda.

-}

module Untyped.Semantics.Interp.Clos5 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; int; bool)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_)
open import Untyped.Language.Clos5
open import Semantics.Observation
open import Framework.ListUtil using (_‼_; proj)
open import Semantics.Interp.Clock
open import Untyped.Semantics.Interp.Values
  using (Val; code; pair; const; tup; inl; inr; Env; obs; obs-list; out; prim?; project; first; second) public

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)

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
    do v ← eval ck ρ L; w ← eval ck ρ M; ret (pair v w)
  eval ck ρ (fst-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= first
  eval ck ρ (snd-op ⦅ M ,, Nil ⦆) = eval ck ρ M >>= second
  eval ck ρ (tuple n ⦅ args ⦆) = do vs ← eval-args ck ρ [] args; ret (tup (reverse vs))
  eval ck ρ (get i ⦅ M ,, Nil ⦆) = eval ck ρ M >>= project i
  eval ck ρ (inl-op ⦅ M ,, Nil ⦆) = do v ← eval ck ρ M; ret (inl v)
  eval ck ρ (inr-op ⦅ M ,, Nil ⦆) = do v ← eval ck ρ M; ret (inr v)
  eval ck ρ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = eval ck ρ L >>= branch ck ρ M N
  eval ck ρ (prim p ⦅ L ,, M ,, Nil ⦆) =
    do v ← eval ck ρ L; w ← eval ck ρ M; from-maybe (prim? p v w)
  eval ck ρ (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = do v ← eval ck ρ M; eval ck (v ∷ ρ) N

  eval-args {zero} ck ρ vs Nil = ret vs
  eval-args {suc n} ck ρ vs (M ,, args) = do v ← eval ck ρ M; eval-args ck ρ (v ∷ vs) args

  apply ck ρ M N f = do e ← eval ck ρ M; w ← eval ck ρ N; call ck (code? f) (w ∷ e ∷ [])

  {- the definition a code pointer refers to -}
  code? (code k) = global ds k
  code? _ = nothing

  call ck nothing ρ = error
  call zero (just N) ρ = timeout
  call (suc ck) (just N) ρ = eval ck ρ N

  branch ck ρ M N (inl v) = eval ck (v ∷ ρ) M
  branch ck ρ M N (inr v) = eval ck (v ∷ ρ) N
  branch ck ρ M N _ = error

{- a program starts with its main expression -}
sem : Program → Semantics
sem (program ds M) = semantics Val obs (λ ck → eval ds ck [] M)
