{-

  A CEK-style abstract machine for Clos5 (call by value, left to right),
  as for Clos4 except for code: a program runs with its table of global
  definitions, a reference fun-ref k evaluates to a code pointer (code k),
  and applying code k looks up definition k in the table, going wrong if
  there is none. As in Clos4, the operator is checked to be code only at
  the call, after all three operands. See the design note in Smallstep.agda.

  Observations: as in Clos4, code pointers and pairs (closures) are
  observed as functions (o-fun). The values, their observations and the
  primitives are in Semantics/CEK/Values.agda, shared with the machines of Imp,
  CFG and X86.

-}

module Semantics.CEK.Clos5 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; int; bool)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_)
open import Language.Clos5
open import Semantics.Observation
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Framework.ListUtil
open import Semantics.CEK.Values public

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ)

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
  primL : Prim → AST → Env → Cont → Cont   {- evaluating the first operand -}
  primR : Prim → Val → Cont → Cont         {- evaluating the second operand -}
  letK : AST → Env → Cont → Cont

data State : Set where
  eval : AST → Env → Cont → State
  ret : Val → Cont → State

tuple-next : List Val → List AST → Env → Cont → State
tuple-next vs [] ρ κ = ret (tup (reverse vs)) κ
tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

ret? : Maybe Val → Cont → Next State
ret? (just v) κ = next (ret v κ)
ret? nothing κ = stop o-wrong

{- run code, if there is any, in the environment y, x -}
call : Maybe AST → Val → Val → Cont → Next State
call (just N) w e κ = next (eval N (w ∷ e ∷ []) κ)
call nothing w e κ = stop o-wrong

{- the machine for a program with global definitions ds -}
step : List AST → State → Next State
step ds (eval (` x) ρ κ) = ret? (ρ ‼ x) κ
step ds (eval (fun-ref k ⦅ Nil ⦆) ρ κ) = next (ret (code k) κ)
step ds (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) ρ κ) = next (eval L ρ (appF M N ρ κ))
step ds (eval (lit B k ⦅ Nil ⦆) ρ κ) = next (ret (const B k) κ)
step ds (eval (pair-op ⦅ L ,, M ,, Nil ⦆) ρ κ) = next (eval L ρ (pairL M ρ κ))
step ds (eval (fst-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (fstK κ))
step ds (eval (snd-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (sndK κ))
step ds (eval (tuple n ⦅ args ⦆) ρ κ) = next (tuple-next [] (args→list args) ρ κ)
step ds (eval (get i ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (getK i κ))
step ds (eval (inl-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inlK κ))
step ds (eval (inr-op ⦅ M ,, Nil ⦆) ρ κ) = next (eval M ρ (inrK κ))
step ds (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ κ) = next (eval L ρ (caseK M N ρ κ))
step ds (eval (prim p ⦅ L ,, M ,, Nil ⦆) ρ κ) = next (eval L ρ (primL p M ρ κ))
step ds (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ρ κ) = next (eval M ρ (letK N ρ κ))
step ds (ret v halt) = stop (obs v)
step ds (ret f (appF M N ρ κ)) = next (eval M ρ (appE f N ρ κ))
step ds (ret e (appE f N ρ κ)) = next (eval N ρ (appA f e κ))
step ds (ret w (appA (code k) e κ)) = call (global ds k) w e κ
step ds (ret w (appA _ e κ)) = stop o-wrong
step ds (ret v (pairL M ρ κ)) = next (eval M ρ (pairR v κ))
step ds (ret w (pairR v κ)) = next (ret (pair v w) κ)
step ds (ret (pair v w) (fstK κ)) = next (ret v κ)
step ds (ret _ (fstK κ)) = stop o-wrong
step ds (ret (pair v w) (sndK κ)) = next (ret w κ)
step ds (ret _ (sndK κ)) = stop o-wrong
step ds (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
step ds (ret (tup vs) (getK i κ)) = ret? (proj i vs) κ
step ds (ret _ (getK i κ)) = stop o-wrong
step ds (ret v (inlK κ)) = next (ret (inl v) κ)
step ds (ret v (inrK κ)) = next (ret (inr v) κ)
step ds (ret (inl v) (caseK M N ρ κ)) = next (eval M (v ∷ ρ) κ)
step ds (ret (inr v) (caseK M N ρ κ)) = next (eval N (v ∷ ρ) κ)
step ds (ret _ (caseK M N ρ κ)) = stop o-wrong
step ds (ret v (primL p M ρ κ)) = next (eval M ρ (primR p v κ))
step ds (ret w (primR p v κ)) = ret? (prim? p v w) κ
step ds (ret v (letK N ρ κ)) = next (eval N (v ∷ ρ) κ)

{- a program starts with its main expression -}
sem : Program → Machine
sem (program ds M) = machine State (step ds) (eval M [] halt)
