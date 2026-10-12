{-

  A reduction semantics for Clos3 (call by value, left to right), by
  substitution. A closure clos-op n ⦅ ∁ (x y. N) , fv₁ , ... , fvₙ ⦆
  evaluates its free variables fv₁ ... fvₙ left to right, and is a value
  once they are values. Applying it to a value W substitutes W for y and
  the tuple of the values of the free variables for x in N, which can see
  no other variable. See the design note in Smallstep.agda.

-}

module Compiler.Reduction.Clos3 where

open import Framework.Primitives using (Int)
open import Compiler.Lang.Prim using (Prim; Out; int; bool)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos3
open import Compiler.Observation
open import Compiler.Reduction.Smallstep using (Machine; Red; val; wrong; to; step-in; reduction)
open import Framework.Syntax.Subst Op sig using (_[_]; sub; ids)
open import Framework.ListUtil using (proj; args→list)

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; replicate; reverse)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (zero; suc)

obs : AST → Obs
obs-args : ∀ {n} → Args (replicate n ■) → List Obs
obs (clos-op n ⦅ _ ⦆) = o-fun
obs (lit B k ⦅ _ ⦆) = o-const B k
obs (tuple n ⦅ as ⦆) = o-tuple (obs-args as)
obs (inl-op ⦅ M ,, Nil ⦆) = o-inl (obs M)
obs (inr-op ⦅ M ,, Nil ⦆) = o-inr (obs M)
obs _ = o-wrong
obs-args {zero} Nil = []
obs-args {suc n} (M ,, as) = obs M ∷ obs-args as

ret? : Maybe AST → Red AST
ret? (just M) = to M
ret? nothing = wrong

{- the term of a primitive's result -}
out : Out → AST
out (int n) = lit Int n ⦅ Nil ⦆
out (bool true) = inl-op ⦅ tuple 0 ⦅ Nil ⦆ ,, Nil ⦆
out (bool false) = inr-op ⦅ tuple 0 ⦅ Nil ⦆ ,, Nil ⦆

{- the redexes, once the operands are values (r reduces the argument) -}
app? : AST → Red AST → AST → Red AST
app? F@(clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) r M =
  step-in (λ M' → app ⦅ F ,, M' ,, Nil ⦆) r (to (sub (M • tuple n ⦅ fvs ⦆ • ids) N))
app? _ _ _ = wrong

get? : ∀ {n} → Fin n → AST → Red AST
get? i (tuple n ⦅ as ⦆) = ret? (proj i (args→list as))
get? i _ = wrong

case? : AST → AST → AST → Red AST
case? (inl-op ⦅ V ,, Nil ⦆) M N = to (M [ V ])
case? (inr-op ⦅ V ,, Nil ⦆) M N = to (N [ V ])
case? _ M N = wrong

prim? : Prim → AST → AST → Red AST
prim? p V W = ret? (map out (δ? p (obs V) (obs W)))

red : AST → Red AST
red-args : ∀ {n} → Args (replicate n ■) → Red (Args (replicate n ■))

red (` x) = wrong
red (clos-op n ⦅ cons (clear N) fvs ⦆) =
  step-in (λ fvs' → clos-op n ⦅ cons (clear N) fvs' ⦆) (red-args fvs) val
red (app ⦅ L ,, M ,, Nil ⦆) = step-in (λ L' → app ⦅ L' ,, M ,, Nil ⦆) (red L) (app? L (red M) M)
red (lit B k ⦅ Nil ⦆) = val
red (tuple n ⦅ as ⦆) = step-in (λ as' → tuple n ⦅ as' ⦆) (red-args as) val
red (get i ⦅ M ,, Nil ⦆) = step-in (λ M' → get i ⦅ M' ,, Nil ⦆) (red M) (get? i M)
red (inl-op ⦅ M ,, Nil ⦆) = step-in (λ M' → inl-op ⦅ M' ,, Nil ⦆) (red M) val
red (inr-op ⦅ M ,, Nil ⦆) = step-in (λ M' → inr-op ⦅ M' ,, Nil ⦆) (red M) val
red (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
  step-in (λ L' → case-op ⦅ L' ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (red L) (case? L M N)
red (prim p ⦅ L ,, M ,, Nil ⦆) =
  step-in (λ L' → prim p ⦅ L' ,, M ,, Nil ⦆) (red L)
    (step-in (λ M' → prim p ⦅ L ,, M' ,, Nil ⦆) (red M) (prim? p L M))

red-args {zero} Nil = val
red-args {suc n} (M ,, as) =
  step-in (λ M' → M' ,, as) (red M) (step-in (λ as' → M ,, as') (red-args as) val)

sem : AST → Machine
sem M = reduction obs red M
