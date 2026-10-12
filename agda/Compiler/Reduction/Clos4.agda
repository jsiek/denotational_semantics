{-

  A reduction semantics for Clos4 (call by value, left to right), by
  substitution. The code of a function, fun-op ⦅ ∁ (x. y. N) ⦆, is closed
  and is a value; a closure is a pair of code and the tuple of its free
  variables. app ⦅ L , M , N ⦆ evaluates the code L, the environment M
  and the argument N, and only then checks that L is code, like an
  indirect call instruction (as the CEK machine does), and substitutes
  the argument for y and the environment for x in its body. See the
  design note in Smallstep.agda.

  Observations: as in the CEK machine, a pair, like bare code, is
  observed as a function (o-fun).

-}

module Compiler.Reduction.Clos4 where

open import Framework.Primitives using (Int)
open import Compiler.Lang.Prim using (Prim; Out; int; bool)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos4
open import Compiler.Observation
open import Compiler.Reduction.Smallstep using (Machine; Red; val; wrong; to; step-in; reduction)
open import Framework.Syntax.Subst Op sig using (_[_]; sub; ids)
open import Framework.ListUtil using (proj; args→list)

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (zero; suc)

obs : AST → Obs
obs-args : ∀ {n} → Args (replicate n ■) → List Obs
obs (fun-op ⦅ _ ⦆) = o-fun
obs (pair-op ⦅ _ ⦆) = o-fun
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

{- the redexes, once the operands are values -}
call : AST → AST → AST → Red AST
call (fun-op ⦅ cons (clear (bind (bind (ast N)))) Nil ⦆) E W = to (sub (W • E • ids) N)
call _ E W = wrong

fst? : AST → Red AST
fst? (pair-op ⦅ V ,, W ,, Nil ⦆) = to V
fst? _ = wrong

snd? : AST → Red AST
snd? (pair-op ⦅ V ,, W ,, Nil ⦆) = to W
snd? _ = wrong

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
red (fun-op ⦅ _ ⦆) = val
red (app ⦅ L ,, M ,, N ,, Nil ⦆) =
  step-in (λ L' → app ⦅ L' ,, M ,, N ,, Nil ⦆) (red L)
    (step-in (λ M' → app ⦅ L ,, M' ,, N ,, Nil ⦆) (red M)
      (step-in (λ N' → app ⦅ L ,, M ,, N' ,, Nil ⦆) (red N) (call L M N)))
red (lit B k ⦅ Nil ⦆) = val
red (pair-op ⦅ L ,, M ,, Nil ⦆) =
  step-in (λ L' → pair-op ⦅ L' ,, M ,, Nil ⦆) (red L)
    (step-in (λ M' → pair-op ⦅ L ,, M' ,, Nil ⦆) (red M) val)
red (fst-op ⦅ M ,, Nil ⦆) = step-in (λ M' → fst-op ⦅ M' ,, Nil ⦆) (red M) (fst? M)
red (snd-op ⦅ M ,, Nil ⦆) = step-in (λ M' → snd-op ⦅ M' ,, Nil ⦆) (red M) (snd? M)
red (tuple n ⦅ as ⦆) = step-in (λ as' → tuple n ⦅ as' ⦆) (red-args as) val
red (get i ⦅ M ,, Nil ⦆) = step-in (λ M' → get i ⦅ M' ,, Nil ⦆) (red M) (get? i M)
red (inl-op ⦅ M ,, Nil ⦆) = step-in (λ M' → inl-op ⦅ M' ,, Nil ⦆) (red M) val
red (inr-op ⦅ M ,, Nil ⦆) = step-in (λ M' → inr-op ⦅ M' ,, Nil ⦆) (red M) val
red (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
  step-in (λ L' → case-op ⦅ L' ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (red L) (case? L M N)
red (prim p ⦅ L ,, M ,, Nil ⦆) =
  step-in (λ L' → prim p ⦅ L' ,, M ,, Nil ⦆) (red L)
    (step-in (λ M' → prim p ⦅ L ,, M' ,, Nil ⦆) (red M) (prim? p L M))
red (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = step-in (λ M' → let-op ⦅ M' ,, ⟩ N ,, Nil ⦆) (red M) (to (N [ M ]))

red-args {zero} Nil = val
red-args {suc n} (M ,, as) =
  step-in (λ M' → M' ,, as) (red M) (step-in (λ as' → M ,, as') (red-args as) val)

sem : AST → Machine
sem M = reduction obs red M
