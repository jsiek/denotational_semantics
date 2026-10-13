{-

  A reduction semantics for Clos5 (call by value, left to right), by
  substitution, as for Clos4 except for code: a program runs with its
  table of global definitions ds, a reference fun-ref k is a value, and
  app ⦅ L , M , N ⦆, once its three operands are values, checks that L is
  a reference to a definition of ds, and substitutes the argument N and
  the environment M for its two parameters in it. See the design note in
  Smallstep.agda.

  Observations: as in the CEK machine, code references and pairs are
  observed as functions (o-fun).

-}

module Compiler.Reduction.Clos5 where

open import Framework.Primitives using (Int)
open import Compiler.Lang.Prim using (Prim; Out; int; bool)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos5
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
obs (fun-ref k ⦅ _ ⦆) = o-fun
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
call? : Maybe AST → AST → AST → Red AST
call? (just N) E W = to (sub (W • E • ids) N)
call? nothing E W = wrong

call : List AST → AST → AST → AST → Red AST
call ds (fun-ref k ⦅ Nil ⦆) E W = call? (global ds k) E W
call ds _ E W = wrong

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

{- the reduction for a program with global definitions ds -}
red : List AST → AST → Red AST
red-args : List AST → ∀ {n} → Args (replicate n ■) → Red (Args (replicate n ■))

red ds (` x) = wrong
red ds (fun-ref k ⦅ Nil ⦆) = val
red ds (app ⦅ L ,, M ,, N ,, Nil ⦆) =
  step-in (λ L' → app ⦅ L' ,, M ,, N ,, Nil ⦆) (red ds L)
    (step-in (λ M' → app ⦅ L ,, M' ,, N ,, Nil ⦆) (red ds M)
      (step-in (λ N' → app ⦅ L ,, M ,, N' ,, Nil ⦆) (red ds N) (call ds L M N)))
red ds (lit B k ⦅ Nil ⦆) = val
red ds (pair-op ⦅ L ,, M ,, Nil ⦆) =
  step-in (λ L' → pair-op ⦅ L' ,, M ,, Nil ⦆) (red ds L)
    (step-in (λ M' → pair-op ⦅ L ,, M' ,, Nil ⦆) (red ds M) val)
red ds (fst-op ⦅ M ,, Nil ⦆) = step-in (λ M' → fst-op ⦅ M' ,, Nil ⦆) (red ds M) (fst? M)
red ds (snd-op ⦅ M ,, Nil ⦆) = step-in (λ M' → snd-op ⦅ M' ,, Nil ⦆) (red ds M) (snd? M)
red ds (tuple n ⦅ as ⦆) = step-in (λ as' → tuple n ⦅ as' ⦆) (red-args ds as) val
red ds (get i ⦅ M ,, Nil ⦆) = step-in (λ M' → get i ⦅ M' ,, Nil ⦆) (red ds M) (get? i M)
red ds (inl-op ⦅ M ,, Nil ⦆) = step-in (λ M' → inl-op ⦅ M' ,, Nil ⦆) (red ds M) val
red ds (inr-op ⦅ M ,, Nil ⦆) = step-in (λ M' → inr-op ⦅ M' ,, Nil ⦆) (red ds M) val
red ds (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
  step-in (λ L' → case-op ⦅ L' ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (red ds L) (case? L M N)
red ds (prim p ⦅ L ,, M ,, Nil ⦆) =
  step-in (λ L' → prim p ⦅ L' ,, M ,, Nil ⦆) (red ds L)
    (step-in (λ M' → prim p ⦅ L ,, M' ,, Nil ⦆) (red ds M) (prim? p L M))
red ds (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = step-in (λ M' → let-op ⦅ M' ,, ⟩ N ,, Nil ⦆) (red ds M) (to (N [ M ]))

red-args ds {zero} Nil = val
red-args ds {suc n} (M ,, as) =
  step-in (λ M' → M' ,, as) (red ds M) (step-in (λ as' → M ,, as') (red-args ds as) val)

{- a program starts with its main expression -}
sem : Program → Machine
sem (program ds M) = reduction obs (red ds) M
