{-

  Examples of simplify (Compiler/Simplify.agda).

-}

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Language.ISWIM
open import Compiler.Simplify using (simplify)
open import Compiler.Enclose using (enclose)
import Language.Clos2 as L2
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; !_,,_; Nil)

open import Data.Fin using (zero; suc)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module proof.Compiler.Examples.SimplifyExample where

n : ∀ k → AST
n k = lit Int (+ k) ⦅ Nil ⦆

{- constant folding: 3 - 1 is 2 -}
fold : simplify (prim sub ⦅ n 3 ,, n 1 ,, Nil ⦆) ≡ n 2
fold = refl

{- a case on a known injection: case (1 = 1) of _. 10 | _. 20 is 10 -}
if-true : simplify (case-op ⦅ prim eq ⦅ n 1 ,, n 1 ,, Nil ⦆ ,, ⟩ n 10 ,, ⟩ n 20 ,, Nil ⦆) ≡ n 10
if-true = refl

{- β on a small value, then folding: (λ x. x - 1) 3 is 2 -}
beta : simplify (app ⦅ lam ⦅ ⟩ prim sub ⦅ ` 0 ,, n 1 ,, Nil ⦆ ,, Nil ⦆ ,, n 3 ,, Nil ⦆) ≡ n 2
beta = refl

{- a dead binding of a small value: (λ x. 5) 7 is 5 -}
dead : simplify (app ⦅ lam ⦅ ⟩ n 5 ,, Nil ⦆ ,, n 7 ,, Nil ⦆) ≡ n 5
dead = refl

{- copy propagation under a binder: λ z. (λ x. x) z is λ z. z -}
copy : simplify (lam ⦅ ⟩ app ⦅ lam ⦅ ⟩ ` 0 ,, Nil ⦆ ,, ` 0 ,, Nil ⦆ ,, Nil ⦆) ≡ lam ⦅ ⟩ ` 0 ,, Nil ⦆
copy = refl

{- a let of a small value is substituted, like β:  let x = 3 in x - 1  is 2 -}
let-in : AST → AST → AST
let-in M N = let-op ⦅ M ,, ⟩ N ,, Nil ⦆

source-let : simplify (let-in (n 3) (prim sub ⦅ ` 0 ,, n 1 ,, Nil ⦆)) ≡ n 2
source-let = refl

{- a tuple holding a function is not duplicated, but it is known:
     (λ p. get 1 p) ⟨λ y. y, 3⟩  is  let p = ⟨λ y. y, 3⟩ in 3 -}
id : AST
id = lam ⦅ ⟩ ` 0 ,, Nil ⦆

pair : AST
pair = tuple 2 ⦅ id ,, n 3 ,, Nil ⦆

known-tuple : simplify (app ⦅ lam ⦅ ⟩ get {2} (suc zero) ⦅ ` 0 ,, Nil ⦆ ,, Nil ⦆ ,, pair ,, Nil ⦆)
  ≡ let-in pair (n 3)
known-tuple = refl

{- an operand that is not a value keeps its binding, and its evaluation,
   as a let:  λ g. (λ x. 5) (g 1)  is  λ g. let x = g 1 in 5 -}
effect : simplify (lam ⦅ ⟩ app ⦅ lam ⦅ ⟩ n 5 ,, Nil ⦆ ,, app ⦅ ` 0 ,, n 1 ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆)
  ≡ lam ⦅ ⟩ let-in (app ⦅ ` 0 ,, n 1 ,, Nil ⦆) (n 5) ,, Nil ⦆
effect = refl

{- inlining: a known function, let-bound, is inlined at its call, and
   the result folded:  let f = λ x. x - 1 in f 3  is  let f = λ x. x - 1 in 2 -}
dec : AST
dec = lam ⦅ ⟩ prim sub ⦅ ` 0 ,, n 1 ,, Nil ⦆ ,, Nil ⦆

inline : simplify (let-in dec (app ⦅ ` 0 ,, n 3 ,, Nil ⦆)) ≡ let-in dec (n 2)
inline = refl

{- a function passed to a known function is known in the inlined body:
     let dec = λ x. x - 1 in let twice = λ f. λ x. f (f x) in twice dec 5
   is 3 (the let-bound functions stay) -}
twice : AST
twice = lam ⦅ ⟩ lam ⦅ ⟩ app ⦅ ` 1 ,, app ⦅ ` 1 ,, ` 0 ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆

higher-order : simplify (let-in dec (let-in twice (app ⦅ app ⦅ ` 0 ,, ` 1 ,, Nil ⦆ ,, n 5 ,, Nil ⦆)))
  ≡ let-in dec (let-in twice (n 3))
higher-order = refl

{- an operand that is not a value stays bound by a let, and is evaluated
   before the inlined body:  λ g. let f = λ x. x - 1 in f (g 3)  is
   λ g. let f = λ x. x - 1 in let x = g 3 in x - 1 -}
inline-let-src : AST
inline-let-src = lam ⦅ ⟩ let-in dec (app ⦅ ` 0 ,, app ⦅ ` 1 ,, n 3 ,, Nil ⦆ ,, Nil ⦆) ,, Nil ⦆

inline-let : simplify inline-let-src
  ≡ lam ⦅ ⟩ let-in dec (let-in (app ⦅ ` 1 ,, n 3 ,, Nil ⦆) (prim sub ⦅ ` 0 ,, n 1 ,, Nil ⦆)) ,, Nil ⦆
inline-let = refl

{- End to end: that let stays a let through enclose, so no closure is
   allocated for it (before let, it was the call (λ x. x - 1) (g 3) of a
   new closure). Only the functions of the source, λ g and λ x. x - 1,
   become closures (with no free variables):
     clos (λ g. let f = clos (λ x. x - 1) in let x = g 3 in x - 1) -}
dec₂ : L2.AST
dec₂ = L2.prim sub L2.⦅ L2.` 0 ,, L2.lit Int (+ 1) L2.⦅ Nil ⦆ ,, Nil ⦆

clos₂ : L2.AST → L2.AST
clos₂ N = L2.clos-op 0 L2.⦅ ! L2.clear (L2.bind (L2.ast N)) ,, Nil ⦆

inline-let-enclosed : enclose (simplify inline-let-src)
  ≡ clos₂ (L2.let-op L2.⦅ clos₂ dec₂ ,,
                          ⟩ L2.let-op L2.⦅ L2.app L2.⦅ L2.` 1 ,, L2.lit Int (+ 3) L2.⦅ Nil ⦆ ,, Nil ⦆ ,, ⟩ dec₂ ,, Nil ⦆ ,, Nil ⦆)
inline-let-enclosed = refl
