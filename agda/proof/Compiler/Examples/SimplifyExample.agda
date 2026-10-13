{-

  Examples of simplify (Compiler/Simplify.agda).

-}

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Language.ISWIM
open import Compiler.Simplify using (simplify)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)

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

{- a tuple holding a function is not duplicated, but it is known:
     (λ p. get 1 p) ⟨λ y. y, 3⟩  is  (λ p. 3) ⟨λ y. y, 3⟩ -}
id : AST
id = lam ⦅ ⟩ ` 0 ,, Nil ⦆

pair : AST
pair = tuple 2 ⦅ id ,, n 3 ,, Nil ⦆

known-tuple : simplify (app ⦅ lam ⦅ ⟩ get {2} (suc zero) ⦅ ` 0 ,, Nil ⦆ ,, Nil ⦆ ,, pair ,, Nil ⦆)
  ≡ app ⦅ lam ⦅ ⟩ n 3 ,, Nil ⦆ ,, pair ,, Nil ⦆
known-tuple = refl

{- an operand that is not a value keeps its binding, and its evaluation:
     (λ x. 5) (id id) stays as it is -}
effect : simplify (app ⦅ lam ⦅ ⟩ n 5 ,, Nil ⦆ ,, app ⦅ id ,, id ,, Nil ⦆ ,, Nil ⦆)
  ≡ app ⦅ lam ⦅ ⟩ n 5 ,, Nil ⦆ ,, app ⦅ id ,, id ,, Nil ⦆ ,, Nil ⦆
effect = refl
