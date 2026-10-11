{-

  Examples of remove complex operands (Compile/RCO.agda).

-}

open import Primitives using (Int)
open import Compiler.Lang.Prim using (sub; eq)
open import Compiler.Lang.Clos5
open import Compiler.Compile.RCO using (rco)
open import NewSyntaxUtil using (_,,_; ⟩_,,_; Nil)

open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Compiler.Compile.Examples.RCOExample where

one : AST
one = lit Int (+ 1) ⦅ Nil ⦆

{- an application as delay makes it, in a context with y as variable 0:
     let c = y in app (fst c) (snd c) (y - 1) -}
call : AST
call = let-op ⦅ ` 0 ,,
         ⟩ app ⦅ fst-op ⦅ ` 0 ,, Nil ⦆ ,, snd-op ⦅ ` 0 ,, Nil ⦆
               ,, prim sub ⦅ ` 1 ,, one ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆

{- the three operands are bound in order:
     let c = y in let f = fst c in let e = snd c in let a = y - 1 in app f e a
   and the atom 1 stays in place -}
call-rco : rco call
  ≡ let-op ⦅ ` 0 ,,
      ⟩ let-op ⦅ fst-op ⦅ ` 0 ,, Nil ⦆ ,,
      ⟩ let-op ⦅ snd-op ⦅ ` 1 ,, Nil ⦆ ,,
      ⟩ let-op ⦅ prim sub ⦅ ` 3 ,, one ,, Nil ⦆ ,,
      ⟩ app ⦅ ` 2 ,, ` 1 ,, ` 0 ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆
call-rco = refl

{- with x as variable 0: case (x = 1) of inl _ ⇒ x | inr z ⇒ z; the
   branches go under the let for the scrutinee -}
test : AST
test = case-op ⦅ prim eq ⦅ ` 0 ,, one ,, Nil ⦆ ,, ⟩ ` 1 ,, ⟩ ` 0 ,, Nil ⦆

test-rco : rco test
  ≡ let-op ⦅ prim eq ⦅ ` 0 ,, one ,, Nil ⦆ ,,
      ⟩ case-op ⦅ ` 0 ,, ⟩ ` 2 ,, ⟩ ` 0 ,, Nil ⦆ ,, Nil ⦆
test-rco = refl
