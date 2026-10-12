{-

  An example of lift locals (Compile/LiftLocals.agda), after remove
  complex operands (Compile/RCO.agda).

-}

open import Framework.Primitives using (Int)
open import Compiler.Lang.Prim using (eq)
open import Compiler.Lang.Clos5
open import Compiler.Lang.Imp as Imp using (body; assign; case; simple; atm; var; lit)
open import Compiler.Compile.RCO using (rco; rco-mon)
open import Compiler.Compile.LiftLocals using (lift-body)
open import proof.Compiler.Compile.Examples.RCOExample using (one; test)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)

open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module proof.Compiler.Compile.Examples.LiftLocalsExample where

{- let x = 1 in case (x = 1) of inl _ ⇒ x | inr z ⇒ z -}
main : AST
main = let-op ⦅ one ,, ⟩ test ,, Nil ⦆

{- after rco:  let x = 1 in let t = (x = 1) in case t of inl _ ⇒ x | inr z ⇒ z
   x, t and z get the slots 0, 1 and 2 of a frame of three:
     x := 1; t := (x = 1); case t: z := the payload; inl ⇒ x | inr ⇒ z -}
main-lift : lift-body 0 (rco-mon main)
  ≡ body 3 (assign 0 (simple (atm (lit Int (+ 1))))
             (assign 1 (simple (Imp.prim eq (var 0) (lit Int (+ 1))))
               (case (var 1) 2 (simple (atm (var 0))) (simple (atm (var 2))))))
main-lift = refl
