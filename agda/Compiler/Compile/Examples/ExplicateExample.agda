{-

  Examples of explicate control (Compile/Explicate.agda).

-}

open import Primitives using (Int)
open import Compiler.Lang.Prim using (eq)
open import Compiler.Lang.Imp as Imp using (simple; atm; var; lit; assign)
open import Compiler.Lang.CFG
open import Compiler.Compile.Explicate using (explicate-body)

open import Data.Integer using (+_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Compiler.Compile.Examples.ExplicateExample where

{- the output of lift locals in LiftLocalsExample:
     x := 1; t := (x = 1); case t: z := the payload; inl ⇒ x | inr ⇒ z
   the branches become blocks 0 and 1 -}
main-explicate :
  explicate-body
    (Imp.body 3 (assign 0 (simple (atm (lit Int (+ 1))))
                 (assign 1 (simple (Imp.prim eq (var 0) (lit Int (+ 1))))
                   (Imp.case (var 1) 2 (simple (atm (var 0))) (simple (atm (var 2)))))))
  ≡ body 3 (return (atm (var 2)) ∷ return (atm (var 0)) ∷ [])
      (seq 0 (atm (lit Int (+ 1)))
        (seq 1 (Imp.prim eq (var 0) (lit Int (+ 1)))
          (case (var 1) 2 0 1)))
main-explicate = refl

{- a case on the right of an assignment:
     y := (case x: z := the payload; inl ⇒ 1 | inr ⇒ 2); y
   what follows the assignment becomes block 0, the join point, and the
   branches assign y and jump to it -}
join :
  explicate-body
    (Imp.body 3 (assign 1 (Imp.case (var 0) 2 (simple (atm (lit Int (+ 1))))
                                               (simple (atm (lit Int (+ 2)))))
                 (simple (atm (var 1)))))
  ≡ body 3 (seq 1 (atm (lit Int (+ 2))) (goto 0)
            ∷ seq 1 (atm (lit Int (+ 1))) (goto 0)
            ∷ return (atm (var 1)) ∷ [])
      (case (var 0) 2 1 2)
join = refl
