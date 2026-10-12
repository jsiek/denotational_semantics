{-

  An example of select instructions (Compile/Select.agda).

-}

open import Framework.Primitives using (Int)
open import Compiler.Lang.Prim using (eq)
open import Compiler.Lang.Imp as Imp using (atm; var; lit)
open import Compiler.Lang.CFG as CFG using (return; seq; case)
open import Compiler.Lang.X86
open import Compiler.Compile.Select using (select-body)

open import Data.Integer using (+_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module proof.Compiler.Compile.Examples.SelectExample where

{- the output of explicate control in ExplicateExample:
     block 0: return z   block 1: return x
     start:   x := 1; t := (x = 1); case t: z := the payload; goto 0 or 1 -}
main-select :
  select-body []
    (CFG.body 3 (return (atm (var 2)) ∷ return (atm (var 0)) ∷ [])
      (seq 0 (atm (lit Int (+ 1)))
        (seq 1 (Imp.prim eq (var 0) (lit Int (+ 1)))
          (case (var 1) 2 0 1))))
  ≡ body 3 (block (movq (loc (var 2)) (reg rax) ∷ []) retq
            ∷ block (movq (loc (var 0)) (reg rax) ∷ []) retq ∷ [])
      (block (movq (imm Int (+ 1)) (var 0)
              ∷ cmpq (imm Int (+ 1)) (loc (var 0)) ∷ sete (var 1)
              ∷ testinl (loc (var 1)) ∷ load payload (loc (var 1)) (var 2) ∷ [])
             (je 0 1))
main-select = refl
