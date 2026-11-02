{-

  An example of cast insertion and the typed closure-conversion passes:
  (λx. x - 1) 5, and an application of a non-function, 5 5, through cast
  insertion, capture, prune, concretize and split, run on the ISWIM
  machine and on the Clos4ᵀ machine.

-}

open import Framework.Primitives using (Int)
open import Language.Prim using (sub)
open import Language.ISWIM
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)
open import Language.Typed.Type
import Language.Typed.ISWIM as T
open import Compiler.Cast using (cast-program)
open import Compiler.Capture using (capture)
open import Compiler.Prune using (prune-program)
open import Compiler.Concretize using (concretize-program)
open import Compiler.Split using (split-program)
import Language.Typed.Clos4 as Clos4ᵀ
open import Data.List using ([])
open import Semantics.Observation using (Obs; o-const; o-error)
open import Semantics.CEK.Smallstep using (Machine; next; stop)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos4 as Clos4ᵀₘ

open import Framework.Syntax.Scope Op sig using (WS)
open import Data.Fin using (zero; suc)
open import Data.Integer using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module proof.Compiler.Examples.CastExample where

{- cast insertion to split, on a well-scoped closed program -}
to-clos4 : (M : AST) → WS 0 M → Clos4ᵀ.Tm [] Any
to-clos4 M w = split-program (concretize-program (prune-program (capture (cast-program M w))))

{- run a machine for at most n steps -}
run : ℕ → (L : Machine) → Maybe Obs
run n L = go n (Machine.start L)
  where
  go : ℕ → Machine.State L → Maybe Obs
  go zero s = nothing
  go (suc n) s with Machine.step L s
  ... | next s' = go n s'
  ... | stop o = just o

five : AST
five = lit Int (+ 5) ⦅ Nil ⦆

{- (λx. x - 1) 5 -}
dec5 : AST
dec5 = app ⦅ lam ⦅ ⟩ prim sub ⦅ ` 0 ,, lit Int (+ 1) ⦅ Nil ⦆ ,, Nil ⦆ ,, Nil ⦆ ,, five ,, Nil ⦆

dec5-ws : WS 0 dec5
dec5-ws = ((s≤s z≤n , tt , tt) , tt) , tt , tt

{- cast insertion: the operator is projected to a function, the operands
   of sub are let-bound and projected to integers -}
dec5ᵀ : cast-program dec5 dec5-ws
  ≡ T.app (T.project tfun (T.inject fun (T.lam
          (T.let′ (T.` zero) (T.let′ (T.inject (base Int) (T.lit Int (+ 1)))
            (T.inject (base Int) (T.prim sub (T.project tint (T.` suc zero))
                                             (T.project tint (T.` zero)))))))))
        (T.inject (base Int) (T.lit Int (+ 5)))
dec5ᵀ = refl

dec5-iswim : run 20 (ISWIMₘ.sem dec5) ≡ just (o-const Int (+ 4))
dec5-iswim = refl

dec5-clos4 : run 60 (Clos4ᵀₘ.sem (to-clos4 dec5 dec5-ws)) ≡ just (o-const Int (+ 4))
dec5-clos4 = refl

{- 5 5: the ISWIM machine finds that 5 is not a function; the compiled
   program stops at the project that cast insertion put there -}
bad : AST
bad = app ⦅ five ,, five ,, Nil ⦆

bad-ws : WS 0 bad
bad-ws = tt , tt , tt

bad-iswim : run 10 (ISWIMₘ.sem bad) ≡ just o-error
bad-iswim = refl

bad-clos4 : run 20 (Clos4ᵀₘ.sem (to-clos4 bad bad-ws)) ≡ just o-error
bad-clos4 = refl
