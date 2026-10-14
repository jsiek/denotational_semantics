{-

  Smoke tests of the typed compiler (Compiler/Pipeline.agda), from
  untyped ISWIM to X86, run on the X86 machine (Semantics/CEK/X86.agda)
  and on the ISWIM machine, by computation.

-}

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Language.ISWIM
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)
open import Compiler.Pipeline using (compile-x86)
open import Semantics.Observation using (Obs; o-const; o-error)
open import Semantics.CEK.Smallstep using (Machine; next; stop)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.X86 as X86ₘ

open import Data.Integer using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module proof.Compiler.Examples.PipelineExample where

{- run a machine for at most n steps -}
run : ℕ → (L : Machine) → Maybe Obs
run n L = go n (Machine.start L)
  where
  go : ℕ → Machine.State L → Maybe Obs
  go zero s = nothing
  go (suc n) s with Machine.step L s
  ... | next s' = go n s'
  ... | stop o = just o

int : ℕ → AST
int n = lit Int (+ n) ⦅ Nil ⦆

{- (λx. x - 1) 5 -}
dec5 : AST
dec5 = app ⦅ lam ⦅ ⟩ prim sub ⦅ ` 0 ,, int 1 ,, Nil ⦆ ,, Nil ⦆ ,, int 5 ,, Nil ⦆

dec5-iswim : run 50 (ISWIMₘ.sem dec5) ≡ just (o-const Int (+ 4))
dec5-iswim = refl

dec5-x86 : run 200 (X86ₘ.sem (compile-x86 dec5)) ≡ just (o-const Int (+ 4))
dec5-x86 = refl

{- (λx. λy. x - y) 10 3: a closure that captures x -}
sub103 : AST
sub103 = app ⦅ app ⦅ lam ⦅ ⟩ lam ⦅ ⟩ prim sub ⦅ ` 1 ,, ` 0 ,, Nil ⦆ ,, Nil ⦆ ,, Nil ⦆ ,, int 10 ,, Nil ⦆
               ,, int 3 ,, Nil ⦆

sub103-x86 : run 400 (X86ₘ.sem (compile-x86 sub103)) ≡ just (o-const Int (+ 7))
sub103-x86 = refl

{- (λx. case x = 1 of inl _ ⇒ 5 | inr _ ⇒ 6) 1: eq, case, a join -}
pick : AST
pick = app ⦅ lam ⦅ ⟩ case-op ⦅ prim eq ⦅ ` 0 ,, int 1 ,, Nil ⦆ ,, ⟩ int 5 ,, ⟩ int 6 ,, Nil ⦆ ,, Nil ⦆
           ,, int 1 ,, Nil ⦆

pick-x86 : run 400 (X86ₘ.sem (compile-x86 pick)) ≡ just (o-const Int (+ 5))
pick-x86 = refl

{- (get 0 (1, 2)) - 1: a tuple, and a project to a tuple of 2 -}
fst12 : AST
fst12 = prim sub ⦅ get {2} zero ⦅ tuple 2 ⦅ int 1 ,, int 2 ,, Nil ⦆ ,, Nil ⦆ ,, int 1 ,, Nil ⦆
  where open import Data.Fin using (zero)

fst12-x86 : run 400 (X86ₘ.sem (compile-x86 fst12)) ≡ just (o-const Int (+ 0))
fst12-x86 = refl

{- 5 5: the X86 code stops at the test of the project that cast
   insertion put in front of the operator, as the ISWIM machine does -}
bad : AST
bad = app ⦅ int 5 ,, int 5 ,, Nil ⦆

bad-iswim : run 10 (ISWIMₘ.sem bad) ≡ just o-error
bad-iswim = refl

bad-x86 : run 100 (X86ₘ.sem (compile-x86 bad)) ≡ just o-error
bad-x86 = refl

{- (λx. x) - 1: the project to an integer fails -}
bad-sub : AST
bad-sub = prim sub ⦅ lam ⦅ ⟩ ` 0 ,, Nil ⦆ ,, int 1 ,, Nil ⦆

bad-sub-x86 : run 100 (X86ₘ.sem (compile-x86 bad-sub)) ≡ just o-error
bad-sub-x86 = refl
