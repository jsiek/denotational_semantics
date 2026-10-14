open import Data.List using (List)
open import Framework.abt.Sig using (Sig)

{-
  Well-scopedness (Framework/Syntax/Scope.agda) is decidable.
-}
module Framework.Syntax.ScopeDec (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; clear; nil; cons)
  renaming (ABT to AST; Arg to Arg; Args to Args)
open import Framework.Syntax.Scope Op sig

open import Data.Nat using (ℕ; suc; _<?_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_×?_)

ws? : ∀ k M → Dec (WS k M)
ws-arg? : ∀ {b} k (a : Arg b) → Dec (WS-arg k a)
ws-args? : ∀ {bs} k (args : Args bs) → Dec (WS-args k args)

ws? k (` x) = x <? k
ws? k (op ⦅ args ⦆) = ws-args? k args

ws-arg? k (ast M) = ws? k M
ws-arg? k (bind a) = ws-arg? (suc k) a
ws-arg? k (clear a) = ws-arg? 0 a

ws-args? k nil = yes tt
ws-args? k (cons a args) = ws-arg? k a ×? ws-args? k args
