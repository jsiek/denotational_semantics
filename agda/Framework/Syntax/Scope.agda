open import Data.List using (List)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Framework.abt.Sig using (Sig)

{-
  Well-scoped terms, for any signature: WS k M when every variable of M
  is bound in a context of k variables, where a cleared argument (∁) is
  in a context of its own binders only. (A variable that a well-scoped
  term uses is in its context: ws-uses, in proof/Framework/Syntax/Scope.agda.)
-}
module Framework.Syntax.Scope (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; clear; nil; cons)
  renaming (ABT to AST; Arg to Arg; Args to Args)

WS : ℕ → AST → Set
WS-arg : ∀ {b} → ℕ → Arg b → Set
WS-args : ∀ {bs} → ℕ → Args bs → Set

WS k (` x) = x < k
WS k (op ⦅ args ⦆) = WS-args k args

WS-arg k (ast M) = WS k M
WS-arg k (bind a) = WS-arg (suc k) a
WS-arg k (clear a) = WS-arg 0 a

WS-args k nil = ⊤
WS-args k (cons a args) = WS-arg k a × WS-args k args
