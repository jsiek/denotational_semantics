open import Data.List using (List)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)
open import abt.Sig using (Sig)

{-
  Well-scoped terms, for any signature: WS k M when every variable of M
  is bound in a context of k variables, where a cleared argument (∁) is
  in a context of its own binders only. A variable that a well-scoped
  term uses is in its context (ws-uses).
-}
module Syntax.Scope (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; clear; nil; cons)
  renaming (ABT to AST; Arg to Arg; Args to Args)
open import Syntax.Uses Op sig using (Uses; UsesArg; UsesArgs)

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

ws-uses : ∀ {k x} M → WS k M → Uses x M → x < k
ws-uses-arg : ∀ {b k x} (a : Arg b) → WS-arg k a → UsesArg x a → x < k
ws-uses-args : ∀ {bs k x} (args : Args bs) → WS-args k args → UsesArgs x args → x < k

ws-uses (` x) w refl = w
ws-uses (op ⦅ args ⦆) w u = ws-uses-args args w u

ws-uses-arg (ast M) w u = ws-uses M w u
ws-uses-arg (bind a) w u = ≤-pred (ws-uses-arg a w u)
ws-uses-arg (clear a) w ()

ws-uses-args (cons a args) (w , ws) (inj₁ u) = ws-uses-arg a w u
ws-uses-args (cons a args) (w , ws) (inj₂ u) = ws-uses-args args ws u
