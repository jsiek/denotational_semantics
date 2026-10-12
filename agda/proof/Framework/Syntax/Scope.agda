open import Data.List using (List)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Framework.abt.Sig using (Sig)

{-
  A variable that a well-scoped term uses is in its context.
-}
module proof.Framework.Syntax.Scope (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
  renaming (ABT to AST)
open import Framework.Syntax.Scope Op sig public
open import proof.Framework.Syntax.Uses Op sig using (Uses; UsesArg; UsesArgs)

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
