open import Data.Nat using (ℕ; zero; suc; _∸_; _⊔_; _<_)
open import Data.Nat.Properties using (≤-pred; n<1+n; <-≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.List using (List)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Framework.abt.Sig using (Sig)

{-
  Every variable a term uses is below its bound.
-}
module proof.Framework.Syntax.Uses (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
  renaming (ABT to AST)
open import Framework.Syntax.Uses Op sig public

<-∸1 : ∀ {x b} → suc x < b → x < b ∸ 1
<-∸1 {x} {suc b} sx<sb = ≤-pred sx<sb

uses-bound : ∀ x (M : AST) → Uses x M → x < bound M
uses-bound-arg : ∀ {b} x (a : Arg b) → UsesArg x a → x < bound-arg a
uses-bound-args : ∀ {bs} x (args : Args bs) → UsesArgs x args → x < bound-args args

uses-bound x (` .x) refl = n<1+n x
uses-bound x (op ⦅ args ⦆) u = uses-bound-args x args u

uses-bound-arg x (ast M) u = uses-bound x M u
uses-bound-arg x (bind a) u = <-∸1 (uses-bound-arg (suc x) a u)

uses-bound-args x (cons a args) (inj₁ u) = <-≤-trans (uses-bound-arg x a u) (m≤m⊔n _ _)
uses-bound-args x (cons a args) (inj₂ u) =
  <-≤-trans (uses-bound-args x args u) (m≤n⊔m (bound-arg a) _)
