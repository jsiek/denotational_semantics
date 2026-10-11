open import Data.Nat using (ℕ; zero; suc; _≟_; _∸_; _⊔_; _<_)
open import Data.Nat.Properties using (≤-pred; n<1+n; <-≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_⊎?_)
open import abt.Sig using (Sig; ν; ■; ∁)
open import abt.Var using (Var)

{-
  Which variables a term uses. A cleared argument (∁) cannot see the
  variables around it, so it uses none of them. Every variable a term
  uses is below its bound.
-}
module Compiler.Lang.Uses (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; clear; nil; cons)
  renaming (ABT to AST; Arg to Arg; Args to Args)

Uses : Var → AST → Set
UsesArg : ∀ {b} → Var → Arg b → Set
UsesArgs : ∀ {bs} → Var → Args bs → Set

Uses x (` y) = x ≡ y
Uses x (op ⦅ args ⦆) = UsesArgs x args

UsesArg x (ast M) = Uses x M
UsesArg x (bind a) = UsesArg (suc x) a
UsesArg x (clear a) = ⊥

UsesArgs x nil = ⊥
UsesArgs x (cons a args) = UsesArg x a ⊎ UsesArgs x args

uses? : ∀ x M → Dec (Uses x M)
uses-arg? : ∀ {b} x (a : Arg b) → Dec (UsesArg x a)
uses-args? : ∀ {bs} x (args : Args bs) → Dec (UsesArgs x args)

uses? x (` y) = x ≟ y
uses? x (op ⦅ args ⦆) = uses-args? x args

uses-arg? x (ast M) = uses? x M
uses-arg? x (bind a) = uses-arg? (suc x) a
uses-arg? x (clear a) = no (λ ())

uses-args? x nil = no (λ ())
uses-args? x (cons a args) = uses-arg? x a ⊎? uses-args? x args

{- one more than the largest variable a term uses, or 0 if it uses none -}
bound : AST → ℕ
bound-arg : ∀ {b} → Arg b → ℕ
bound-args : ∀ {bs} → Args bs → ℕ

bound (` x) = suc x
bound (op ⦅ args ⦆) = bound-args args

bound-arg (ast M) = bound M
bound-arg (bind a) = bound-arg a ∸ 1
bound-arg (clear a) = 0

bound-args nil = 0
bound-args (cons a args) = bound-arg a ⊔ bound-args args

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
