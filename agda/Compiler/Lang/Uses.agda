open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_⊎?_)
open import abt.Sig using (Sig; ν; ■; ∁)
open import abt.Var using (Var)

{-
  Which variables a term uses. A cleared argument (∁) cannot see the
  variables around it, so it uses none of them.
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
