{-# OPTIONS --without-K #-}
{- Extracted from the abt library (github.com/jsiek/abstract-binding-trees,
   commit 1387c40): just the abstract binding trees themselves. -}
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import abt.Sig
open import abt.Var

module abt.AbstractBindingTree (Op : Set) (sig : Op → List Sig) where

data Args : List Sig → Set

data ABT : Set where
  `_ : Var → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : Sig → Set where
  ast : ABT → Arg ■
  bind : ∀{b} → Arg b → Arg (ν b)
  clear : ∀{b} → Arg b → Arg (∁ b)

data Args where
  nil : Args []
  cons : ∀{b bs} → Arg b → Args bs → Args (b ∷ bs)

var-injective : ∀ {x y} → ` x ≡ ` y → x ≡ y
var-injective refl = refl
