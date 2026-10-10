{-# OPTIONS --without-K --safe #-}
{- Extracted from the abt library (github.com/jsiek/abstract-binding-trees,
   commit 1387c40): just environments and extending them. -}
open import Data.Nat using (ℕ; zero; suc)
open import abt.Var

module abt.GSubst where

GSubst : ∀{ℓ} (V : Set ℓ) → Set ℓ
GSubst V = Var → V

infixr 6 _•_
_•_ : ∀{ℓ}{V : Set ℓ} → V → GSubst V → GSubst V
(v • σ) 0 = v
(v • σ) (suc x) = σ x
