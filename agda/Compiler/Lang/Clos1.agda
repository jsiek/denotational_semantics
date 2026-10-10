{-# OPTIONS --safe #-}

module Compiler.Lang.Clos1 where

{-
 In this intermediate language, a closure lists its free variables but
   its body still refers to the surrounding variables directly:
   clos-op n ⦅ (y. N) , fv₁ , ... , fvₙ ⦆
 This language is after the 'annotate' pass,
   and before the 'enclose' pass.
-}

open import Primitives
open import abt.ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import SetsAsPredicates
open import NewDenotProperties
open import abt.Sig using (Sig; ∁; ν; ■) public
open import abt.Var using (Var) public
open import abt.GSubst using (_•_) public


open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)

{- Syntax ---------------------------------------------------------------------}

data Op : Set where
  clos-op : ℕ → Op
  app : Op
  lit : (B : Base) → (k : base-rep B) → Op
  tuple : ℕ → Op
  get : ∀ {n} (i : Fin n) → Op
  inl-op : Op
  inr-op : Op
  case-op : Op

sig : Op → List Sig
sig (clos-op n) = ν ■ ∷ (replicate n ■)
sig app = ■ ∷ ■ ∷ []
sig (lit B k) = []
sig (tuple n) = replicate n ■
sig (get i) = ■ ∷ []
sig inl-op = ■ ∷ []
sig inr-op = ■ ∷ []
sig case-op = ■ ∷ ν ■ ∷ ν ■ ∷ []

import abt.AbstractBindingTree
module ASTMod = abt.AbstractBindingTree Op sig
open ASTMod using (`_; _⦅_⦆; clear; bind; ast; cons; nil; Arg; Args)
            renaming (ABT to AST) public