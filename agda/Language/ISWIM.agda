module Language.ISWIM where

{-
 The source language: ISWIM, an untyped lambda calculus with constants,
   tuples, sums, and the primitive operations sub and eq on integers.
   There are no booleans: eq returns inl ⟨⟩ for true and inr ⟨⟩ for false
   (⟨⟩ is the empty tuple), so case serves as if (see Language/Prim).
 A function lam ⦅ (y. N) ⦆ refers to the surrounding variables directly.
 This language is before the 'enclose' pass.
-}

open import Framework.Primitives
open import Language.Prim using (Prim)
open import Framework.abt.ScopedTuple hiding (𝒫)
open import Framework.Syntax.SigUtil
open import Framework.abt.Sig using (Sig; ∁; ν; ■) public
open import Framework.abt.Var using (Var) public
open import Framework.abt.GSubst using (_•_) public


open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)

{- Syntax ---------------------------------------------------------------------}

data Op : Set where
  lam : Op
  app : Op
  lit : (B : Base) → (k : base-rep B) → Op
  tuple : ℕ → Op
  get : ∀ {n} (i : Fin n) → Op
  inl-op : Op
  inr-op : Op
  case-op : Op
  prim : Prim → Op      {- a primitive operation on integers (Language/Prim) -}

sig : Op → List Sig
sig lam = ν ■ ∷ []
sig app = ■ ∷ ■ ∷ []
sig (lit B k) = []
sig (tuple n) = replicate n ■
sig (get i) = ■ ∷ []
sig inl-op = ■ ∷ []
sig inr-op = ■ ∷ []
sig case-op = ■ ∷ ν ■ ∷ ν ■ ∷ []
sig (prim p) = ■ ∷ ■ ∷ []

import Framework.abt.AbstractBindingTree
module ASTMod = Framework.abt.AbstractBindingTree Op sig
open ASTMod using (`_; _⦅_⦆; clear; bind; ast; cons; nil; Arg; Args)
            renaming (ABT to AST) public