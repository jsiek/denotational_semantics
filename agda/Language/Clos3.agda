module Language.Clos3 where

{-
 In this intermediate language,
   we perform early application of functions 
   on a tuple that captures the local enviroment.
 This language is after the 'uncurry' pass,
   and before the 'delay' pass.
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
  clos-op : ℕ → Op
  app : Op
  lit : (B : Base) → (k : base-rep B) → Op
  tuple : ℕ → Op
  get : ∀ {n} (i : Fin n) → Op
  inl-op : Op
  inr-op : Op
  case-op : Op
  prim : Prim → Op      {- a primitive operation on integers (Language/Prim) -}
  let-op : Op           {- let x = M in N, call by value -}

sig : Op → List Sig
sig (clos-op n) = ∁ (ν (ν ■)) ∷ (replicate n ■)
sig app = ■ ∷ ■ ∷ []
sig (lit B k) = []
sig (tuple n) = replicate n ■
sig (get i) = ■ ∷ []
sig inl-op = ■ ∷ []
sig inr-op = ■ ∷ []
sig case-op = ■ ∷ ν ■ ∷ ν ■ ∷ []
sig (prim p) = ■ ∷ ■ ∷ []
sig let-op = ■ ∷ ν ■ ∷ []

import Framework.abt.AbstractBindingTree
module ASTMod = Framework.abt.AbstractBindingTree Op sig
open ASTMod using (`_; _⦅_⦆; clear; bind; ast; cons; nil; Arg; Args)
            renaming (ABT to AST) public