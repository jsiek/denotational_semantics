module Language.Clos2 where

{-
 In this intermediate language, a closure binds its free variables
   one at a time, around the function body:
   clos-op n ⦅ ∁ (x₁ ... xₙ y. N) , fv₁ , ... , fvₙ ⦆
   where N may refer only to the argument y and the free variables x₁ ... xₙ.
 This language is after the 'enclose' pass,
   and before the 'concretize' pass.
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

sig : Op → List Sig
sig (clos-op n) = ∁ (ν-n n (ν ■)) ∷ (replicate n ■)
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
{- the body of a closure's code, under its n + 1 binders -}
unbind-n : ∀ k → Arg (ν-n k (ν ■)) → AST
unbind-n zero (bind (ast N)) = N
unbind-n (suc k) (bind a) = unbind-n k a
