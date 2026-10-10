module Compiler.Lang.Clos5 where
{-

 In this language the code of every function is a global definition.
 A closure pairs a reference to a global definition (fun-ref k) with the
   tuple of its free variables, and applications have two operands
   besides the function, as in Clos4.
 A program is a list of global definitions and a main expression.
 This language is after the 'globalize' pass.

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

open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

{- Syntax ---------------------------------------------------------------------}

data Op : Set where
  fun-ref : ℕ → Op
  app : Op
  lit : (B : Base) → (k : base-rep B) → Op
  pair-op : Op
  fst-op : Op
  snd-op : Op
  tuple : ℕ → Op
  get : ∀ {n} (i : Fin n) → Op
  inl-op : Op
  inr-op : Op
  case-op : Op

sig : Op → List Sig
sig (fun-ref k) = []
sig app = ■ ∷ ■ ∷ ■ ∷ []
sig (lit B k) = []
sig pair-op = ■ ∷ ■ ∷ []
sig fst-op = ■ ∷ []
sig snd-op = ■ ∷ []
sig (tuple n) = replicate n ■
sig (get i) = ■ ∷ []
sig inl-op = ■ ∷ []
sig inr-op = ■ ∷ []
sig case-op = ■ ∷ ν ■ ∷ ν ■ ∷ []

import abt.AbstractBindingTree
module ASTMod = abt.AbstractBindingTree Op sig
open ASTMod using (`_; _⦅_⦆; clear; bind; ast; cons; nil; Arg; Args)
            renaming (ABT to AST) public

{- A program. Each global definition is the code of a function, with the
   argument as variable 0 and the tuple of free variables as variable 1.
   The definitions are listed newest first: a reference fun-ref k names
   the definition with k definitions before it (the k-th, counting from
   the oldest), and the code of a definition refers only to older ones. -}
record Program : Set where
  constructor program
  field
    defs : List AST
    main : AST
