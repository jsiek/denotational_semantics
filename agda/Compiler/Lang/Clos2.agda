
module Compiler.Lang.Clos2 where

{-
 In this intermediate language, a closure binds its free variables
   one at a time, around the function body:
   clos-op n ⦅ ∁ (x₁ ... xₙ y. N) , fv₁ , ... , fvₙ ⦆
   where N may refer only to the argument y and the free variables x₁ ... xₙ.
 This language is after the 'enclose' pass,
   and before the 'concretize' pass.
-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewDenotProperties
open import Syntax using (Sig; ext; ∁; ν; ■; Var; _•_; ↑; id; _⨟_) public


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
sig (clos-op n) = ∁ (ν-n n (ν ■)) ∷ (replicate n ■)
sig app = ■ ∷ ■ ∷ []
sig (lit B k) = []
sig (tuple n) = replicate n ■
sig (get i) = ■ ∷ []
sig inl-op = ■ ∷ []
sig inr-op = ■ ∷ []
sig case-op = ■ ∷ ν ■ ∷ ν ■ ∷ []

module ASTMod = Syntax.OpSig Op sig
open ASTMod using (`_; _⦅_⦆; Subst; Ctx; plug; rename; 
                   ⟪_⟫; _[_]; subst-zero; clear; bind; ast; cons; nil;
                   Arg; Args;
                   rename-id; exts-cons-shift; WF; WF-Ctx; ctx-depth;
                   WF-op; WF-cons; WF-nil; WF-ast; WF-bind; WF-var;
                   COp; CAst; CBind; ccons; tcons; append₊)
            renaming (ABT to AST) public