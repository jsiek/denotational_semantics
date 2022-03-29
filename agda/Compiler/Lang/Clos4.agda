module Compiler.Lang.Clos4 where
{-

 In this intermediate semantics all functions take two parameters,
   so applications have two operands. We use a pair to create 
   concrete closures instead of performing early appliction.
 This language is after the 'delay' pass,
   and before the 'globalize' pass.

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
  fun-op : Op
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
sig fun-op = ∁ (ν (ν ■)) ∷ []
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

module ASTMod = Syntax.OpSig Op sig
open ASTMod using (`_; _⦅_⦆; Subst; Ctx; plug; rename; 
                   ⟪_⟫; _[_]; subst-zero; clear; bind; ast; cons; nil;
                   Arg; Args;
                   rename-id; exts-cons-shift; WF; WF-Ctx; ctx-depth;
                   WF-op; WF-cons; WF-nil; WF-ast; WF-bind; WF-var;
                   COp; CAst; CBind; ccons; tcons; append₊)
            renaming (ABT to AST) public