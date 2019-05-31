{- 

   ISWM: the call-by-value lambda calculus with constants.

-}

module ISWM where
  
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Primitives
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Primitives

data Op : Set where
  lam : Op
  app : Op
  const : ∀{p : Prim} → rep p → Op

sig : Op → List Bool
sig lam = true ∷ []
sig app = false ∷ false ∷ []
sig (const {p} k) = []

import Syntax2
module ASTMod = Syntax2 Op sig
open ASTMod using (AST; `_; _⦅_⦆; Var; Rename; Subst;
    rename; ⟪_⟫; _[_]; Z; S_; _•_; _⨟_; ↑;
    exts; exts-cons-shift; extensionality; bind; cons; nil)

infixl 7  _·_

Term : ℕ → Set
Term Γ = AST Γ

ƛ : ∀{Γ} → Term (suc Γ) → Term Γ
ƛ N = lam ⦅ bind N nil ⦆

_·_ : ∀{Γ} → Term Γ → Term Γ → Term Γ
L · M = app ⦅ cons L (cons M nil) ⦆

$_ : ∀{Γ}{p : Prim} → rep p → Term Γ
$_ {Γ}{p} k = const {p} k ⦅ nil ⦆

module Reduction where

  data TermValue : ∀ {Γ} → Term Γ → Set where

    V-var : ∀ {Γ}{x : Var Γ}
        --------------------
      → TermValue {Γ} (` x)

    V-ƛ : ∀ {Γ} {N : Term (suc Γ)}
        -----------
      → TermValue (ƛ N)

    V-const : ∀ {Γ} {p : Prim} {k : rep p}
        ---------------------------
      → TermValue {Γ} ($_ {Γ}{p} k)
      
  infix 2 _—→_

  data _—→_ : ∀ {Γ} → (Term Γ) → (Term Γ) → Set where

    ξ₁-rule : ∀ {Γ} {L L′ M : Term Γ}
      → L —→ L′
        ----------------
      → L · M —→ L′ · M

    ξ₂-rule : ∀ {Γ} {L M M′ : Term Γ}
      → TermValue L
      → M —→ M′
        ----------------
      → L · M —→ L · M′

    β-rule : ∀ {Γ} {N : Term (suc Γ)} {M : Term Γ}
      → TermValue M
        ---------------------------------
      → (ƛ N) · M —→ N [ M ]

    δ-rule : ∀ {Γ}{B}{P} {f : base-rep B → rep P} {k : base-rep B}
        ------------------------------------------------------------
      → ($_ {Γ} {B ⇒ P} f) · ($_ {Γ}{base B} k) —→ ($_ {Γ}{P} (f k))
    
  infix  2 _—↠_
  infixr 2 _—→⟨_⟩_
  infix  3 _□

  data _—↠_ : ∀ {Γ} → (Term Γ) → (Term Γ) → Set where

    _□ : ∀ {Γ} (M : Term Γ)
        --------
      → M —↠ M

    _—→⟨_⟩_ : ∀ {Γ} (L : Term Γ) {M N : Term Γ}
      → L —→ M
      → M —↠ N
        ---------
      → L —↠ N


