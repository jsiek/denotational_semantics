module LambdaV where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Primitives
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

data Op : Set where
  lam : Op
  app : Op
{-
  prim : ∀{p : Prim} → rep p → Op
-}

sig : Op → List Bool
sig lam = true ∷ []
sig app = false ∷ false ∷ []
{-
sig (prim {p} k) = []
-}

import Syntax2
module ASTMod = Syntax2 Op sig
open ASTMod using (`_; _⦅_⦆; Var; Rename; Subst; rename; ⟪_⟫; _[_]; Z; S_; _•_; _⨟_; ↑;
                   exts; exts-cons-shift; extensionality; bind; cons; nil)


AST : ℕ → Set
AST Γ = ASTMod.AST Γ

infixl 7  _·_

ƛ : ∀{Γ} → AST (suc Γ) → AST Γ
ƛ N = lam ⦅ bind N nil ⦆

_·_ : ∀{Γ} → AST Γ → AST Γ → AST Γ
L · M = app ⦅ cons L (cons M nil) ⦆

{-
$ : ∀{Γ}{p : Prim} → rep p → AST Γ
$ {Γ}{p} k = prim {p} k ⦅ nil ⦆
-}

Term : ℕ → Set
Term Γ = AST Γ


module CBV-Reduction where

  data TermValue : ∀ {Γ} → Term Γ → Set where

    V-var : ∀ {Γ}{x : Var Γ}
        --------------------
      → TermValue {Γ} (` x)

    V-ƛ : ∀ {Γ} {N : Term (suc Γ)}
        -----------
      → TermValue (ƛ N)

  {-
    V-const : ∀ {Γ} {p : Prim} {k : rep p}
        ------------------------
      → TermValue {Γ} ($ {Γ}{p} k)
  -}

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

  {-
    δ-rule : ∀ {Γ}{B}{P} {f : base-rep B → rep P} {k : base-rep B}
        ----------------------------------------------------------
      → ($ {Γ} {B ⇒ P} f) · ($ {Γ}{base B} k) —→ ($ {Γ}{P} (f k))
  -}

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


module Reduction where

  infix 2 _—→_

  data _—→_ : ∀ {Γ} → (Term Γ) → (Term Γ) → Set where

    ξ₁-rule : ∀ {Γ} {L L′ M : Term Γ}
      → L —→ L′
        ----------------
      → L · M —→ L′ · M

    ξ₂-rule : ∀ {Γ} {L M M′ : Term Γ}
      → M —→ M′
        ----------------
      → L · M —→ L · M′

    β-rule : ∀ {Γ} {N : Term (suc Γ)} {M : Term Γ}
        ---------------------------------
      → (ƛ N) · M —→ N [ M ]

  {-
    δ-rule : ∀ {Γ}{B}{P} {f : base-rep B → rep P} {k : base-rep B}
        ----------------------------------------------------------
      → ($ {Γ} {B ⇒ P} f) · ($ {Γ}{base B} k) —→ ($ {Γ}{P} (f k))
  -}

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

