module LambdaV where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Primitives

data Op : Set where
  lam : Op
  app : Op
  prim : ∀{p : Prim} → rep p → Op

import Syntax
module AST = Syntax Op
open AST using (`_; α_; _⦅_⦆; Var; Subst; ⟪_⟫; _[_]; Z; S_; _•_; _⨟_; ↑;
                sub-abs; sub-op; exts; exts-cons-shift)

Term : ℕ → Set
Term Γ = AST.Term Γ

infixl 7  _·_

ƛ : ∀{Γ} → Term (suc Γ) → Term Γ
ƛ N = lam ⦅ (α N) ∷ [] ⦆

_·_ : ∀{Γ} → Term Γ → Term Γ → Term Γ
L · M = app ⦅ L ∷ M ∷ [] ⦆

$ : ∀{Γ}{p : Prim} → rep p → Term Γ
$ {Γ}{p} k = prim {p} k ⦅ [] ⦆

data TermV : ∀{Γ} → Term Γ → Set where
  t-var : ∀{Γ} → (x : Var Γ) → TermV (` x)
  t-lam : ∀{Γ}{N : Term (suc Γ)} → TermV N → TermV (ƛ N)
  t-app : ∀{Γ}{L M : Term Γ} → TermV L → TermV M → TermV (L · M)

sub-lam : ∀{Γ Δ} {σ : Subst Γ Δ} {N : Term (suc Γ)}
        → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ exts σ ⟫ N)
sub-lam = refl

sub-app : ∀{Γ Δ} {σ : Subst Γ Δ} {L M : Term Γ}
        → ⟪ σ ⟫ (L · M)  ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = refl

data TermValue : ∀ {Γ} → Term Γ → Set where

  V-ƛ : ∀ {Γ} {N : Term (suc Γ)}
      -----------
    → TermValue (ƛ N)

  V-const : ∀ {Γ} {p : Prim} {k : rep p}
      ------------------------
    → TermValue {Γ} ($ {Γ}{p} k)

  V-var : ∀ {Γ}{x : Var Γ}
      --------------------
    → TermValue {Γ} (` x)

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
      ----------------------------------------------------------
    → ($ {Γ} {B ⇒ P} f) · ($ {Γ}{` B} k) —→ ($ {Γ}{P} (f k))


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

