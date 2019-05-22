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
  prim : ∀{p : Prim} → rep p → Op

import Syntax
module ASTMod = Syntax Op
open ASTMod using (`_; α_; _⦅_⦆; Var; Rename; Subst; _[_]; Z; S_; _•_; _⨟_; ↑;
                sub-abs; sub-op; exts; exts-cons-shift; rename; extensionality)
            renaming (⟪_⟫ to subst)

AST : ℕ → Set
AST Γ = ASTMod.AST Γ

infixl 7  _·_

ƛ : ∀{Γ} → AST (suc Γ) → AST Γ
ƛ N = lam ⦅ (α N) ∷ [] ⦆

_·_ : ∀{Γ} → AST Γ → AST Γ → AST Γ
L · M = app ⦅ L ∷ M ∷ [] ⦆

$ : ∀{Γ}{p : Prim} → rep p → AST Γ
$ {Γ}{p} k = prim {p} k ⦅ [] ⦆

data IsTerm : ∀{Γ} → AST Γ → Set where
  t-var : ∀{Γ} → (x : Var Γ) → IsTerm (` x)
  t-lam : ∀{Γ}{N : AST (suc Γ)} → IsTerm N → IsTerm (ƛ N)
  t-app : ∀{Γ}{L M : AST Γ} → IsTerm L → IsTerm M → IsTerm (L · M)

Term : ℕ → Set
Term Γ = Σ[ M ∈ AST Γ ] IsTerm M

TSubst : ℕ → ℕ → Set
TSubst Γ Δ = Var Γ → Σ[ M ∈ AST Δ ] IsTerm M

rename-pres-term : ∀{Γ Δ}{M : AST Γ}{ρ : Rename Γ Δ} → IsTerm M
                 → IsTerm (rename ρ M)
rename-pres-term {ρ = ρ} (t-var x) = t-var (ρ x)
rename-pres-term (t-lam Mt) = t-lam (rename-pres-term Mt)
rename-pres-term (t-app Mt Mt₁) =
  t-app (rename-pres-term Mt) (rename-pres-term Mt₁)

texts : ∀ {Γ Δ} → (TSubst Γ Δ)
        ----------------------
      → TSubst (suc Γ) (suc Δ)
texts σ Z      =  ⟨ ` Z , t-var Z ⟩
texts σ (S x)  =  ⟨ rename S_ (proj₁ (σ x)) , rename-pres-term (proj₂ (σ x)) ⟩

⟪_⟫ : ∀ {Γ Δ}
  → TSubst Γ Δ
    -------------
  → Term Γ → Term Δ
tsubsts : ∀ {Γ Δ}
  → TSubst Γ Δ
    ---------------------------
  → List (Term Γ) → List (Term Δ)

⌊_⌋ : ∀{Γ Δ} → TSubst Γ Δ → Subst Γ Δ
⌊ σ ⌋ x = proj₁ (σ x)

sub-lam : ∀{Γ Δ} {σ : Subst Γ Δ} {N : AST (suc Γ)}
        → subst σ (ƛ N) ≡ ƛ (subst (exts σ) N)
sub-lam = refl

sub-app : ∀{Γ Δ} {σ : Subst Γ Δ} {L M : AST Γ}
        → subst σ (L · M)  ≡ (subst σ L) · (subst σ M)
sub-app = refl


texts-exts : ∀{Γ Δ}{σ : TSubst Γ Δ}
           → ⌊ texts σ ⌋ ≡ exts ⌊ σ ⌋
texts-exts {σ = σ} = extensionality λ x → G {x}
  where
  G : ∀{x} → ⌊ texts σ ⌋ x ≡ exts ⌊ σ ⌋ x
  G {Syntax.Z} = refl
  G {Syntax.S x} = refl

subst-term : ∀{Γ Δ}{M : AST Γ}{σ : TSubst Γ Δ}
           → IsTerm M
           → IsTerm (subst ⌊ σ ⌋ M)
subst-term {σ = σ} (t-var x) = proj₂ (σ x)
subst-term {σ = σ} (t-lam {N = N} Nt)
    with subst-term {σ = texts σ} Nt
... | ih    
    rewrite sub-lam {σ = ⌊ σ ⌋}{N = N} | texts-exts{σ = σ} =
    t-lam ih
subst-term {σ = σ} (t-app Lt Mt) =
    t-app (subst-term {σ = σ} Lt) (subst-term {σ = σ} Mt)


⟪_⟫ {Γ}{Δ} σ ⟨ M , Mt ⟩ = ⟨ subst ⌊ σ ⌋ M , subst-term {σ = σ} Mt ⟩

tsubsts σ [] = []
tsubsts σ (t ∷ ts) = ⟪ σ ⟫ t ∷ tsubsts σ ts







data TermValue : ∀ {Γ} → AST Γ → Set where

  V-var : ∀ {Γ}{x : Var Γ}
      --------------------
    → TermValue {Γ} (` x)

  V-ƛ : ∀ {Γ} {N : AST (suc Γ)}
      -----------
    → TermValue (ƛ N)

  V-const : ∀ {Γ} {p : Prim} {k : rep p}
      ------------------------
    → TermValue {Γ} ($ {Γ}{p} k)

infix 2 _—→_

data _—→_ : ∀ {Γ} → (AST Γ) → (AST Γ) → Set where

  ξ₁-rule : ∀ {Γ} {L L′ M : AST Γ}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀ {Γ} {L M M′ : AST Γ}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀ {Γ} {N : AST (suc Γ)} {M : AST Γ}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  δ-rule : ∀ {Γ}{B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ----------------------------------------------------------
    → ($ {Γ} {B ⇒ P} f) · ($ {Γ}{` B} k) —→ ($ {Γ}{P} (f k))


infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _□

data _—↠_ : ∀ {Γ} → (AST Γ) → (AST Γ) → Set where

  _□ : ∀ {Γ} (M : AST Γ)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ} (L : AST Γ) {M N : AST Γ}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

