{-

  The Lambda Calculus

-}

module Lambda where


open import Variables

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

sig : Op → List Bool
sig lam = true ∷ []
sig app = false ∷ false ∷ []

import Syntax2
module ASTMod = Syntax2 Op sig
open ASTMod using (`_; _⦅_⦆; Subst; rename; ⟪_⟫;
         _[_]; _•_; _⨟_; ↑;
         exts; exts-cons-shift; bind; cons; nil)


AST : ℕ → Set
AST Γ = ASTMod.AST Γ

infixl 7  _·_

ƛ : ∀{Γ} → AST (suc Γ) → AST Γ
ƛ N = lam ⦅ bind N nil ⦆

_·_ : ∀{Γ} → AST Γ → AST Γ → AST Γ
L · M = app ⦅ cons L (cons M nil) ⦆

Term : ℕ → Set
Term Γ = AST Γ

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

    ζ-rule : ∀ {Γ} {N N′ : Term (suc Γ)}
      → N —→ N′
        -----------
      → ƛ N —→ ƛ N′

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

  —↠-trans : ∀{Γ}{L M N : Term Γ}
           → L —↠ M
           → M —↠ N
           → L —↠ N
  —↠-trans (M □) mn = mn
  —↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)

  —→-app-cong : ∀{Γ}{L L' M : Term Γ}
              → L —→ L'
              → L · M —→ L' · M
  —→-app-cong (ξ₁-rule ll') = ξ₁-rule (—→-app-cong ll')
  —→-app-cong (ξ₂-rule ll') = ξ₁-rule (ξ₂-rule ll')
  —→-app-cong β-rule = ξ₁-rule β-rule
  —→-app-cong (ζ-rule ll') = ξ₁-rule (ζ-rule ll')

  abs-cong : ∀ {Γ} {N N' : Term (suc Γ)}
           → N —↠ N'
             ----------
           → ƛ N —↠ ƛ N'
  abs-cong (M □) = ƛ M □
  abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ-rule r ⟩ abs-cong rs

  appL-cong : ∀ {Γ} {L L' M : Term Γ}
           → L —↠ L'
             ---------------
           → L · M —↠ L' · M
  appL-cong {Γ}{L}{L'}{M} (L □) = L · M □
  appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁-rule r ⟩ appL-cong rs

  appR-cong : ∀ {Γ} {L M M' : Term Γ}
           → M —↠ M'
             ---------------
           → L · M —↠ L · M'
  appR-cong {Γ}{L}{M}{M'} (M □) = L · M □
  appR-cong {Γ}{L}{M}{M'} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂-rule r ⟩ appR-cong rs

