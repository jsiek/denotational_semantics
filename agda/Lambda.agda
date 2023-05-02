{-

  The Lambda Calculus

-}

module Lambda where


open import Utilities using (_iff_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Primitives
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Syntax using (Var; Sig; ■; ν; _•_; ↑; id; ext; _⨟_) public

data Op : Set where
  lam : Op
  app : Op

sig : Op → List Sig
sig lam = (ν ■) ∷ []
sig app = ■ ∷ ■ ∷ []

module ASTMod = Syntax.OpSig Op sig
open ASTMod
    using (`_; _⦅_⦆; bind; ast; cons; nil; _[_];
           Ctx; plug; WF; WF-Ctx; ctx-depth)
    renaming (ABT to AST) public

infixl 7  _·_

ƛ : AST → AST
ƛ N = lam ⦅ cons (bind (ast N)) nil ⦆

_·_ : AST → AST → AST
L · M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

Term : Set
Term = AST

module Reduction where

  infix 2 _—→_

  data _—→_ : Term → Term → Set where

    ξ₁-rule : ∀ {L L′ M : Term}
      → L —→ L′
        ----------------
      → L · M —→ L′ · M

    ξ₂-rule : ∀ {L M M′ : Term}
      → M —→ M′
        ----------------
      → L · M —→ L · M′

    β-rule : ∀ {N : Term} {M : Term}
        ---------------------------------
      → (ƛ N) · M —→ N [ M ]

    ζ-rule : ∀ {N N′ : Term}
      → N —→ N′
        -----------
      → ƛ N —→ ƛ N′

  open import MultiStep Op sig _—→_ public

  —→-app-cong : ∀ {L L' M : Term}
              → L —→ L'
              → L · M —→ L' · M
  —→-app-cong (ξ₁-rule ll') = ξ₁-rule (—→-app-cong ll')
  —→-app-cong (ξ₂-rule ll') = ξ₁-rule (ξ₂-rule ll')
  —→-app-cong β-rule = ξ₁-rule β-rule
  —→-app-cong (ζ-rule ll') = ξ₁-rule (ζ-rule ll')

  abs-cong : ∀ {N N' : Term}
           → N —↠ N'
             ----------
           → ƛ N —↠ ƛ N'
  abs-cong (M □) = ƛ M □
  abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ-rule r ⟩ abs-cong rs

  appL-cong : ∀ {L L' M : Term}
           → L —↠ L'
             ---------------
           → L · M —↠ L' · M
  appL-cong {L}{L'}{M} (L □) = L · M □
  appL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁-rule r ⟩ appL-cong rs

  appR-cong : ∀ {L M M' : Term}
           → M —↠ M'
             ---------------
           → L · M —↠ L · M'
  appR-cong {L}{M}{M'} (M □) = L · M □
  appR-cong {L}{M}{M'} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂-rule r ⟩ appR-cong rs

  terminates : ∀ (M : Term ) → Set
  terminates  M = Σ[ N ∈ Term ] (M —↠ ƛ N)

  _≅_ : ∀ (M N : Term) → Set₁
  (_≅_  M N) = ∀ {C : Ctx}{wfC : WF-Ctx 0 C}
                 {wfM : WF (ctx-depth C 0) M}{wfN : WF (ctx-depth C 0) N}
                → (terminates (plug C M)) iff (terminates (plug C N))
