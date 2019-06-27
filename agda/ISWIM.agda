{- 

   ISWIM: the call-by-value lambda calculus with constants.

-}

module ISWIM where

open import Variables public
open import Primitives

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)


data Op : Set where
  lam : Op
  app : Op
  lit : ∀{p : Prim} → rep p → Op

sig : Op → List ℕ
sig lam = 1 ∷ []
sig app = 0 ∷ 0 ∷ []
sig (lit {p} k) = []

import Syntax3
module ASTMod = Syntax3 Op sig
open ASTMod using (AST; `_; _⦅_⦆; Subst; Ctx; plug;
                   rename; ⟪_⟫; _[_]; subst-zero; bind; ast; cons; nil; exts;
                   rename-id) public
open ASTMod using (_•_; _⨟_; ↑; exts-cons-shift)

infixl 7  _·_

Term : ℕ → Set
Term Γ = AST Γ

ƛ : ∀{Γ} → Term (suc Γ) → Term Γ
ƛ N = lam ⦅ cons (bind (ast N)) nil ⦆

_·_ : ∀{Γ} → Term Γ → Term Γ → Term Γ
L · M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

$_ : ∀{Γ}{p : Prim} → rep p → Term Γ
$_ {Γ}{p} k = lit {p} k ⦅ nil ⦆



data TermValue : ∀ {Γ} → Term Γ → Set where

  V-var : ∀ {Γ}{x : Var Γ}
      --------------------
    → TermValue {Γ} (` x)

  V-ƛ : ∀ {Γ} {N : Term (suc Γ)}
      -----------
    → TermValue (ƛ N)

  V-lit : ∀ {Γ} {p : Prim} {k : rep p}
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


open import MultiStep Op sig _—→_ public

—→-app-cong : ∀{Γ}{L L' M : Term Γ}
            → L —→ L'
            → L · M —→ L' · M
—→-app-cong (ξ₁-rule ll') = ξ₁-rule (—→-app-cong ll')
—→-app-cong (ξ₂-rule v ll') = ξ₁-rule (ξ₂-rule v ll')
—→-app-cong (β-rule v) = ξ₁-rule (β-rule v)
—→-app-cong δ-rule = ξ₁-rule δ-rule

appL-cong : ∀ {Γ} {L L' M : Term Γ}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {Γ}{L}{L'}{M} (L □) = L · M □
appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁-rule r ⟩ appL-cong rs

appR-cong : ∀ {Γ} {L M M' : Term Γ}
         → TermValue L
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} v (M □) = L · M □
appR-cong {Γ}{L}{M}{M'} v (M —→⟨ r ⟩ rs) =
    L · M —→⟨ ξ₂-rule v r ⟩ appR-cong v rs

terminates : ∀{Γ} → (M : Term Γ ) → Set
terminates {Γ} M = Σ[ N ∈ Term Γ ] TermValue N × (M —↠ N)

_≅_ : ∀{Γ} → (M N : Term Γ) → Set
(_≅_ {Γ} M N) = ∀ {C : Ctx Γ zero}
              → (terminates (plug C M)) iff (terminates (plug C N))
