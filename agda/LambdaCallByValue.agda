{-

  Call-by-value Lambda Calculus

-}

module LambdaCallByValue where

open import Variables
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open import ValueBCD

open import Data.Nat using (ℕ; zero; suc)

data TermValue : ∀ {Γ} → Term Γ → Set where

  V-var : ∀ {Γ}{x : Var Γ}
      --------------------
    → TermValue {Γ} (` x)

  V-ƛ : ∀ {Γ} {N : Term (suc Γ)}
      -----------
    → TermValue (ƛ N)

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

infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _▩

data _—↠_ : ∀ {Γ} → (Term Γ) → (Term Γ) → Set where

  _▩ : ∀ {Γ} (M : Term Γ)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ} (L : Term Γ) {M N : Term Γ}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N
