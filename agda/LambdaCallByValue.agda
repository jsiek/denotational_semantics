{-

  Call-by-value Lambda Calculus

-}

module LambdaCallByValue where

open import Variables
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst; Ctx; plug;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open import ValueBCD

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

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


—↠-trans : ∀{Γ}{L M N : Term Γ}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M ▩) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)

infixr 2 _—↠⟨_⟩_

_—↠⟨_⟩_ : ∀{Γ}(L : Term Γ) {M N : Term Γ}
         → L —↠ M
         → M —↠ N
         → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N

—→-app-cong : ∀{Γ}{L L' M : Term Γ}
            → L —→ L'
            → L · M —→ L' · M
—→-app-cong (ξ₁-rule ll') = ξ₁-rule (—→-app-cong ll')
—→-app-cong (ξ₂-rule v ll') = ξ₁-rule (ξ₂-rule v ll')
—→-app-cong (β-rule v) = ξ₁-rule (β-rule v)

appL-cong : ∀ {Γ} {L L' M : Term Γ}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {Γ}{L}{L'}{M} (L ▩) = L · M ▩
appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁-rule r ⟩ appL-cong rs

appR-cong : ∀ {Γ} {L M M' : Term Γ}
         → TermValue L
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} v (M ▩) = L · M ▩
appR-cong {Γ}{L}{M}{M'} v (M —→⟨ r ⟩ rs) =
    L · M —→⟨ ξ₂-rule v r ⟩ appR-cong v rs

terminates : ∀{Γ} → (M : Term Γ ) → Set
terminates {Γ} M = Σ[ N ∈ Term (suc Γ) ] (M —↠ ƛ N)

_≅_ : ∀{Γ} → (M N : Term Γ) → Set
(_≅_ {Γ} M N) = ∀ {C : Ctx Γ zero}
              → (terminates (plug C M)) iff (terminates (plug C N))
