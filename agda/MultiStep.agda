open import Data.Bool  
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)

import Syntax3

module MultiStep
  (Op : Set)
  (sig : Op → List ℕ) 
  (_—→_ : ∀ {Γ} → (Syntax3.AST Op sig Γ) → (Syntax3.AST Op sig Γ) → Set)
  where

  open Syntax3 Op sig

  private Term : ℕ → Set
  Term Γ = AST Γ

  infix  2 _—↠_
  infixr 2 _—→⟨_⟩_
  infixr 2 _—↠⟨_⟩_
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


  _—↠⟨_⟩_ : ∀{Γ}(L : Term Γ) {M N : Term Γ}
           → L —↠ M
           → M —↠ N
           → L —↠ N
  L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N

