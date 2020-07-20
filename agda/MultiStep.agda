open import Data.Bool  
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)

import Syntax
open Syntax using (Sig)

module MultiStep
  (Op : Set)
  (sig : Op → List Sig) 
  (_—→_ : (Syntax.OpSig.ABT Op sig) → (Syntax.OpSig.ABT Op sig) → Set)
  where

  open Syntax.OpSig Op sig

  private Term : Set
  Term = ABT

  infix  2 _—↠_
  infixr 2 _—→⟨_⟩_
  infixr 2 _—↠⟨_⟩_
  infix  3 _□

  data _—↠_ : Term → Term → Set where

    _□ : (M : Term)
        --------
      → M —↠ M

    _—→⟨_⟩_ : ∀ (L : Term) {M N : Term}
      → L —→ M
      → M —↠ N
        ---------
      → L —↠ N

  —↠-trans : ∀{L M N : Term}
           → L —↠ M
           → M —↠ N
           → L —↠ N
  —↠-trans (M □) mn = mn
  —↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)


  _—↠⟨_⟩_ : ∀(L : Term) {M N : Term}
           → L —↠ M
           → M —↠ N
           → L —↠ N
  L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N

