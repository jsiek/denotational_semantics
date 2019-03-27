module ToANF where

open import Lambda

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)

data Simp : Context → Set where
  $_ :  ∀ {Γ}{p : Prim} → rep p → Simp Γ
  
  `_ : ∀ {Γ}
    → Γ ∋ ★
      -----
    → Simp Γ


data ANF : Context → Set where
  s_ : ∀ {Γ}
    → Simp Γ
      ------
    → ANF Γ

  ƛ_  :  ∀ {Γ}
    → ANF (Γ , ★)
      -----------
    → ANF Γ

  _·_ : ∀ {Γ}
    → Simp Γ
    → Simp Γ
      ------
    → ANF Γ
    
  bind_then_ : ∀ {Γ}
    → ANF Γ
    → ANF (Γ , ★)
      ------
    → ANF Γ
  
rename-ANF : ∀ {Γ Δ}
  → Rename Γ Δ
    ---------------
  → (ANF Γ → ANF Δ)
rename-ANF ρ M          =  {!!}

to-ANF : ∀{Γ} → Γ ⊢ ★ → ANF Γ
to-ANF {Γ} ($_ {p = p} x) = s ($_ {p = p} x)
to-ANF {Γ} (` x) = s (` x)
to-ANF {Γ} (ƛ M) = ƛ (to-ANF M)
to-ANF {Γ} (M₁ · M₂) =
  let x = to-ANF M₁ in
  let y = rename-ANF (λ {A} → λ x → S x) (to-ANF M₂) in 
  bind x then (bind y then ((` (S Z)) · (` Z)))
