open import Variables
open import Structures
import ValueStructAux

open import Data.Nat using (ℕ; zero; suc)

module LambdaDenot
  (D : ValueStruct)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
     → ValueStructAux.Denotation D Γ)
  where
  open ValueStruct D
  open ValueStructAux D
  open ValueOrdering V

  open import Lambda
  open ASTMod using (`_; _⦅_⦆; cons; bind; nil; Subst)

  ℰ : ∀{Γ} → Term Γ → Denotation Γ
  ℰ {Γ} (` x) γ v = v ⊑ γ x
  ℰ {Γ} (lam ⦅ cons (bind (ast N)) nil ⦆) = ℱ (ℰ N)
  ℰ {Γ} (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) = (ℰ L) ● (ℰ M)

  {- 
     The following are here and not in DenotAux 
     because they do not depend on LambdaModelBasics.
   -}
   
  split : ∀ {Γ} {M : Term (suc Γ)} {δ : Env (suc Γ)} {v}
    → ℰ M δ v
      ------------------------
    → ℰ M (init δ `, last δ) v
  split {δ = δ} δMv rewrite init-last δ = δMv

  infix 3 _`⊢_↓_
  _`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
  _`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))


