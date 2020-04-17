open import Structures
import ValueStructAux

open import Data.Nat using (ℕ; zero; suc)

module LambdaDenot
  (D : ValueStruct)
  (V : ValueOrdering D)
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  where
  open ValueStruct D
  open ValueStructAux D
  open ValueOrdering V

  open import Lambda
  open ASTMod using (`_; _⦅_⦆; cons; bind; nil; Subst; ⟦_⟧)

  ℰ : Term → Denotation
  ℰ (` x) γ v = v ⊑ γ x
  ℰ (lam ⦅ cons (bind (ast N)) nil ⦆) = ℱ (ℰ N)
  ℰ (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) = (ℰ L) ● (ℰ M)

  {- 
     The following are here and not in DenotAux 
     because they do not depend on LambdaModelBasics.
   -}
   
  split : ∀ {M : Term} {δ : Env} {v}
    → ℰ M δ v
      ------------------------
    → ℰ M (init δ `, last δ) v
  split {δ = δ} δMv rewrite init-last δ = δMv

  infix 3 _`⊢_↓_
  _`⊢_↓_ : Env → Subst → Env → Set
  _`⊢_↓_ δ σ γ = (∀ (x : Var) → ℰ (⟦ σ ⟧ x) δ (γ x))


