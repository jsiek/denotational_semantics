open import Primitives
open import Structures
import ValueStructAux

open import Data.Nat using (ℕ; suc ; zero)

module ISWIMDenot
  (D : ValueStruct)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
     → ValueStructAux.Denotation D Γ)
  (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
  where
  open ValueStruct D
  open ValueStructAux D
  open ValueOrdering V

  open import ISWIM

  ℰ : ∀{Γ} → Term Γ → Denotation Γ
  ℰ ($ P k) γ v = ℘ {P} k v
  ℰ {Γ} (` x) γ v = v ⊑ γ x
  ℰ {Γ} (ƛ N) = ℱ (ℰ N)
  ℰ {Γ} (L · M) = (ℰ L) ● (ℰ M)

  {- The following is a duplication from Structures.LambdaDenot -}
  split : ∀ {Γ} {M : Term (suc Γ)} {δ : Env (suc Γ)} {v}
    → ℰ M δ v
      ------------------------
    → ℰ M (init δ `, last δ) v
  split {δ = δ} δMv rewrite init-last δ = δMv

  infix 3 _`⊢_↓_
  _`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
  _`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))


