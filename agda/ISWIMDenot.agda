open import Primitives
open import Structures
import ValueStructAux

open import Data.Nat using (ℕ; suc ; zero)

module ISWIMDenot
  (D : ValueStruct)
  (V : ValueOrdering D)
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
  where
  open ValueStruct D
  open ValueStructAux D
  open ValueOrdering V

  open import ISWIM

  ℰ : Term → Denotation
  ℰ ($ P k) γ v = ℘ {P} k v
  ℰ (` x) γ v = v ⊑ γ x
  ℰ (ƛ N) = ℱ (ℰ N)
  ℰ (L · M) = (ℰ L) ● (ℰ M)

  {- The following is a duplication from Structures.LambdaDenot -}
  split : ∀ {M : Term} {δ : Env} {v}
    → ℰ M δ v
      ------------------------
    → ℰ M (init δ `, last δ) v
  split {δ = δ} δMv rewrite init-last δ = δMv

  infix 3 _`⊢_↓_
  _`⊢_↓_ : Env → Subst → Env → Set
  _`⊢_↓_ δ σ γ = (∀ (x : Var) → ℰ (⟦ σ ⟧ x) δ (γ x))


