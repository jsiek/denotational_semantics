open import Structures
import ValueStructAux

open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)

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


  module Experiment
    (𝐹 : (Value → Value → Set) → (Value → Set))
    (_○_ : (Value → Set) → (Value → Set) → (Value → Set))
    where
    {-
    (dᶠ ○ dₐ) w = Σ[ v ∈ Value ] dᶠ (v ↦ w) × dₐ v
    -}
    open import ScopedTuple
    open import GenericSubstitution 
    open import Fold Op sig
    DenotSub : Substable Value
    DenotSub = record { var→val = λ x → ⊥ ; shift = λ x → x
                      ; var→val-suc-shift = refl }

    denot-op : (op : Op) → Tuple (sig op) (Bind Value (Value → Set))
             → Value → Set
    denot-op lam ⟨ f , tt ⟩ = 𝐹 f
    denot-op app ⟨ dᶠ , ⟨ dₐ , tt ⟩ ⟩ = dᶠ ○ dₐ

    DenotFold : Fold Value (Value → Set)
    DenotFold = record { S = DenotSub; ret = λ v w → w ⊑ v; fold-op = denot-op }
    open Fold DenotFold

    𝐸 : Term → GSubst Value → Value → Set
    𝐸 M ρ = fold ρ M
