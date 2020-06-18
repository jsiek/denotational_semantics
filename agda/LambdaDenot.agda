open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Structures
import ValueStructAux

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

  open import Fold Op sig
  open RelBind {lsuc lzero}{Value}{Value → Set}{Value}{Value → Set} _≡_ _≡_

  module Experiment
    (𝐹 : (Value → Value → Set) → (Value → Set))
    (_○_ : (Value → Set) → (Value → Set) → (Value → Set))
    (𝐹-cong : ∀ {x y : Bind Value (Value → Set) 1} → _⩳_ {b = 1} x y → 𝐹 x ≡ 𝐹 y)
    where
    {-
    (dᶠ ○ dₐ) w = Σ[ v ∈ Value ] dᶠ (v ↦ w) × dₐ v
    -}
    open import ScopedTuple

    denot-op : (op : Op) → Tuple (sig op) (Bind Value (Value → Set))
             → Value → Set
    denot-op lam ⟨ f , tt ⟩ = 𝐹 f
    denot-op app ⟨ dᶠ , ⟨ dₐ , tt ⟩ ⟩ = dᶠ ○ dₐ

    open import GenericSubstitution

    ValueIsShiftable : Shiftable Value
    ValueIsShiftable = record { var→val = λ x → ⊥ ; shift = λ v → v
                              ; var→val-suc-shift = refl }
    open Shiftable ValueIsShiftable                        

    open import Env ValueIsShiftable
    
    DenotFold : FoldEnv Env Value (Value → Set)
    DenotFold = record { ret = λ v w → w ⊑ v; fold-op = denot-op
                       ; env = FunIsEnv }
    open FoldEnv DenotFold

    𝐸 : Term → Env → Value → Set
    𝐸 M ρ = fold ρ M

    op-cong : (op : Op) (rs rs' : Tuple (sig op) (Bind Value (Value → Set)))
       → zip _⩳_ rs rs' → denot-op op rs ≡ denot-op op rs'
    op-cong lam ⟨ fst , tt ⟩ ⟨ fst₁ , tt ⟩ ⟨ fst₂ , tt ⟩ = 𝐹-cong fst₂
    op-cong app ⟨ fst , ⟨ fst₁ , tt ⟩ ⟩ ⟨ fst₂ , ⟨ fst₃ , tt ⟩ ⟩ ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl

    {-
    open import Preserve Op sig
    SPFE : SubstPreserveFoldEnv DenotFold
    SPFE = record
             { shiftᶜ = λ d → d
             ; op-cong = op-cong
             ; ret-inj = {!!} {- ouch! -}
             ; shift-ret = λ vᶠ → refl
             ; op-shift = λ op {rs↑}{rs} z → op-cong op rs↑ rs z
             }
    -}
