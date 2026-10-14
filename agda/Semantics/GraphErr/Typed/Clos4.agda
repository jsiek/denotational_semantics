{-

  The semantics of Clos4ᵀ (Language/Typed/Clos4.agda) in the graph model
  with errors. Code is a closed function of two arguments (ΛΛᵐ); a closure
  is a pair of code and environment. callc binds the closure and the
  argument and applies the closure's code (car) to its environment (cdr)
  and the argument, with no check. A value of type ⟪ fun ⟫ is a pair, so project sees a pair
  as a function (kind₄).

-}

module Semantics.GraphErr.Typed.Clos4 where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops using (⋆; car; cdr)
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Framework.GraphModel.Env using (Env)
open import Semantics.GraphErr.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Clos4

open import Data.List using (replicate)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the kind of a value, for project: a pair (a closure) is a function,
   and code is not (it is not a value of type Any) -}
kind₄ : Kind → Kind
kind₄ prod = fun
kind₄ fun = error
kind₄ k = k

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ n} → Vec (Tm Γ Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ code N ⟧ ρ = ΛΛᵐ ⟨ (λ X Y → ⟦ N ⟧ (Y • X • λ _ → init)) , ptt ⟩
⟦ pack L M ⟧ ρ = pairᵐ ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ callc L M ⟧ ρ = ⟦ L ⟧ ρ ≫= λ P → ⟦ M ⟧ ρ ≫= λ X →
  ⋆ ⟨ ⋆ ⟨ car ⟨ P , ptt ⟩ , ⟨ cdr ⟨ P , ptt ⟩ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
⟦ lit B c ⟧ ρ = ℬ B c ptt
⟦ tuple {n = n} Ms ⟧ ρ = 𝒯ᵐ n (⟦ Ms ⟧s ρ)
⟦ get i M ⟧ ρ = getᵗ i (⟦ M ⟧ ρ)
⟦ inl M ⟧ ρ = inlᵐ ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inr M ⟧ ρ = inrᵐ ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ case L M N ⟧ ρ = caseᵗ (⟦ L ⟧ ρ) (λ X → ⟦ M ⟧ (X • ρ)) (λ X → ⟦ N ⟧ (X • ρ))
⟦ prim p L M ⟧ ρ = primᵗ p (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)
⟦ let′ M N ⟧ ρ = ⟦ M ⟧ ρ ≫= λ X → ⟦ N ⟧ (X • ρ)
⟦ inject G M ⟧ ρ = ⟦ M ⟧ ρ
⟦ project t M ⟧ ρ = projectᵠ kind₄ t (⟦ M ⟧ ρ)

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
