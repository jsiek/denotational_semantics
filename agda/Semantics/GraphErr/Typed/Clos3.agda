{-

  The semantics of Clos3ᵀ (Language/Typed/Clos3.agda) in the graph model
  with errors: a closure evaluates the tuple of its free variables and is
  its code, a closed function of two arguments (ΛΛᵐ), applied to that
  tuple. Variable x is position idx x of the environment.

-}

module Semantics.GraphErr.Typed.Clos3 where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops using (⋆)
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Framework.GraphModel.Env using (Env)
open import Semantics.GraphErr.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Clos3

open import Data.List using (replicate)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ n} → Vec (Tm Γ Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ clos {n = n} N Ms ⟧ ρ =
  𝒯ᵐ n (⟦ Ms ⟧s ρ) ≫= λ T → ⋆ ⟨ ΛΛᵐ ⟨ (λ X Y → ⟦ N ⟧ (Y • X • λ _ → init)) , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
⟦ app L M ⟧ ρ = appᵗ (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)
⟦ lit B c ⟧ ρ = ℬ B c ptt
⟦ tuple {n = n} Ms ⟧ ρ = 𝒯ᵐ n (⟦ Ms ⟧s ρ)
⟦ get i M ⟧ ρ = getᵗ i (⟦ M ⟧ ρ)
⟦ inl M ⟧ ρ = inlᵐ ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inr M ⟧ ρ = inrᵐ ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ case L M N ⟧ ρ = caseᵗ (⟦ L ⟧ ρ) (λ X → ⟦ M ⟧ (X • ρ)) (λ X → ⟦ N ⟧ (X • ρ))
⟦ prim p L M ⟧ ρ = primᵗ p (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)
⟦ let′ M N ⟧ ρ = ⟦ M ⟧ ρ ≫= λ X → ⟦ N ⟧ (X • ρ)
⟦ inject G M ⟧ ρ = ⟦ M ⟧ ρ
⟦ project G M ⟧ ρ = projectᵗ G (⟦ M ⟧ ρ)

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
