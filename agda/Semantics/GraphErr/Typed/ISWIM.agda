{-

  The semantics of ISWIMᵀ (Language/Typed/ISWIM.agda) in the graph model
  with errors, with the typed operators (Semantics/GraphErr/Typed/Ops.agda):
  no operator checks the kind of an operand but project. Defined by
  recursion on typed terms; variable x is position toℕ x of the
  environment.

-}

module Semantics.GraphErr.Typed.ISWIM where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Framework.GraphModel.Env using (Env)
open import Semantics.GraphErr.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.ISWIM

open import Data.Fin using (toℕ)
open import Data.List using (replicate)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

⟦_⟧ : ∀ {k A} → Tm k A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {k n} → Vec (Tm k Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (toℕ x)
⟦ lam N ⟧ ρ = Λᵐ ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩
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
⟦ project G M ⟧ ρ = projectᵗ (kindᶠ G) (⟦ M ⟧ ρ)

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
