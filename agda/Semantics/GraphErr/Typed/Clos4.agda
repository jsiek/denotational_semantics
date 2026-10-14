{-

  The semantics of Clos4ᵀ (Language/Typed/Clos4.agda) in the graph model
  with errors. Code is a closed function of two arguments (ΛΛᵐ); a call
  binds code, environment and argument and applies the code to both,
  with no check; a closure is a pair. unpack binds the pair and runs the
  body with its environment (cdr) and its code (car), for every length:
  the body for a length other than that of the environment finds no
  component of it. A value of type ⟪ fun ⟫ is a pair, so project ⟪ fun ⟫
  checks for a pair (kind₄).

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
open import Data.Product using (Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the kind of the values of a flat type: a function is a pair -}
kind₄ : Flat → Kind
kind₄ fun = prod
kind₄ G = kindᶠ G

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {Γ n} → Vec (Tm Γ Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (idx x)
⟦ code N ⟧ ρ = ΛΛᵐ ⟨ (λ X Y → ⟦ N ⟧ (Y • X • λ _ → init)) , ptt ⟩
⟦ call L M N ⟧ ρ =
  ⟦ L ⟧ ρ ≫= λ F → ⟦ M ⟧ ρ ≫= λ E → ⟦ N ⟧ ρ ≫= λ X → ⋆ ⟨ ⋆ ⟨ F , ⟨ E , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
⟦ pack L M ⟧ ρ = pairᵐ ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩
⟦ unpack L B ⟧ ρ = ⟦ L ⟧ ρ ≫= λ P w →
  Σ[ n ∈ ℕ ] w ∈ ⟦ B n ⟧ (cdr ⟨ P , ptt ⟩ • car ⟨ P , ptt ⟩ • ρ)
⟦ lit B c ⟧ ρ = ℬ B c ptt
⟦ tuple {n = n} Ms ⟧ ρ = 𝒯ᵐ n (⟦ Ms ⟧s ρ)
⟦ get i M ⟧ ρ = getᵗ i (⟦ M ⟧ ρ)
⟦ inl M ⟧ ρ = inlᵐ ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ inr M ⟧ ρ = inrᵐ ⟨ ⟦ M ⟧ ρ , ptt ⟩
⟦ case L M N ⟧ ρ = caseᵗ (⟦ L ⟧ ρ) (λ X → ⟦ M ⟧ (X • ρ)) (λ X → ⟦ N ⟧ (X • ρ))
⟦ prim p L M ⟧ ρ = primᵗ p (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)
⟦ let′ M N ⟧ ρ = ⟦ M ⟧ ρ ≫= λ X → ⟦ N ⟧ (X • ρ)
⟦ inject G M ⟧ ρ = ⟦ M ⟧ ρ
⟦ project G M ⟧ ρ = projectᵗ (kind₄ G) (⟦ M ⟧ ρ)

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
