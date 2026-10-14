{-

  The semantics of Clos2ᵀ (Language/Typed/Clos2.agda) in the graph model
  with errors, as that of ISWIMᵀ (Semantics/GraphErr/Typed/ISWIM.agda): a
  closure binds its free variables left to right and is a function of
  the argument, whose body sees the argument and the free variables.

-}

module Semantics.GraphErr.Typed.Clos2 where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Framework.GraphModel.Env using (Env)
open import Semantics.GraphErr.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Clos2

open import Data.Fin using (toℕ)
open import Data.List using (replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the environment of the code of a closure: its free variables -}
fv-env : ∀ n → Results (𝒫 Value) (replicate n ■) → Env Value
fv-env zero _ _ = init
fv-env (suc n) ⟨ X , Xs ⟩ zero = X
fv-env (suc n) ⟨ X , Xs ⟩ (suc i) = fv-env n Xs i

⟦_⟧ : ∀ {k A} → Tm k A → Env Value → 𝒫 Value
⟦_⟧s : ∀ {k n} → Vec (Tm k Any) n → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧ ρ = ρ (toℕ x)
⟦ clos {n = n} N Ms ⟧ ρ = binds n (⟦ Ms ⟧s ρ) λ Xs → Λᵐ ⟨ (λ Y → ⟦ N ⟧ (Y • fv-env n Xs)) , ptt ⟩
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
⟦ project t M ⟧ ρ = projectᵗ t (⟦ M ⟧ ρ)

⟦ [] ⟧s ρ = ptt
⟦ M ∷ Ms ⟧s ρ = ⟨ ⟦ M ⟧ ρ , ⟦ Ms ⟧s ρ ⟩
