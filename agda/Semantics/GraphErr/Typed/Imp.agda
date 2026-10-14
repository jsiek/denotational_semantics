{-

  The semantics of Impᵀ (Language/Typed/Imp.agda) in the graph model
  with errors, continuation-passing, as that of Imp
  (Semantics/GraphErr/ImpK.agda). The frame is the environment: slot x
  is position idx x, as variable x is in Clos5ᵀ, so the frame needs no
  checks. A simple expression means what it means as an expression of
  Monᵀ, that is, in Clos5ᵀ (𝒮). x := e₁; e₂ runs e₁ with the
  continuation that binds its value to the next slot (letᵗ, the
  application of a function, as the X86 machine's slot writes are) and
  runs e₂; case binds the payload to the next slot and runs a branch.

-}

module Semantics.GraphErr.Typed.Imp where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops using (⋆)
open import Framework.GraphModel.ErrorMonad
open import Framework.GraphModel.Env using (Env)
open import Semantics.GraphErr.Typed.Ops
open import Semantics.GraphErr.Typed.Clos5 using (Table; ⟦_⟧[_]; tbl) public
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open import Language.Typed.Imp

open import Data.List using ([]; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- a simple expression, as one of Monᵀ -}
⌞_⌟ : ∀ {Σ Δ A} → Simple Σ Δ A → M.Exp Σ Δ A
⌞ atm a ⌟ = M.atm a
⌞ pack a b ⌟ = M.pack a b
⌞ callc a b ⌟ = M.callc a b
⌞ tuple as ⌟ = M.tuple as
⌞ get i a ⌟ = M.get i a
⌞ inl a ⌟ = M.inl a
⌞ inr a ⌟ = M.inr a
⌞ prim p a b ⌟ = M.prim p a b
⌞ inject G a ⌟ = M.inject G a
⌞ project t a ⌟ = M.project t a

𝒜 : ∀ {Σ Δ A} → Atm Σ Δ A → Table → Env Value → 𝒫 Value
𝒜 a = ⟦ M.⌜ a ⌝ᵃ ⟧[_]

𝒮 : ∀ {Σ Δ A} → Simple Σ Δ A → Table → Env Value → 𝒫 Value
𝒮 s = ⟦ M.⌜ ⌞ s ⌟ ⌝ ⟧[_]

{- bind D to the next slot, then F -}
letᵗ : 𝒫 Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
letᵗ D F = D ≫= λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩

Kont : Set₁
Kont = 𝒫 Value → 𝒫 Value

⟦_⟧ᴷ : ∀ {Σ Δ A} → Exp Σ Δ A → Table → Env Value → Kont → 𝒫 Value
⟦ simple s ⟧ᴷ T ρ κ = κ (𝒮 s T ρ)
⟦ assign e₁ e₂ ⟧ᴷ T ρ κ = ⟦ e₁ ⟧ᴷ T ρ λ D → letᵗ D λ X → ⟦ e₂ ⟧ᴷ T (X • ρ) κ
⟦ case a e₁ e₂ ⟧ᴷ T ρ κ = caseᵗ (𝒜 a T ρ) (λ X → ⟦ e₁ ⟧ᴷ T (X • ρ) κ) (λ X → ⟦ e₂ ⟧ᴷ T (X • ρ) κ)

{- the code of a definition: its body on the environment X and argument Y -}
codeᵢ : ∀ {Σ} → Table → ∀ {n} → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any → 𝒫 Value
codeᵢ T e = ΛΛᵐ ⟨ (λ X Y → ⟦ e ⟧ᴷ T (Y • X • λ _ → init) λ D → D) , ptt ⟩

⟦_⟧ᵢ : Program → 𝒫 Value
⟦ program {Σ} ds e ⟧ᵢ = ⟦ e ⟧ᴷ (tbl (codeᵢ {Σ}) ds) (λ _ → init) λ D → D
