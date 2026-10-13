module Semantics.GraphErr.ImpK where
{-

 The continuation-passing semantics of Imp (Language/Imp.agda) in the
 graph model with errors: that of Semantics/Graph/ImpK.agda, with the
 error-propagating operators and the frame checks of the machine
 (Semantics/CEK/Imp.agda), Semantics/GraphErr/Imp.agda.

 x := e₁; e₂ runs e₁ with the continuation that, given its value D and
 store σ', errs if x is beyond the frame (once D is computed) and is
 otherwise strict in D like let in Clos5 (letᵉ). case a x e₁ e₂ errs if
 x is beyond the frame, and is otherwise 𝒞ᵉ on a, each branch with x
 bound to the payload and then κ.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.ErrorOps
open import Semantics.GraphErr.Imp public
open import Language.Imp

open import Data.Nat using (ℕ; _⊔_)
open import Data.List using (List)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

Kont : Set₁
Kont = 𝒫 Value → Store → 𝒫 Value

⟦_⟧ᴷ[_] : Exp → Table → ℕ → Store → Kont → 𝒫 Value
⟦ simple s ⟧ᴷ[ T ] n σ κ = κ (𝒮 T n σ s) σ
⟦ case a x e₁ e₂ ⟧ᴷ[ T ] n σ κ = checkedᵉ n x (𝒜 T n σ a)
  (𝒞ᵉ ⟨ 𝒜 T n σ a , ⟨ (λ X → ⟦ e₁ ⟧ᴷ[ T ] n (σ [ x ↦ X ]) κ) , ⟨ (λ X → ⟦ e₂ ⟧ᴷ[ T ] n (σ [ x ↦ X ]) κ) , ptt ⟩ ⟩ ⟩)
⟦ assign x e₁ e₂ ⟧ᴷ[ T ] n σ κ = ⟦ e₁ ⟧ᴷ[ T ] n σ (λ D σ' → checkedᵉ n x D
  (letᵉ ⟨ D , ⟨ (λ X → ⟦ e₂ ⟧ᴷ[ T ] n (σ' [ x ↦ X ]) κ) , ptt ⟩ ⟩))

halt : Kont
halt D σ = D

{- the code of a definition: its body runs in a fresh frame of max(2, n)
   slots -}
code : Table → Body → 𝒫 Value
code T (body n e) = ΛΛᵉ ⟨ (λ X Y → ⟦ e ⟧ᴷ[ T ] (2 ⊔ n) (frame X Y) halt) , ptt ⟩

table : List Body → Table
table = tables code

⟦_⟧ᴷₚ : Program → 𝒫 Value
⟦ program ds (body n e) ⟧ᴷₚ = ⟦ e ⟧ᴷ[ table ds ] n zeros halt
