{-

  The semantics of Clos5ᵀ (Language/Typed/Clos5.agda) in the graph model
  with errors: that of Clos4ᵀ (Semantics/GraphErr/Typed/Clos4.agda), with
  the code of a function a reference to a global definition. Under a
  table T, the meanings of the definitions by their position from the
  oldest (as in Untyped/Semantics/GraphErr/Clos5.agda), a reference f means
  T (lvl f); let binds a value of any type.

  The table of a program (tbl) gives each definition the meanings of
  the older ones only, and errcode at any other position, so that it is
  well founded; globalize makes only references to older definitions.
  tbl is generic in what the definitions are, for Impᵀ and CFGᵀ too.

-}

module Semantics.GraphErr.Typed.Clos5 where

open import Framework.GraphModel.ErrorPrelude
open import Framework.GraphModel.Ops using (⋆; car; cdr)
open import Semantics.GraphErr.Typed.Ops
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.Clos5

open import Data.List using (List; _∷_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≟_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- the meanings of the global definitions, by their levels -}
Table : Set₁
Table = ℕ → 𝒫 Value

⟦_⟧[_] : ∀ {Σ Γ A} → Tm Σ Γ A → Table → Env Value → 𝒫 Value
⟦_⟧s[_] : ∀ {Σ Γ n} → Vec (Tm Σ Γ Any) n → Table → Env Value → Results (𝒫 Value) (replicate n ■)

⟦ ` x ⟧[ T ] ρ = ρ (idx x)
⟦ fun-ref f ⟧[ T ] ρ = T (lvl f)
⟦ pack L M ⟧[ T ] ρ = pairᵐ ⟨ ⟦ L ⟧[ T ] ρ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩
⟦ callc L M ⟧[ T ] ρ = ⟦ L ⟧[ T ] ρ ≫= λ P → ⟦ M ⟧[ T ] ρ ≫= λ X →
  ⋆ ⟨ ⋆ ⟨ car ⟨ P , ptt ⟩ , ⟨ cdr ⟨ P , ptt ⟩ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
⟦ lit B c ⟧[ T ] ρ = ℬ B c ptt
⟦ tuple {n = n} Ms ⟧[ T ] ρ = 𝒯ᵐ n (⟦ Ms ⟧s[ T ] ρ)
⟦ get i M ⟧[ T ] ρ = getᵗ i (⟦ M ⟧[ T ] ρ)
⟦ inl M ⟧[ T ] ρ = inlᵐ ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ inr M ⟧[ T ] ρ = inrᵐ ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩
⟦ case L M N ⟧[ T ] ρ = caseᵗ (⟦ L ⟧[ T ] ρ) (λ X → ⟦ M ⟧[ T ] (X • ρ)) (λ X → ⟦ N ⟧[ T ] (X • ρ))
⟦ prim p L M ⟧[ T ] ρ = primᵗ p (⟦ L ⟧[ T ] ρ) (⟦ M ⟧[ T ] ρ)
⟦ let′ M N ⟧[ T ] ρ = ⟦ M ⟧[ T ] ρ ≫= λ X → ⟦ N ⟧[ T ] (X • ρ)
⟦ inject G M ⟧[ T ] ρ = ⟦ M ⟧[ T ] ρ
⟦ project t M ⟧[ T ] ρ = projectᵠ kind₄ t (⟦ M ⟧[ T ] ρ)

⟦ [] ⟧s[ T ] ρ = ptt
⟦ M ∷ Ms ⟧s[ T ] ρ = ⟨ ⟦ M ⟧[ T ] ρ , ⟦ Ms ⟧s[ T ] ρ ⟩

{- the code of a definition: its body on the environment X and argument Y -}
code₅ : ∀ {Σ} → Table → ∀ {n} → Code Σ n → 𝒫 Value
code₅ T N = ΛΛᵐ ⟨ (λ X Y → ⟦ N ⟧[ T ] (Y • X • λ _ → init)) , ptt ⟩

{- the table of a list of definitions, newest first: each sees the older ones -}
tbl : ∀ {P : ℕ → Set} → (Table → ∀ {n} → P n → 𝒫 Value) → ∀ {ns} → All P ns → Table
tbl c [] k = errcode
tbl c {_ ∷ ns} (d ∷ ds) k with k ≟ length ns
... | yes _ = c (tbl c ds) d
... | no _ = tbl c ds k

⟦_⟧₅ : Program → 𝒫 Value
⟦ program {Σ} ds M ⟧₅ = ⟦ M ⟧[ tbl (code₅ {Σ}) ds ] (λ _ → init)
