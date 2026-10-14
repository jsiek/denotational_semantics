{-

  The semantics of CFGᵀ (Language/Typed/CFG.agda) in the graph model
  with errors, as that of CFG (Untyped/Semantics/GraphErr/CFG.agda). The frame
  is the environment, as in Impᵀ (Semantics/GraphErr/Typed/Imp.agda);
  a tail that forgets the slots of a finished scope (p : Δ' ⊑ Δ) sees
  the environment without them (drop). A label means the block it
  indexes, under the meanings of the older blocks (blocks), so a jump
  needs no check.

-}

module Semantics.GraphErr.Typed.CFG where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.ErrorMonad
open import Framework.GraphModel.Env using (Env)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Semantics.GraphErr.Typed.Ops
open import Semantics.GraphErr.Typed.Imp using (Table; tbl; 𝒜; 𝒮; letᵗ) public
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.CFG

open import Data.List using (List; []; _∷_)
open import Data.Nat using (suc)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the meanings of blocks, by label -}
BEnv : List Ctx → Set₁
BEnv Bs = ∀ {Δ} → Bs ∋ Δ → Env Value → 𝒫 Value

{- the environment without the slots after Δ' -}
drop : ∀ {Δ' Δ : Ctx} → Δ' ⊑ Δ → Env Value → Env Value
drop here⊑ ρ = ρ
drop (there⊑ p) ρ = drop p (λ i → ρ (suc i))

⟦_⟧ᵗ : ∀ {Σ Bs Δ} → Tail Σ Bs Δ → Table → BEnv Bs → Env Value → 𝒫 Value
⟦ return s ⟧ᵗ T B ρ = 𝒮 s T ρ
⟦ seq p s t ⟧ᵗ T B ρ = letᵗ (𝒮 s T ρ) λ X → ⟦ t ⟧ᵗ T B (X • drop p ρ)
⟦ goto l ⟧ᵗ T B ρ = B l ρ
⟦ case a p l₁ l₂ ⟧ᵗ T B ρ = caseᵗ (𝒜 a T ρ) (λ X → B l₁ (X • drop p ρ)) (λ X → B l₂ (X • drop p ρ))

{- each block, with the meanings of the older ones -}
blocks : ∀ {Σ Bs} → Blocks Σ Bs → Table → BEnv Bs
blocks (bs ▷ t) T Z = ⟦ t ⟧ᵗ T (blocks bs T)
blocks (bs ▷ t) T (S l) = blocks bs T l

run : ∀ {Σ Δ} → Body Σ Δ → Table → Env Value → 𝒫 Value
run (body bs t) T = ⟦ t ⟧ᵗ T (blocks bs T)

codeᶜ : ∀ {Σ} → Table → ∀ {n} → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ []) → 𝒫 Value
codeᶜ T b = ΛΛᵐ ⟨ (λ X Y → run b T (Y • X • λ _ → init)) , ptt ⟩

⟦_⟧ᶜ : Program → 𝒫 Value
⟦ program {Σ} ds b ⟧ᶜ = run b (tbl (codeᶜ {Σ}) ds) (λ _ → init)
