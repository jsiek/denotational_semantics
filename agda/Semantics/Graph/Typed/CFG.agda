{-

  The semantics of CFGᵀ (Language/Typed/CFG.agda) in the graph model, as
  that of CFG (Untyped/Semantics/Graph/CFG.agda). A tail runs in a frame σ, given
  the meanings B of the blocks it can see (by their typed labels), and
  means a set of values. Atoms and simple expressions are Impᵀ's
  (Semantics/Graph/Typed/Imp.agda).

  * seq p s t is strict in s, like an assignment in Impᵀ: ⋆ ⟨ Λ F , D ⟩,
    where D is the value of s and F X runs t with X in the next slot of
    the frame cut to the context of p (drop);
  * case a p l₁ l₂ is 𝒞, its branches running block l₁ or l₂ with the
    payload in that slot; goto l runs block l in the frame as it is.

  The blocks of a body are given meaning newest first, each with the
  meanings of the older ones (blocks), which are all it can jump to.
  Definitions are given meaning as in Clos5ᵀ (tables).

-}

module Semantics.Graph.Typed.CFG where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Framework.GraphModel.Env using (Env)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Semantics.Graph.Typed.Ops
open import Semantics.Graph.Typed.Imp using (𝒜; 𝒮) public
open import Language.Typed.Type
open import Language.Typed.CFG

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (suc)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the frame cut to the slots of an older context -}
drop : ∀ {Δ' Δ : Ctx} → Δ' ⊑ Δ → Env Value → Env Value
drop here⊑ σ = σ
drop (there⊑ p) σ = drop p (λ i → σ (suc i))

{- the meanings of the visible blocks, by label -}
Meanings : List Ctx → Set₁
Meanings Bs = ∀ {Δ} → Bs ∋ Δ → Env Value → 𝒫 Value

⟦_⟧ᵗ : ∀ {Σ Bs Δ} → Tail Σ Bs Δ → Table Σ → Meanings Bs → Env Value → 𝒫 Value
⟦ return s ⟧ᵗ T B σ = 𝒮 s T σ
⟦ seq p s t ⟧ᵗ T B σ = ⋆ ⟨ Λ ⟨ (λ X → ⟦ t ⟧ᵗ T B (X • drop p σ)) , ptt ⟩ , ⟨ 𝒮 s T σ , ptt ⟩ ⟩
⟦ goto l ⟧ᵗ T B σ = B l σ
⟦ case a p l₁ l₂ ⟧ᵗ T B σ =
  𝒞 ⟨ 𝒜 a T σ , ⟨ (λ X → B l₁ (X • drop p σ)) , ⟨ (λ X → B l₂ (X • drop p σ)) , ptt ⟩ ⟩ ⟩

blocks : ∀ {Σ Bs} → Blocks Σ Bs → Table Σ → Meanings Bs
blocks (bs ▷ t) T Z = ⟦ t ⟧ᵗ T (blocks bs T)
blocks (bs ▷ t) T (S l) = blocks bs T l

{- the start of a body, with its blocks -}
run : ∀ {Σ Δ} → Body Σ Δ → Table Σ → Env Value → 𝒫 Value
run (body bs t) T = ⟦ t ⟧ᵗ T (blocks bs T)

{- the function whose body is b, given the table T -}
code′ : ∀ {Σ} → Table Σ → ∀ {n} → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ []) → 𝒫 Value
code′ T b = Λ ⟨ (λ X → Λ ⟨ (λ Y → run b T (Y • X • λ _ → init)) , ptt ⟩) , ptt ⟩

table : ∀ {Σ} → All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds b ⟧ₚ = run b (table ds) (λ _ → init)
