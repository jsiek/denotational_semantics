module Semantics.GraphErr.CFG where
{-

 The semantics of CFG (Language/CFG.agda) in the graph model with
 errors: that of Semantics/Graph/CFG.agda, with the error-propagating
 operators and the checks of the machine (Semantics/CEK/CFG.agda): an
 assignment or the payload of a case beyond the frame errs, and so does a
 jump to a block that is not there (blocks, at a missing label, is
 {ω}). A body runs in a frame of max(2, n) slots when called, of n for
 main, as in the machine.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErr.Imp public
open import Language.CFG

open import Data.Nat using (ℕ; _≟_; _⊔_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- the meanings of the visible blocks, by label -}
Blocks : Set₁
Blocks = ℕ → Store → 𝒫 Value

⟦_⟧[_] : Tail → Table → ℕ → Blocks → Store → 𝒫 Value
⟦ return s ⟧[ T ] n B σ = 𝒮 T n σ s
⟦ seq x s t ⟧[ T ] n B σ = frameᵐ n x (𝒮 T n σ s)
  (letᵐ ⟨ 𝒮 T n σ s , ⟨ (λ X → ⟦ t ⟧[ T ] n B (σ [ x ↦ X ])) , ptt ⟩ ⟩)
⟦ goto l ⟧[ T ] n B σ = B l σ
⟦ case a x l₁ l₂ ⟧[ T ] n B σ = frameᵐ n x (payloadᵐ (𝒜 T n σ a))
  (𝒞ᵐ ⟨ 𝒜 T n σ a , ⟨ (λ X → B l₁ (σ [ x ↦ X ])) , ⟨ (λ X → B l₂ (σ [ x ↦ X ])) , ptt ⟩ ⟩ ⟩)

{- the blocks bs (newest first), each with the meanings of the older ones;
   a missing block errs -}
blocks : Table → ℕ → List Tail → Blocks
blocks T n [] l σ = init
blocks T n (t ∷ bs) l with l ≟ length bs
... | yes _ = ⟦ t ⟧[ T ] n (blocks T n bs)
... | no _ = blocks T n bs l

{- the start of a body, in a frame of m slots, with its blocks -}
run : Table → ℕ → Body → Store → 𝒫 Value
run T m (body n bs t) = ⟦ t ⟧[ T ] m (blocks T m bs)

code : Table → Body → 𝒫 Value
code T b = ΛΛᵐ ⟨ (λ X Y → run T (2 ⊔ Body.locals b) b (frame X Y)) , ptt ⟩

table : List Body → Table
table = tables code

⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds b ⟧ₚ = run (table ds) (Body.locals b) b zeros
