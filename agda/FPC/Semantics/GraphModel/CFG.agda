{-

  The semantics of CFGμ (FPC/Language/CFG.agda) in the graph model, as
  that of CFGᵀ (ISWIM/Semantics/Graph/Typed/CFG.agda), in a fixed frame. A
  tail runs in a frame σ, given the meanings B of the blocks it can see
  (by their typed labels), and means a set of values. Atoms and simple
  expressions are Impμ's (FPC/Semantics/GraphModel/Imp.agda).

  * seq x s p t is strict in s, like an assignment in Impμ:
    ⋆ ⟨ Λ F , D ⟩, where D is the value of s and F X runs t in the
    frame with X written to slot x;
  * case a x y l₁ l₂ is 𝒞; its branches write the payload to slot x and
    run block l₁, or write it to slot y and run block l₂; goto l runs
    block l in the frame as it is.

  The blocks of a body are given meaning newest first, each with the
  meanings of the older ones (blocks).

-}

module FPC.Semantics.GraphModel.CFG where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops
open import FPC.Semantics.GraphModel.Ops
open import FPC.Semantics.GraphModel.Imp using (𝒜; 𝒮) public
open import FPC.Language.Type
open import FPC.Language.CFG
open import FPC.Framework.AllUtil using (All)

open import Data.List using (List; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the meanings of the visible blocks, by label -}
Meanings : ∀ {Δ} → List (Inits Δ) → Set₁
Meanings Bs = ∀ {I} → Bs ∋ I → Env Value → 𝒫 Value

⟦_⟧ᵗ : ∀ {Σ R Δ Bs I} → Tail Σ R Δ Bs I → Table Σ → Meanings Bs
  → Env Value → 𝒫 Value
⟦ return s ⟧ᵗ T B σ = 𝒮 s T σ
⟦ seq x s _ t ⟧ᵗ T B σ =
  ⋆ ⟨ Λ ⟨ (λ X → ⟦ t ⟧ᵗ T B (σ [ idx x ≔ X ])) , ptt ⟩ , ⟨ 𝒮 s T σ , ptt ⟩ ⟩
⟦ goto l ⟧ᵗ T B σ = B l σ
⟦ case a x y l₁ l₂ ⟧ᵗ T B σ =
  𝒞
    ⟨ 𝒜 a T σ
      ,
      ⟨ (λ X → B l₁ (σ [ idx x ≔ X ]))
        , ⟨ (λ X → B l₂ (σ [ idx y ≔ X ])) , ptt ⟩ ⟩ ⟩

blocks : ∀ {Σ R Δ Bs} → Blocks Σ R Δ Bs → Table Σ → Meanings Bs
blocks (bs ▷ t) T Z = ⟦ t ⟧ᵗ T (blocks bs T)
blocks (bs ▷ t) T (S l) = blocks bs T l

{- the start of a body, with its blocks -}
run : ∀ {Σ R Γ} → Body Σ R Γ → Table Σ → Env Value → 𝒫 Value
run (body Δ p bs t) T = ⟦ t ⟧ᵗ T (blocks bs T)

{- the function whose body is b, given the table T -}
code′ : ∀ {Σ} → Table Σ → ∀ {s} → Body Σ (DSig.cod s) (Args s) → 𝒫 Value
code′ T b@(body Δ p bs t) =
  Λ ⟨ (λ X → Λ ⟨ (λ Y → run b T (start p X Y)) , ptt ⟩) , ptt ⟩

table : ∀ {Σ} → All (λ s → Body Σ (DSig.cod s) (Args s)) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : ∀ {A} → Program A → 𝒫 Value
⟦ program ds b ⟧ₚ = run b (table ds) (λ _ → init)
