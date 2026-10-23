{-

  The semantics of CFGμ (Mu/Language/CFG.agda) in Scott domains, as in
  the graph model (Mu/Semantics/GraphModel/CFG.agda). A tail runs in a frame
  σ, given the meanings B of the blocks it can see (by their typed
  labels), and means a value, continuously in σ. Atoms and simple
  expressions are Impμ's (Mu/Semantics/ScottDomains/Imp.agda).

  * seq p s t is strict in s, like an assignment in Impμ: app (Λ F) D,
    where D is the value of s and F X runs t with X in the next slot of
    the frame cut to the context of p (drop);
  * case a p l₁ l₂ is a case, its branches running block l₁ or l₂ with
    the payload in that slot; goto l runs block l in the frame as it is.

  The blocks of a body are given meaning newest first, each with the
  meanings of the older ones (blocks).

-}

open import MLTT.Spartan using (𝓤₀; 𝓤₁; _̇)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type
open import Mu.Language.CFG
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Mu.Framework.AllUtil using (All)
open import Data.List using (List; []; _∷_)

module Mu.Semantics.ScottDomains.CFG
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env) renaming (app to appᵈ)
open import Framework.Scott.Semantics pt fe pe
open import Mu.Semantics.ScottDomains.Ops pt fe pe
open import Mu.Semantics.ScottDomains.Imp pt fe pe using (𝒜; 𝒮) public

{- the frame cut to the slots of an older context -}
drop : ∀ {Δ' Δ : Ctx} → Δ' ⊑ Δ → DCPO[ Env , Env ]
drop here⊑ = id₁ Env
drop (there⊑ p) = ∘₁ Env Env Env shiftᶜ (drop p)

{- the meanings of the visible blocks, by label -}
Meanings : List Ctx → 𝓤₁ ̇
Meanings Bs = ∀ {Δ} → Bs ∋ Δ → Den Env

⟦_⟧ᵗ : ∀ {Σ R Bs Δ} → Tail Σ R Bs Δ → Table Σ → Meanings Bs → Den Env
⟦ return s ⟧ᵗ T B = 𝒮 s T
⟦ seq p s t ⟧ᵗ T B = op₂ appᵈ (∘₁ Env Env 𝔻 (drop p) (lamᶜ (⟦ t ⟧ᵗ T B))) (𝒮 s T)
⟦ goto l ⟧ᵗ T B = B l
⟦ case a p l₁ l₂ ⟧ᵗ T B =
  casesᶜ (𝒜 a T) (∘₁ Env Env (𝔻 ⟹₁ 𝔻) (drop p) (abs (B l₁))) (∘₁ Env Env (𝔻 ⟹₁ 𝔻) (drop p) (abs (B l₂)))

blocks : ∀ {Σ R Bs} → Blocks Σ R Bs → Table Σ → Meanings Bs
blocks (bs ▷ t) T Z = ⟦ t ⟧ᵗ T (blocks bs T)
blocks (bs ▷ t) T (S l) = blocks bs T l

{- the start of a body, with its blocks -}
run : ∀ {Σ R Δ} → Body Σ R Δ → Table Σ → Den Env
run (body bs t) T = ⟦ t ⟧ᵗ T (blocks bs T)

{- the function whose body is b, given the table T -}
code′ : ∀ {Σ} → Table Σ → ∀ {s} → Body Σ (DSig.cod s) (Args s) → ⟨ 𝔻 ⟩
code′ T b = codeᶜ (run b T)

table : ∀ {Σ} → All (λ s → Body Σ (DSig.cod s) (Args s)) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : ∀ {A} → Program A → ⟨ 𝔻 ⟩
⟦ program ds b ⟧ₚ = run b (table ds) · (λ _ → init)
