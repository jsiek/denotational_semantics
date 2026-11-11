{-

  The semantics of CFGμ (FPC/Language/CFG.agda) in Scott domains, as in
  the graph model (FPC/Semantics/GraphModel/CFG.agda). A tail runs in a
  frame σ, the environment whose position idx x is slot x, as in Impμ;
  given the meanings B of the blocks it can see (by their typed labels),
  it means a value, continuously in σ. Atoms and simple expressions are
  Impμ's (FPC/Semantics/ScottDomains/Imp.agda).

  * seq x s p t is strict in s, like an assignment in Impμ: app (Λ F) D,
    where D is the value of s and F X writes X to slot x in place and
    runs t (lamAt, FPC/Semantics/ScottDomains/Ops.agda);
  * case a x y l₁ l₂ is a case, its branches writing the payload to slot
    x and running block l₁, or to slot y and running block l₂; goto l
    runs block l in the frame as it is.

  The blocks of a body are given meaning newest first, each with the
  meanings of the older ones (blocks).

-}

open import MLTT.Spartan using (𝓤₀; 𝓤₁; _̇)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import FPC.Language.Type
open import FPC.Language.CFG
open import FPC.Framework.AllUtil using (All)
open import Data.List using (List; []; _∷_)

module FPC.Semantics.ScottDomains.CFG
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env) renaming (app to appᵈ)
open import Framework.Scott.Semantics pt fe pe
open import FPC.Semantics.ScottDomains.Ops pt fe pe
open import FPC.Semantics.ScottDomains.Imp pt fe pe using (𝒜; 𝒮) public

{- the meanings of the visible blocks, by label -}
Meanings : ∀ {Δ} → List (Inits Δ) → 𝓤₁ ̇
Meanings Bs = ∀ {I} → Bs ∋ I → Den Env

⟦_⟧ᵗ : ∀ {Σ R Δ Bs I} → Tail Σ R Δ Bs I → Table Σ → Meanings Bs → Den Env
⟦ return s ⟧ᵗ T B = 𝒮 s T
⟦ seq x s p t ⟧ᵗ T B = op₂ appᵈ (lamAt (idx x) (⟦ t ⟧ᵗ T B)) (𝒮 s T)
⟦ goto l ⟧ᵗ T B = B l
⟦ case a x y l₁ l₂ ⟧ᵗ T B =
  casesᶜ (𝒜 a T) (absAt (idx x) (B l₁)) (absAt (idx y) (B l₂))

blocks : ∀ {Σ R Δ Bs} → Blocks Σ R Δ Bs → Table Σ → Meanings Bs
blocks (bs ▷ t) T Z = ⟦ t ⟧ᵗ T (blocks bs T)
blocks (bs ▷ t) T (S l) = blocks bs T l

{- the start of a body, with its blocks -}
run : ∀ {Σ R Γ} → Body Σ R Γ → Table Σ → Den Env
run (body Δ p bs t) T = ⟦ t ⟧ᵗ T (blocks bs T)

{- the function whose body is b, given the table T -}
code′ : ∀ {Σ} → Table Σ → ∀ {s} → Body Σ (DSig.cod s) (Args s) → ⟨ 𝔻 ⟩
code′ T b = codeᶠ (Body.params b) (run b T)

table : ∀ {Σ} → All (λ s → Body Σ (DSig.cod s) (Args s)) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : ∀ {A} → Program A → ⟨ 𝔻 ⟩
⟦ program ds b ⟧ₚ = run b (table ds) · (λ _ → init)
