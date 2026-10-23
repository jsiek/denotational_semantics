{-

  The semantics of ISWIMμ (Mu/Language/ISWIM.agda) in Scott domains: a
  term means a continuous map from environments to the domain of values
  𝔻 (Framework/Scott/), by erasing the types, as in the graph model
  (Mu/Semantics/GraphModel/ISWIM.agda): fold and unfold are the identity.
  Recursion needs no fixed point: self-application, through a recursive
  type, gives it, as in untyped ISWIM, since 𝔻 ≅ 𝓛(… + (𝔻 ⟹ 𝔻) + …).
  Variable x is position idx x of the environment; component i of a
  tuple is its position pos i.

-}

open import MLTT.Spartan using (𝓤₀)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Data.List using (length)

module Mu.Semantics.ScottDomains.ISWIM
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (at)
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env; const; proj) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ)
open import Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Den Env
⟦_⟧s : ∀ {Γ Δ} → All (Tm Γ) Δ → Dens (length Δ)

⟦ ` x ⟧ = at _ 𝔻 (idx x)
⟦ lam N ⟧ = lamᶜ ⟦ N ⟧
⟦ app L M ⟧ = op₂ appᵈ ⟦ L ⟧ ⟦ M ⟧
⟦ lit B c ⟧ = litᶜ (const B c)
⟦ tuple Ms ⟧ = tupleᶜ ⟦ Ms ⟧s
⟦ get i M ⟧ = op₁ (proj (pos i)) ⟦ M ⟧
⟦ inl M ⟧ = op₁ inlᵈ ⟦ M ⟧
⟦ inr M ⟧ = op₁ inrᵈ ⟦ M ⟧
⟦ case L M N ⟧ = caseᶜ ⟦ L ⟧ ⟦ M ⟧ ⟦ N ⟧
⟦ prim p L M ⟧ = op₂ (primD p) ⟦ L ⟧ ⟦ M ⟧
⟦ let′ M N ⟧ = letᶜ ⟦ M ⟧ ⟦ N ⟧
⟦ fold M ⟧ = ⟦ M ⟧
⟦ unfold M ⟧ = ⟦ M ⟧

⟦ [] ⟧s = nil
⟦ M ∷ Ms ⟧s = cons ⟦ M ⟧ ⟦ Ms ⟧s
