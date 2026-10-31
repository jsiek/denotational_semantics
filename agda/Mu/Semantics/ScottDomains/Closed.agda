{-

  The environment of a closed FPC program in Scott domains: every
  variable means init, the empty tuple, as in the graph model
  (Mu/Semantics/GraphModel/Closed.agda). It only matters for open terms.

-}

open import MLTT.Spartan using (𝓤₀)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

module Mu.Semantics.ScottDomains.Closed
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (⟨_⟩)
open import Framework.Scott.Ops pt fe pe using (Env)
open import Framework.Scott.Semantics pt fe pe using (init)

ρ₀ : ⟨ Env ⟩
ρ₀ = λ _ → init
