{-

  The semantics of Closμ (Mu/Language/Clos.agda) in Scott domains, as
  in the graph model (Mu/Semantics/GraphModel/Clos.agda): a closure is
  strict in its free variables (guard) and is the function of the
  argument whose body sees the argument and the values of the free
  variables (closureᶜ, Framework/Scott/Semantics.agda); otherwise as
  FPC (Mu/Semantics/ScottDomains/FPC.agda).

-}

open import MLTT.Spartan using (𝓤₀)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type
open import Mu.Language.Clos
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Data.List using (length)
open import Data.Fin using (Fin)

module Mu.Semantics.ScottDomains.Clos
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (at; ∘₁; Pow)
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env; const; proj) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ)
open import Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Den Env
⟦_⟧s : ∀ {Γ Δ} → All (Tm Γ) Δ → Dens (length Δ)

⟦ ` x ⟧ = at _ 𝔻 (idx x)
⟦ clos {Δ} N Ms ⟧ = ∘₁ Env (Pow (Fin (length Δ)) 𝔻) 𝔻 ⟦ Ms ⟧s (closureᶜ (length Δ) ⟦ N ⟧)
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
