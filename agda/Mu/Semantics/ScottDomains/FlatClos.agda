{-

  The semantics of FlatClosμ (Mu/Language/FlatClos.agda) in Scott domains, as
  in the graph model (Mu/Semantics/GraphModel/FlatClos.agda): code is a closed
  function of two arguments (codeᶜ, Framework/Scott/Semantics.agda), a
  closure the pair of code and environment, and callc applies the
  closure's code (car) to its environment (cdr) and the argument;
  otherwise as ISWIMμ (Mu/Semantics/ScottDomains/ISWIM.agda).

-}

open import MLTT.Spartan using (𝓤₀)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type
open import Mu.Language.FlatClos
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Data.List using (length)

module Mu.Semantics.ScottDomains.FlatClos
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (at)
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env; const; proj; pair; car; cdr) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ)
open import Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)

⟦_⟧ : ∀ {Γ A} → Tm Γ A → Den Env
⟦_⟧s : ∀ {Γ Δ} → All (Tm Γ) Δ → Dens (length Δ)

⟦ ` x ⟧ = at _ 𝔻 (idx x)
⟦ code N ⟧ = litᶜ (codeᶜ ⟦ N ⟧)
⟦ pack L M ⟧ = op₂ pair ⟦ L ⟧ ⟦ M ⟧
⟦ callc L M ⟧ = op₂ appᵈ (op₂ appᵈ (op₁ car ⟦ L ⟧) (op₁ cdr ⟦ L ⟧)) ⟦ M ⟧
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
