{-

  The semantics of Clos5μ (Mu/Language/Clos5.agda) in Scott domains, as
  that of Clos4μ (Mu/Semantics/Scott/Clos4.agda), given a table T of the
  meanings of the global definitions: fun-ref f means T f. As in the
  graph model (Mu/Semantics/Graph/Clos5.agda), the definitions of a
  program are given meaning newest first, each with the table of the
  older ones (tables, Mu/Semantics/Scott/Ops.agda), and main with the
  table of all of them.

-}

open import MLTT.Spartan using (𝓤₀)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type
open import Mu.Language.Clos5
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Data.List using (List; length)

module Mu.Semantics.Scott.Clos5
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (at; ⟨_⟩; _·_)
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env; const; proj; pair; car; cdr) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ)
open import Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.Scott.Ops pt fe pe

⟦_⟧[_] : ∀ {Σ Γ A} → Tm Σ Γ A → Table Σ → Den Env
⟦_⟧s[_] : ∀ {Σ Γ Δ} → All (Tm Σ Γ) Δ → Table Σ → Dens (length Δ)

⟦ ` x ⟧[ T ] = at _ 𝔻 (idx x)
⟦ fun-ref f ⟧[ T ] = litᶜ (T f)
⟦ pack L M ⟧[ T ] = op₂ pair ⟦ L ⟧[ T ] ⟦ M ⟧[ T ]
⟦ callc L M ⟧[ T ] = op₂ appᵈ (op₂ appᵈ (op₁ car ⟦ L ⟧[ T ]) (op₁ cdr ⟦ L ⟧[ T ])) ⟦ M ⟧[ T ]
⟦ lit B c ⟧[ T ] = litᶜ (const B c)
⟦ tuple Ms ⟧[ T ] = tupleᶜ ⟦ Ms ⟧s[ T ]
⟦ get i M ⟧[ T ] = op₁ (proj (pos i)) ⟦ M ⟧[ T ]
⟦ inl M ⟧[ T ] = op₁ inlᵈ ⟦ M ⟧[ T ]
⟦ inr M ⟧[ T ] = op₁ inrᵈ ⟦ M ⟧[ T ]
⟦ case L M N ⟧[ T ] = caseᶜ ⟦ L ⟧[ T ] ⟦ M ⟧[ T ] ⟦ N ⟧[ T ]
⟦ prim p L M ⟧[ T ] = op₂ (primD p) ⟦ L ⟧[ T ] ⟦ M ⟧[ T ]
⟦ let′ M N ⟧[ T ] = letᶜ ⟦ M ⟧[ T ] ⟦ N ⟧[ T ]
⟦ fold M ⟧[ T ] = ⟦ M ⟧[ T ]
⟦ unfold M ⟧[ T ] = ⟦ M ⟧[ T ]

⟦ [] ⟧s[ T ] = nil
⟦ M ∷ Ms ⟧s[ T ] = cons ⟦ M ⟧[ T ] ⟦ Ms ⟧s[ T ]

{- the function whose code is N, given the table T: it takes the tuple of
   its free variables X and then the argument Y -}
code′ : ∀ {Σ} → Table Σ → ∀ {s} → Code Σ s → ⟨ 𝔻 ⟩
code′ T N = codeᶜ ⟦ N ⟧[ T ]

table : ∀ {Σ} → All (Code Σ) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : ∀ {A} → Program A → ⟨ 𝔻 ⟩
⟦ program ds M ⟧ₚ = ⟦ M ⟧[ table ds ] · (λ _ → init)
