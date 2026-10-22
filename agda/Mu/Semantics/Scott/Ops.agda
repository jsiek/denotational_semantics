{-

  What the languages of ISWIMμ from Clos5μ on share in Scott domains:
  the tables of global definitions, as in the graph model
  (Mu/Semantics/Graph/Ops.agda).

  A table gives each definition of a program (Σ ∋ s) its meaning, a
  value. The definitions are given meaning newest first, each with the
  table of the older ones (tables, by the level of a reference); a
  reference to another means ⊥.

-}

open import MLTT.Spartan using (𝓤₀; 𝓤₁; _̇)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type using (_∋_; lvl)
open import Mu.Language.Clos5 using (DSig)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≟_)
open import Relation.Nullary using (Dec; yes; no)

module Mu.Semantics.Scott.Ops
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (⟨_⟩)
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (⊥𝔻)

Table : List DSig → 𝓤₁ ̇
Table Σ = ∀ {s} → Σ ∋ s → ⟨ 𝔻 ⟩

{- the table of the definitions ds (newest first), given the meaning of
   a definition with the table of the older ones -}
tables : ∀ {Σ} {D : DSig → Set} → (Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) → ∀ {ss} → All D ss → Table Σ
tables cd [] f = ⊥𝔻
tables cd {_ ∷ ss} (d ∷ ds) f = choose (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f)
 where
  {- (a `with` here, in a recursive function whose type mentions 𝔻, makes
     Agda's termination check very slow) -}
  choose : ∀ {P : Set} → Dec P → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
  choose (yes _) d e = d
  choose (no _) d e = e
