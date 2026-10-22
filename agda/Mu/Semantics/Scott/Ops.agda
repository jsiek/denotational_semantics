{-

  What the languages of ISWIMμ from Clos5μ on share in Scott domains:
  the tables of global definitions, as in the graph model
  (Mu/Semantics/Graph/Ops.agda).

  A table gives each definition of a program (Σ ∋ s) its meaning, a
  value. The definitions are given meaning newest first, each with the
  table of the older ones (tables, by the level of a reference); a
  reference to another means ⊥.

-}

open import MLTT.Spartan using (𝓤₀; 𝓤₁; _̇; _＝_; refl)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type using (_∋_; lvl)
open import Mu.Language.Clos5 using (DSig)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥-elim)

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
{- (a `with` here, in a recursive function whose type mentions 𝔻, makes
   Agda's termination check very slow) -}
choose : ∀ {P : Set} → Dec P → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
choose (yes _) d e = d
choose (no _) d e = e

tables : ∀ {Σ} {D : DSig → Set} → (Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) → ∀ {ss} → All D ss → Table Σ
tables cd [] f = ⊥𝔻
tables cd {_ ∷ ss} (d ∷ ds) f = choose (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f)

{- the two cases of tables, as equations (proved here: reducing tables
   elsewhere is slow) -}
choose-yes : ∀ {P : Set} (q : Dec P) (d e : ⟨ 𝔻 ⟩) → P → choose q d e ＝ d
choose-yes (yes _) d e p = refl
choose-yes (no ¬p) d e p = ⊥-elim (¬p p)

choose-no : ∀ {P : Set} (q : Dec P) (d e : ⟨ 𝔻 ⟩) → ¬ P → choose q d e ＝ e
choose-no (yes p) d e ¬p = ⊥-elim (¬p p)
choose-no (no _) d e ¬p = refl

tables-yes : ∀ {Σ} {D : DSig → Set} (cd : Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) {s ss} (d : D s) (ds : All D ss) {t} (f : Σ ∋ t)
  → lvl f ≡ length ss → tables cd (d ∷ ds) f ＝ cd (tables cd ds) d
tables-yes cd {ss = ss} d ds f e = choose-yes (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f) e

tables-no : ∀ {Σ} {D : DSig → Set} (cd : Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) {s ss} (d : D s) (ds : All D ss) {t} (f : Σ ∋ t)
  → ¬ (lvl f ≡ length ss) → tables cd (d ∷ ds) f ＝ tables cd ds f
tables-no cd {ss = ss} d ds f ne = choose-no (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f) ne
