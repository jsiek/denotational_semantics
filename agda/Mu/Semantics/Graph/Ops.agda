{-

  What the languages of ISWIMμ from Clos5μ on share in the graph
  model: the tables of global definitions, as in
  Semantics/Graph/Typed/Ops.agda (which also has project, which
  ISWIMμ does not have).

  A table gives each definition of a program (Σ ∋ s) its meaning. The
  definitions are given meaning newest first, each with the table of
  the older ones (tables, by the level of a reference); a reference to
  another means ∅.

-}

module Mu.Semantics.Graph.Ops where

open import Framework.GraphModel.Prelude
open import Mu.Language.Type using (_∋_; lvl)
open import Mu.Language.Clos5 using (DSig)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)

init : 𝒫 Value
init = ⌈ ⟨⟩ ⌉

Table : List DSig → Set₁
Table Σ = ∀ {s} → Σ ∋ s → 𝒫 Value

{- the table of the definitions ds (newest first), given the meaning of
   a definition with the table of the older ones -}
tables : ∀ {Σ} {D : DSig → Set} → (Table Σ → ∀ {s} → D s → 𝒫 Value) → ∀ {ss} → All D ss → Table Σ
tables cd [] f = ∅
tables cd {_ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = cd (tables cd ds) d
... | no _ = tables cd ds f
