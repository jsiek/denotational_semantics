{-

  Lemmas about the tables of FPC in the graph model
  (Mu/Semantics/GraphModel/Ops.agda): a table is consistent when the meaning
  of each definition is, given a consistent table.

-}

module Mu.proof.Semantics.GraphModel.Ops where

open import Mu.Semantics.GraphModel.Ops public
open import proof.Framework.GraphModel.TypedOkBase public

open import proof.Framework.GraphModel.Prelude
open import Mu.Language.Type using (_∋_; lvl)
open import Mu.Language.GlobalFun using (DSig)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)

ConT : ∀ {Σ} → Table Σ → Set
ConT {Σ} T = ∀ {s} (f : Σ ∋ s) → Con (T f)

tables-con : ∀ {Σ} {D : DSig → Set} {cd : Table Σ → ∀ {s} → D s → 𝒫 Value}
  → (∀ {T : Table Σ} → ConT T → ∀ {s} (d : D s) → Con (cd T d)) → ∀ {ss} (ds : All D ss) → ConT (tables cd ds)
tables-con c [] f _ _ ()
tables-con c {_ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = c (tables-con c ds) d
... | no _ = tables-con c ds f
