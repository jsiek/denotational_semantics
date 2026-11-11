{-

  Lemmas about the tables of FPC in the graph model
  (FPC/Semantics/GraphModel/Ops.agda): a table is consistent when the meaning
  of each definition is, given a consistent table. Also lemmas about
  the update of a fixed frame: a read of the updated position finds the
  new meaning (≔-same), a read of another position the old one
  (≔-other), and an update preserves a pointwise relation between
  frames (≔-~).

-}

module FPC.proof.Semantics.GraphModel.Ops where

open import FPC.Semantics.GraphModel.Ops public
open import proof.Framework.GraphModel.TypedOkBase public

open import proof.Framework.GraphModel.Prelude
open import FPC.Language.Type using (_∋_; lvl)
open import FPC.Language.GlobalFun using (DSig)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)

ConT : ∀ {Σ} → Table Σ → Set
ConT {Σ} T = ∀ {s} (f : Σ ∋ s) → Con (T f)

tables-con : ∀ {Σ} {D : DSig → Set} {cd : Table Σ → ∀ {s} → D s → 𝒫 Value}
  → (∀ {T : Table Σ} → ConT T → ∀ {s} (d : D s) → Con (cd T d))
  → ∀ {ss} (ds : All D ss)
  → ConT (tables cd ds)
tables-con c [] f _ _ ()
tables-con c {_ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = c (tables-con c ds) d
... | no _ = tables-con c ds f

{- Frames -----------------------------------------------------------------------}

≔-same : ∀ {σ : Env Value} {X} i
  → (σ [ i ≔ X ]) i ≡ X
≔-same i with i ≟ i
... | yes _ = refl
... | no n = ⊥-elim (n refl)

≔-other : ∀ {σ : Env Value} {X} {i j}
  → i ≢ j
  → (σ [ i ≔ X ]) j ≡ σ j
≔-other {i = i} {j} n with i ≟ j
... | yes e = ⊥-elim (n e)
... | no _ = refl

≔-~ : ∀ {σ σ' : Env Value} {X X'} (R : 𝒫 Value → 𝒫 Value → Set) i
  → (∀ j → R (σ j) (σ' j))
  → R X X'
  → ∀ j → R ((σ [ i ≔ X ]) j) ((σ' [ i ≔ X' ]) j)
≔-~ R i r rX j with i ≟ j
... | yes _ = rX
... | no _ = r j
