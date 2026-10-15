{-

  Lemmas about what the typed languages share in the graph model
  (Semantics/Graph/Typed/Ops.agda): project is Good (a guard,
  proof/Framework/GraphModel/TypedGuard.agda), and a table is consistent
  when the meaning of each definition is, given a consistent table.

-}

module proof.Semantics.Graph.Typed.Ops where

open import Semantics.Graph.Typed.Ops public
open import proof.Framework.GraphModel.TypedGuard using (guardᵖ-good; guardᵖ-≃) public
open import proof.Framework.GraphModel.TypedOkBase public

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.ContinuityBase using (Good)
open import Language.Typed.Type hiding (_≟_)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≟_)
open import Data.Unit using (⊤)
open import Data.Product using (proj₁)
open import Relation.Nullary using (yes; no)

project-good : ∀ F t → Good ⊤ (■ ∷ []) (λ Ds → projectᵍ F t (proj₁ Ds))
project-good F t = guardᵖ-good (accepts F t)

project-≃ : ∀ F t {D D'} → D ≃ D' → projectᵍ F t D ≃ projectᵍ F t D'
project-≃ F t = guardᵖ-≃ (accepts F t)

ConT : ∀ {Σ} → Table Σ → Set
ConT {Σ} T = ∀ {n} (f : Σ ∋ n) → Con (T f)

tables-con : ∀ {Σ} {D : ℕ → Set} {cd : Table Σ → ∀ {n} → D n → 𝒫 Value}
  → (∀ {T : Table Σ} → ConT T → ∀ {n} (d : D n) → Con (cd T d)) → ∀ {ns} (ds : All D ns) → ConT (tables cd ds)
tables-con c [] f _ _ ()
tables-con c {_ ∷ ns} (d ∷ ds) f with lvl f ≟ length ns
... | yes _ = c (tables-con c ds) d
... | no _ = tables-con c ds f
