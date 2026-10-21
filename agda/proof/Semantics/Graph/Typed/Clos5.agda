{-

  Lemmas about the semantics of Clos5ᵀ in the graph model
  (Semantics/Graph/Typed/Clos5.agda): with a consistent table, its
  denotations are Ok, by induction on the term, one line per construct
  (a reference is a constant); the table of a program is consistent.

-}

module proof.Semantics.Graph.Typed.Clos5 where

open import Semantics.Graph.Typed.Clos5 public
open import proof.Semantics.Graph.Typed.Ops

open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim using (primD-good)
open import Language.Typed.Type using (Any; idx)
open import Language.Typed.Clos5

open import Data.List using (replicate)
open import Data.List.Relation.Unary.All using (All)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

module _ {Σ} {T : Table Σ} (cT : ConT T) where
  ok : ∀ {Γ A} (M : Tm Σ Γ A) → Ok ⟦ M ⟧[ T ]
  oks : ∀ {Γ n} (Ms : Vec (Tm Σ Γ Any) n) → Oks (replicate n ■) (split n ⟦ Ms ⟧s[ T ])

  ok (` x) = var-ok (idx x)
  ok (fun-ref f) = const-ok (cT f)
  ok (pack L M) = ok-op pair-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (callc L M) = ok-op callc-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (lit B c) = ok-op (ℬ-good B c) ptt
  ok (tuple Ms) = ok-vec (𝒯-good _) (oks Ms)
  ok (get i M) = ok-op (proj-good i) ⟨ ok M , ptt ⟩
  ok (inl M) = ok-op inl-good ⟨ ok M , ptt ⟩
  ok (inr M) = ok-op inr-good ⟨ ok M , ptt ⟩
  ok (case L M N) = ok-op 𝒞-good ⟨ ok L , ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩ ⟩
  ok (prim p L M) = ok-op (primD-good p) ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (let′ M N) = ok-op letD-good ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩
  ok (inject G M) = ok M
  ok (project t M) = ok-op (project-good _ t) ⟨ ok M , ptt ⟩

  oks [] = ptt
  oks (M ∷ Ms) = ⟨ ok M , oks Ms ⟩

  con : ∀ {Γ A} (M : Tm Σ Γ A) {ρ} → Con-env ρ → Con (⟦ M ⟧[ T ] ρ)
  con M c = proj₂ (proj₂ (ok M)) c

  code-con : ∀ {n} (N : Code Σ n) → Con (code′ T N)
  code-con N = proj₂ (proj₂ (ΛΛ-ok (ok N))) {ρ = λ _ → init} (λ _ → Con-⌈⌉ ω)

table-con : ∀ {Σ} (ds : All (Code Σ) Σ) → ConT (table ds)
table-con = tables-con code-con
