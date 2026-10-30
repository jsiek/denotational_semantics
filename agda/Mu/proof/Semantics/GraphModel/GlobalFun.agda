{-

  Lemmas about the semantics of GlobalFunμ in the graph model
  (Mu/Semantics/GraphModel/GlobalFun.agda): with a consistent table, its
  denotations are Ok, by induction on the term, one line per construct
  (a reference is a constant); the table of a program is consistent.

-}

module Mu.proof.Semantics.GraphModel.GlobalFun where

open import Mu.Semantics.GraphModel.GlobalFun public
open import Mu.proof.Semantics.GraphModel.Ops

open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim using (primD-good)
open import Mu.Language.Type using (idx)
open import Mu.Language.GlobalFun
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (length; replicate)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

module _ {Σ} {T : Table Σ} (cT : ConT T) where
  ok : ∀ {Γ A} (M : Tm Σ Γ A) → Ok ⟦ M ⟧[ T ]
  oks : ∀ {Γ Δ} (Ms : All (Tm Σ Γ) Δ) → Oks (replicate (length Δ) ■) (split (length Δ) ⟦ Ms ⟧s[ T ])

  ok (` x) = var-ok (idx x)
  ok (fun-ref f) = const-ok (cT f)
  ok (pair L M) = ok-op pair-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (callc L M) = ok-op callc-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (lit B c) = ok-op (ℬ-good B c) ptt
  ok (tuple Ms) = ok-vec (𝒯-good _) (oks Ms)
  ok (get i M) = ok-op (proj-good (pos i)) ⟨ ok M , ptt ⟩
  ok (inl M) = ok-op inl-good ⟨ ok M , ptt ⟩
  ok (inr M) = ok-op inr-good ⟨ ok M , ptt ⟩
  ok (case L M N) = ok-op 𝒞-good ⟨ ok L , ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩ ⟩
  ok (prim p L M) = ok-op (primD-good p) ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (let′ M N) = ok-op letD-good ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩
  ok (fold M) = ok M
  ok (unfold M) = ok M

  oks [] = ptt
  oks (M ∷ Ms) = ⟨ ok M , oks Ms ⟩

  con : ∀ {Γ A} (M : Tm Σ Γ A) {ρ} → Con-env ρ → Con (⟦ M ⟧[ T ] ρ)
  con M c = proj₂ (proj₂ (ok M)) c

  code-con : ∀ {s} (N : Code Σ s) → Con (code′ T N)
  code-con N = proj₂ (proj₂ (ΛΛ-ok (ok N))) {ρ = λ _ → init} (λ _ → Con-⌈⌉ ⟨⟩)

table-con : ∀ {Σ} (ds : All (Code Σ) Σ) → ConT (table ds)
table-con = tables-con code-con
