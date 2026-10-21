{-

  Lemmas about the semantics of ISWIMμ in the graph model
  (Mu/Semantics/Graph/ISWIM.agda), for simplify and adequacy: its denotations
  are Ok (monotone, continuous and consistent), by induction on the
  term, one line per construct, as for Clos5μ
  (Mu/proof/Semantics/Graph/Clos5.agda); fold and unfold are the
  identity.

-}

module Mu.proof.Semantics.Graph.ISWIM where

open import Mu.Semantics.Graph.ISWIM public

open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Continuity
open import proof.Framework.GraphModel.TypedOkBase using (Ok; Oks; ok-op; ok-vec; var-ok; split)
open import proof.Semantics.Graph.Prim using (primD-good)
open import Mu.Language.Type using (idx)
open import Mu.Language.ISWIM
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (length; replicate)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

ok : ∀ {Γ A} (M : Tm Γ A) → Ok ⟦ M ⟧
oks : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) → Oks (replicate (length Δ) ■) (split (length Δ) ⟦ Ms ⟧s)

ok (` x) = var-ok (idx x)
ok (lam N) = ok-op Λ-good ⟨ ok N , ptt ⟩
ok (app L M) = ok-op ⋆-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
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

con : ∀ {Γ A} (M : Tm Γ A) {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
con M c = proj₂ (proj₂ (ok M)) c
