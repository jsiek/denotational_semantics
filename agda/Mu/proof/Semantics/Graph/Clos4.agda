{-

  Lemmas about the semantics of Clos4μ in the graph model
  (Mu/Semantics/Graph/Clos4.agda): its denotations are Ok, by induction
  on the term, one line per construct (callc is callcᵈ), as for Clos4ᵀ.

-}

module Mu.proof.Semantics.Graph.Clos4 where

open import Mu.Semantics.Graph.Clos4 public

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Continuity
open import proof.Framework.GraphModel.TypedOkBase
open import proof.Semantics.Graph.Prim using (primD-good)
open import Mu.Language.Type using (idx)
open import Mu.Language.Clos4
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (length; replicate)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

ok : ∀ {Γ A} (M : Tm Γ A) → Ok ⟦ M ⟧
oks : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) → Oks (replicate (length Δ) ■) (split (length Δ) ⟦ Ms ⟧s)

ok (` x) = var-ok (idx x)
ok (code N) = ΛΛ-ok (ok N)
ok (pack L M) = ok-op pair-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
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

con : ∀ {Γ A} (M : Tm Γ A) {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
con M c = proj₂ (proj₂ (ok M)) c
