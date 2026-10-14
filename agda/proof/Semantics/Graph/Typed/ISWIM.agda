{-

  Lemmas about the semantics of ISWIMᵀ in the graph model
  (Semantics/Graph/Typed/ISWIM.agda): its denotations are monotone,
  continuous and consistent (Ok), by induction on the term, one line per
  construct, from the Good operators of the graph model
  (proof/Framework/GraphModel/{Continuity,TypedOkBase}.agda).

-}

module proof.Semantics.Graph.Typed.ISWIM where

open import Semantics.Graph.Typed.ISWIM public
open import proof.Semantics.Graph.Typed.Ops

open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim using (primD-good)
open import Language.Typed.Type using (Any)
open import Language.Typed.ISWIM

open import Data.Fin using (toℕ)
open import Data.List using (replicate)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

ok : ∀ {k A} (M : Tm k A) → Ok ⟦ M ⟧
oks : ∀ {k n} (Ms : Vec (Tm k Any) n) → Oks (replicate n ■) (split n ⟦ Ms ⟧s)

ok (` x) = var-ok (toℕ x)
ok (lam N) = ok-op Λ-good ⟨ ok N , ptt ⟩
ok (app L M) = ok-op ⋆-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
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

con : ∀ {k A} (M : Tm k A) {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
con M c = proj₂ (proj₂ (ok M)) c
