{-

  Lemmas about the semantics of Clos4ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/Clos4.agda): its denotations are monotone,
  continuous and consistent (Ok, as for Clos3ᵀ in
  proof/Semantics/GraphErr/Typed/Clos3.agda), by induction on the term
  from the facts of proof/Framework/GraphModel/{TypedOk,TypedBinders}.agda:
  each operator is Good but unpack, the existential binder of a closure
  (Unpack, unpack-ok), and code, a closed function (code-ok). Bodies
  use finite parts of the sets they are given (fin₁, fin₂), and code
  applied to sets of values contains its body on them (ΛΛᵐ-call).

-}

module proof.Semantics.GraphErr.Typed.Clos4 where

open import Semantics.GraphErr.Typed.Clos4 public
open import proof.Framework.GraphModel.TypedOk using (Ok; Oks; ok-op; Ok-≃; var-ok; const-ok; let-ok; split; ok-vec; fin₁; fin₂) public
open import proof.Framework.GraphModel.TypedBinders using (code-ok; ΛΛᵐ-call; car-witness; Unpack; unpack-ok) public

open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Continuity using (⋆₂-good; ℬ-good)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Typed.Clos2 using (get-good; case-good; prim-good; project-good)
open import Language.Typed.Type using (Any; idx)
open import Language.Typed.Clos4

open import Data.List using (_∷_; replicate)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

ok : ∀ {Γ A} (M : Tm Γ A) → Ok ⟦ M ⟧
oks : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) → Oks (replicate n ■) (split n ⟦ Ms ⟧s)

ok (` x) = var-ok (idx x)
ok (code N) = code-ok (ok N)
ok (call L M N) = ok-op (binds-good 3 ⋆₂-good) ⟨ ok L , ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩ ⟩
ok (pack L M) = ok-op pairᵐ-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
ok (unpack L B) = unpack-ok (ok L) (λ n → ok (B n))
ok (lit B c) = ok-op (ℬ-good B c) ptt
ok (tuple Ms) = ok-vec (𝒯ᵐ-good _) (oks Ms)
ok (get i M) = ok-op (get-good i) ⟨ ok M , ptt ⟩
ok (inl M) = ok-op inlᵐ-good ⟨ ok M , ptt ⟩
ok (inr M) = ok-op inrᵐ-good ⟨ ok M , ptt ⟩
ok (case L M N) = ok-op case-good ⟨ ok L , ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩ ⟩
ok (prim p L M) = ok-op (prim-good p) ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
ok (let′ M N) = let-ok (ok M) (ok N)
ok (inject G M) = ok M
ok (project G M) = ok-op (project-good _) ⟨ ok M , ptt ⟩

oks [] = ptt
oks (M ∷ Ms) = ⟨ ok M , oks Ms ⟩

con : ∀ {Γ A} (M : Tm Γ A) {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
con M c = proj₂ (proj₂ (ok M)) c
