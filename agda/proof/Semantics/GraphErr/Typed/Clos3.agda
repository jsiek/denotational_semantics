{-

  Lemmas about the semantics of Clos3ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/Clos3.agda): its denotations are monotone,
  continuous and consistent (Ok), by induction on the term, one line per
  construct, from the facts of proof/Framework/GraphModel/{TypedOk,
  TypedBinders}.agda: each operator is the error monad's kernel under
  binds (Good), and let is a bind into its body. Hence the code of a
  closure uses a finite part of the tuple of its free variables
  (code-fin), so that applied to that tuple it is the function of its
  body on it (ΛΛᵐ-⋆).

-}

module proof.Semantics.GraphErr.Typed.Clos3 where

open import Semantics.GraphErr.Typed.Clos3 public
open import proof.Framework.GraphModel.TypedOk using (Ok; Oks; ok-op; Ok-≃; var-ok; const-ok; let-ok; split; ok-vec; FinCode; fin-code) public
open import proof.Framework.GraphModel.TypedBinders using (ΛΛᵐ-⋆; code-ok) public

open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Continuity using (⋆-good; ℬ-good)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Typed.Clos2 using (app-good; get-good; case-good; prim-good; project-good)
open import Language.Typed.Type using (Any; tup; idx) renaming (⟪_⟫ to ⟪_⟫ᵗ)
open import Language.Typed.Clos3

open import Data.List using ([]; _∷_; replicate)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

ok : ∀ {Γ A} (M : Tm Γ A) → Ok ⟦ M ⟧
oks : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) → Oks (replicate n ■) (split n ⟦ Ms ⟧s)

ok (` x) = var-ok (idx x)
ok (clos N Ms) = ok-op (strict₂-good ⋆-good) ⟨ code-ok (ok N) , ⟨ ok-vec (𝒯ᵐ-good _) (oks Ms) , ptt ⟩ ⟩
ok (app L M) = ok-op app-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
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

{- the code of a closure uses a finite part of the tuple of its free variables -}
code-fin : ∀ {n} (N : Tm (Any ∷ ⟪ tup n ⟫ᵗ ∷ []) Any) → FinCode ⟦ N ⟧
code-fin N = fin-code (ok N)
