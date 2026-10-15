{-

  The semantics of CFGᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/CFG.agda) is monotone, continuous and
  consistent (Ok), under a consistent table: a simple expression is a
  term of Clos5ᵀ, a slot binding is a let (letᵐ, letᵐ-unfold), and a
  tail that forgets slots reindexes its environment (Ok-η, Ok-skip).

-}

module proof.Semantics.GraphErr.Typed.CFG where

open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Env using (•-~)
open import proof.Framework.GraphModel.TypedOk using (Ok; ok-op; Ok-≃; Ok-η; Ok-skip)
open import proof.Semantics.GraphErr.Typed.Clos2 using (case-good)
open import proof.Semantics.GraphErr.Typed.Clos5 using (ok)
open import Semantics.GraphErr.Typed.CFG
open import Semantics.GraphErr.Typed.Imp using (⌞_⌟)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open import Language.Typed.CFG
open import Framework.Membership using (_⊑_; here⊑; there⊑)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the head of the environment, and the rest without the forgotten slots -}
drop-ok : ∀ {Δ' Δ : Ctx} (p : Δ' ⊑ Δ) {E} → Ok E → Ok (λ ρ → E (ρ 0 • drop p (λ i → ρ (suc i))))
drop-ok here⊑ o = Ok-η o
drop-ok (there⊑ p) o = Ok-skip (drop-ok p o)

module _ {T : Table} (TC : ∀ k → Con (T k)) where

  tail-ok : ∀ {Σ Bs Δ} (t : Tail Σ Bs Δ) {B : BEnv Bs} → (∀ {Δ'} (l : Bs ∋ Δ') → Ok (B l)) → Ok (⟦ t ⟧ᵗ T B)
  tail-ok (return s) oB = ok TC M.⌜ ⌞ s ⌟ ⌝
  tail-ok (seq p s t) {B} oB = Ok-≃ (λ ρ → letᵐ-unfold {𝒮 s T ρ} {λ X → ⟦ t ⟧ᵗ T B (X • drop p ρ)})
    (ok-op letᵐ-good ⟨ ok TC M.⌜ ⌞ s ⌟ ⌝ , ⟨ drop-ok p (tail-ok t oB) , ptt ⟩ ⟩)
  tail-ok (goto l) oB = oB l
  tail-ok (case a p l₁ l₂) oB = ok-op case-good ⟨ ok TC M.⌜ a ⌝ᵃ , ⟨ drop-ok p (oB l₁) , ⟨ drop-ok p (oB l₂) , ptt ⟩ ⟩ ⟩

  blocks-ok : ∀ {Σ Bs} (bs : Blocks Σ Bs) {Δ} (l : Bs ∋ Δ) → Ok (blocks bs T l)
  blocks-ok (bs ▷ t) Z = tail-ok t (blocks-ok bs)
  blocks-ok (bs ▷ t) (S l) = blocks-ok bs l

  run-ok : ∀ {Σ Δ} (b : Body Σ Δ) → Ok (run b T)
  run-ok (body bs t) = tail-ok t (blocks-ok bs)

  codeᶜ-con : ∀ {Σ n} (b : Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) → Con (codeᶜ T b)
  codeᶜ-con b = ΛΛᵐ-con λ X X' Y Y' X~ Y~ → proj₂ (proj₂ (run-ok b)) (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~)
