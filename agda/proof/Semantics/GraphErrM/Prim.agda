module proof.Semantics.GraphErrM.Prim where

open import Semantics.GraphErrM.Prim public

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono)
open import proof.Semantics.Graph.Prim using (primD-good)
open import Language.Prim using (Prim; δ)

open import Data.List using (_∷_; [])
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (refl)

{- primᵐ is primD, checked and bound, by definition -}
primᵐ-good : ∀ {P} p → Good P (■ ∷ ■ ∷ []) (primᵐ p)
primᵐ-good p = strict-good (strict₂-good (checkₒ-good (swap-good (checkₒ-good (swap-good (primD-good p))
                 (λ { w ⟨ n , ⟨ m , ⟨ _ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩ → inj₂ ⟨ _ , ⟨ m∈ , refl ⟩ ⟩ })))
                 (λ { w (inj₁ ⟨ refl , _ ⟩) → inj₁ refl
                    ; w (inj₂ ⟨ n , ⟨ m , ⟨ n∈ , _ ⟩ ⟩ ⟩) → inj₂ ⟨ _ , ⟨ n∈ , refl ⟩ ⟩ })))

primᵐ-≃ : ∀ p {D D' E E'} → D ≃ D' → E ≃ E'
  → primᵐ p ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ primᵐ p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
primᵐ-≃ p D≃ E≃ = mono-≃ (mono (primᵐ-good {⊤} p)) ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

{- a primitive on two integers is its result -}
primᵐ-fold : ∀ p n m → primᵐ p ⟨ ⌈ const {Int} n ⌉ , ⟨ ⌈ const {Int} m ⌉ , ptt ⟩ ⟩ ≃ ⌈ out (δ p n m) ⌉
primᵐ-fold p n m =
  ⟨ (λ { _ (inj₁ ⟨ refl , () ⟩)
       ; _ (inj₂ ⟨ _ , inj₁ ⟨ refl , () ⟩ ⟩)
       ; _ (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₁ ⟨ refl , ⟨ _ , ⟨ ⟨ refl , _ ⟩ , k ⟩ ⟩ ⟩ ⟩ ⟩) → ⊥-elim (k refl)
       ; _ (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ (inj₁ ⟨ refl , ⟨ _ , ⟨ ⟨ refl , _ ⟩ , k ⟩ ⟩ ⟩) ⟩ ⟩) → ⊥-elim (k refl)
       ; _ (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ (inj₂ ⟨ _ , ⟨ _ , ⟨ ⟨ refl , _ ⟩ , ⟨ ⟨ refl , _ ⟩ , refl ⟩ ⟩ ⟩ ⟩) ⟩ ⟩) → refl })
  , (λ { _ refl → inj₂ ⟨ ⟨ _ , ⟨ refl , (λ ()) ⟩ ⟩ , inj₂ ⟨ ⟨ _ , ⟨ refl , (λ ()) ⟩ ⟩
           , inj₂ (inj₂ ⟨ n , ⟨ m , ⟨ ⟨ refl , (λ ()) ⟩ , ⟨ ⟨ refl , (λ ()) ⟩ , refl ⟩ ⟩ ⟩ ⟩) ⟩ ⟩ }) ⟩
  where open import Data.Empty using (⊥-elim)
