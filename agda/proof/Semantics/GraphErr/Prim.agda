module proof.Semantics.GraphErr.Prim where

open import Semantics.GraphErr.Prim public

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.ContinuityBase
  using (Continuous; Good; mk-good; one; done; approx-join; join-l; join-r)
open import proof.Framework.GraphModel.ErrorContinuity using (oneP; errs-cont)
open import proof.Semantics.Graph.Prim using (primD-mono; primD-consis; primD-cont)
open import Language.Prim using (Prim; Out; int; bool; δ)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ)
open import Data.List using (_∷_; [])
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- Monotonicity, consistency and continuity --------------------------------}

primᵉ-mono : ∀ p → monotone (■ ∷ ■ ∷ []) ■ (primᵉ p)
primᵉ-mono p ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ primᵉ p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G v (inj₁ s) = inj₁ (lower (primD-mono p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
                               ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩) v s)
  G v (inj₂ ⟨ refl , inj₁ e ⟩) =
    inj₂ ⟨ refl , inj₁ (errs-mono 2 ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩ e) ⟩
  G v (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ w , x ⟩) ⟩) = inj₂ ⟨ refl , inj₂ (inj₁ ⟨ wrong-mono D⊆ w , val∈-mono E⊆ x ⟩) ⟩
  G v (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ x , w ⟩) ⟩) = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ val∈-mono D⊆ x , wrong-mono E⊆ w ⟩) ⟩

{- a value consistent with an integer is an integer -}
int~ : ∀ {n} d → const {Int} n ~ d → IsInt d
int~ (const {Int} k) ⟨ refl , _ ⟩ = tt

~int : ∀ {n} d → d ~ const {Int} n → IsInt d
~int (const {Int} k) ⟨ refl , _ ⟩ = tt

primᵉ-consis : ∀ p → consistent _~_ (■ ∷ ■ ∷ []) ■ (primᵉ p)
primᵉ-consis p ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩) (primᵉ p ⟨ D' , ⟨ E' , ptt ⟩ ⟩)
  G u w (inj₁ s) (inj₁ s') =
    lower (primD-consis p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , ptt ⟩ ⟩) u w s s'
  G u w (inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩) (inj₂ ⟨ refl , e ⟩) = ⊥-elim (H e)
    where
    H : _ → _
    H (inj₁ (inj₁ ω∈)) with D~ _ _ n∈ ω∈
    ... | ()
    H (inj₁ (inj₂ ⟨ _ , inj₁ ω∈ ⟩)) with E~ _ _ m∈ ω∈
    ... | ()
    H (inj₂ (inj₁ ⟨ ⟨ d , ⟨ d∈ , ⟨ _ , ni ⟩ ⟩ ⟩ , _ ⟩)) = ni (int~ d (D~ _ _ n∈ d∈))
    H (inj₂ (inj₂ ⟨ _ , ⟨ d , ⟨ d∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) = ni (int~ d (E~ _ _ m∈ d∈))
  G u w (inj₂ ⟨ refl , e ⟩) (inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (H e)
    where
    H : _ → _
    H (inj₁ (inj₁ ω∈)) with D~ _ _ ω∈ n∈
    ... | ()
    H (inj₁ (inj₂ ⟨ _ , inj₁ ω∈ ⟩)) with E~ _ _ ω∈ m∈
    ... | ()
    H (inj₂ (inj₁ ⟨ ⟨ d , ⟨ d∈ , ⟨ _ , ni ⟩ ⟩ ⟩ , _ ⟩)) = ni (~int d (D~ _ _ d∈ n∈))
    H (inj₂ (inj₂ ⟨ _ , ⟨ d , ⟨ d∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) = ni (~int d (E~ _ _ d∈ m∈))
  G u w (inj₂ ⟨ refl , _ ⟩) (inj₂ ⟨ refl , _ ⟩) = tt

primᵉ-cont : ∀ p → Continuous (■ ∷ ■ ∷ []) (primᵉ p)
primᵉ-cont p Es NE oks v (inj₁ s) with primD-cont p Es NE oks v s
... | ⟨ ρ′ , ⟨ f , ⟨ s′ , v∈ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s′ , inj₁ v∈ ⟩ ⟩ ⟩
primᵉ-cont p ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE oks v (inj₂ ⟨ refl , inj₁ e ⟩) with errs-cont 2 ⟨ E₁ , ⟨ E₂ , ptt ⟩ ⟩ NE oks e
... | ⟨ a , e′ ⟩ = done (λ ρ → primᵉ p ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) a ω (inj₂ ⟨ refl , inj₁ e′ ⟩)
primᵉ-cont p ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ v (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ w , x ⟩) ⟩)
    with oneP E₁ c₁ w | oneP E₂ c₂ x
... | ⟨ a , ⟨ d , ⟨ d∈ , r ⟩ ⟩ ⟩ | ⟨ b , ⟨ e , ⟨ e∈ , r' ⟩ ⟩ ⟩ =
  done (λ ρ → primᵉ p ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ω
    (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ ⟨ d , ⟨ m₁ (join-l a b) d d∈ , r ⟩ ⟩ , ⟨ e , ⟨ m₂ (join-r a b) e e∈ , r' ⟩ ⟩ ⟩) ⟩)
primᵉ-cont p ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ v (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ x , w ⟩) ⟩)
    with oneP E₁ c₁ x | oneP E₂ c₂ w
... | ⟨ a , ⟨ d , ⟨ d∈ , r ⟩ ⟩ ⟩ | ⟨ b , ⟨ e , ⟨ e∈ , r' ⟩ ⟩ ⟩ =
  done (λ ρ → primᵉ p ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ω
    (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ d , ⟨ m₁ (join-l a b) d d∈ , r ⟩ ⟩ , ⟨ e , ⟨ m₂ (join-r a b) e e∈ , r' ⟩ ⟩ ⟩) ⟩)

primᵉ-good : ∀ {P} p → Good P (■ ∷ ■ ∷ []) (primᵉ p)
primᵉ-good p = mk-good (primᵉ-mono p) (primᵉ-consis p) (primᵉ-cont p)

primᵉ-≃ : ∀ p {D D' E E'} → D ≃ D' → E ≃ E'
  → primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ primᵉ p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
primᵉ-≃ p D≃ E≃ = mono-≃ (primᵉ-mono p) ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

{- a primitive on two integers is its result -}
primᵉ-fold : ∀ p n m → primᵉ p ⟨ ⌈ const {Int} n ⌉ , ⟨ ⌈ const {Int} m ⌉ , ptt ⟩ ⟩ ≃ ⌈ out (δ p n m) ⌉
primᵉ-fold p n m =
  ⟨ (λ { _ (inj₁ ⟨ n' , ⟨ m' , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩) → refl
       ; _ (inj₂ ⟨ refl , inj₁ (inj₁ ()) ⟩)
       ; _ (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₁ () ⟩) ⟩)
       ; _ (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₂ () ⟩) ⟩)
       ; _ (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ ⟨ _ , ⟨ refl , ⟨ _ , ni ⟩ ⟩ ⟩ , _ ⟩) ⟩) → ⊥-elim (ni tt)
       ; _ (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ⟨ _ , ⟨ refl , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩) ⟩) → ⊥-elim (ni tt) })
  , (λ { _ refl → inj₁ ⟨ n , ⟨ m , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩ }) ⟩
