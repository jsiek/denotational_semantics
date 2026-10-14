{-

  Answers (proof/Framework/Reduction.agda) for the operands of tuples
  that are vectors (Framework/ReductionVec.agda): the first, and then
  the rest, related pointwise, when each language's reduction of
  operands is red-∷ (reds-∷, by refl) and the target's values reduce to
  val.

-}

module proof.Framework.ReductionVec (Obs : Set) (o-error : Obs) where

open import proof.Framework.Reduction Obs o-error
open import Framework.ReductionVec Obs o-error public

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

module _ {S T : Set} {red : T → Red T} {Val : T → Set} {R : S → T → Set}
  (reds : ∀ {n} → Vec T n → Red (Vec T n))
  (reds-∷ : ∀ {n} X (Xs : Vec T n) → reds (X ∷ Xs) ≡ red-∷ X Xs (red X) (reds Xs))
  (val-red : ∀ {V} → Val V → red V ≡ val) where

  ans-∷ : ∀ {n M M' r r'} {Ms : Vec S n} {Ms' : Vec T n} → Pointwise R Ms Ms'
    → Ans red Val R M r M' → Ans reds (All Val) (Pointwise R) Ms r' Ms'
    → Ans reds (All Val) (Pointwise R) (M ∷ Ms) (red-∷ M Ms r r') (M' ∷ Ms')
  ans-∷ rs a as = ans-in (frame _ (λ X → reds-∷ X _)) (_∷ rs) a
    λ v m → ans-in (frame {g = λ Xs → _ ∷ Xs} _ (λ Xs → trans (reds-∷ _ Xs) (val-in (val-red v)))) (m ∷_) as
      λ vs ms → val ε (v ∷ vs) (m ∷ ms)

{- a component of a vector with a property -}
all-lookup : ∀ {A : Set} {P : A → Set} {n} {xs : Vec A n} → All P xs → ∀ i → P (lookup xs i)
all-lookup (p ∷ ps) zero = p
all-lookup (p ∷ ps) (suc i) = all-lookup ps i
