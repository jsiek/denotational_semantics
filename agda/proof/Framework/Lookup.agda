{-

  Lemmas about typed indices (Framework/Membership.agda) and lookups in
  typed lists (Framework/Lookup.agda): the level of an index is below
  the length, and stays the same along ⊑; forgetting commutes with
  lookup; proofs of ⊑ are unique, and compose.

-}

module proof.Framework.Lookup where

open import Framework.Membership
open import Framework.Lookup using (_!_; forget)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (n<1+n; m<n⇒m<1+n; ≤-refl; ≤-trans; n≤1+n; <-irrefl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

private variable
  A : Set
  P : A → Set
  a : A
  xs ys zs : List A

lvl-< : (x : xs ∋ a) → lvl x < length xs
lvl-< {xs = _ ∷ xs} Z = n<1+n (length xs)
lvl-< (S x) = m<n⇒m<1+n (lvl-< x)

lvl-⊑ : (p : xs ⊑ ys) (x : xs ∋ a) → lvl (⊑-∋ p x) ≡ lvl x
lvl-⊑ here⊑ x = refl
lvl-⊑ (there⊑ p) x = lvl-⊑ p x

forget-! : (p : xs ⊑ ys) (ps : All P ys) (x : xs ∋ a) → forget p ps ! x ≡ ps ! ⊑-∋ p x
forget-! here⊑ ps x = refl
forget-! (there⊑ p) (_ ∷ ps) x = forget-! p ps x

⊑-len : xs ⊑ ys → length xs ≤ length ys
⊑-len here⊑ = ≤-refl
⊑-len (there⊑ p) = ≤-trans (⊑-len p) (n≤1+n _)

⊑-irr : (p q : xs ⊑ ys) → p ≡ q
⊑-irr here⊑ here⊑ = refl
⊑-irr here⊑ (there⊑ q) = ⊥-elim (<-irrefl refl (⊑-len q))
⊑-irr (there⊑ p) here⊑ = ⊥-elim (<-irrefl refl (⊑-len p))
⊑-irr (there⊑ p) (there⊑ q) = cong there⊑ (⊑-irr p q)

⊑-∋-trans : (p : xs ⊑ ys) (q : ys ⊑ zs) (x : xs ∋ a) → ⊑-∋ (⊑-trans p q) x ≡ ⊑-∋ q (⊑-∋ p x)
⊑-∋-trans p here⊑ x = refl
⊑-∋-trans p (there⊑ q) x = cong S (⊑-∋-trans p q x)

map-! : ∀ {Q : A → Set} (f : ∀ {x} → P x → Q x) (ps : All P xs) (x : xs ∋ a) → All-map f ps ! x ≡ f (ps ! x)
map-! f (_ ∷ ps) Z = refl
map-! f (_ ∷ ps) (S x) = map-! f ps x
