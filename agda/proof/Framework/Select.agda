{-

  Selections (Framework/Select.agda): Thin R fl xs ys says that ys are
  the kept xs, each related by R; then R relates the values at a Kept
  variable and at its squeeze.

-}

module proof.Framework.Select where

open import Framework.Select

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Level using (_⊔_)

data Thin {a b} {A : Set a} {B : Set b} (R : A → B → Set) : ∀ {n} (fl : Vec Bool n) → Vec A n → Vec B (count fl) → Set (a ⊔ b) where
  [] : Thin R [] [] []
  keep : ∀ {n fl x y xs ys} → R x y → Thin R {n} fl xs ys → Thin R (true ∷ fl) (x ∷ xs) (y ∷ ys)
  drop : ∀ {n fl x xs ys} → Thin R {n} fl xs ys → Thin R (false ∷ fl) (x ∷ xs) ys

thin-lookup : ∀ {a b} {A : Set a} {B : Set b} {R : A → B → Set} {n fl x y} {xs : Vec A n} {ys}
  → R x y → Thin R fl xs ys → ∀ i → Kept fl i → R (lookup (x ∷ xs) i) (lookup (y ∷ ys) (squeeze fl i))
thin-lookup r th zero _ = r
thin-lookup r (keep r' th) (suc zero) _ = r'
thin-lookup {fl = true ∷ fl} r (keep r' th) (suc (suc i)) k with squeeze fl (suc i) | thin-lookup r th (suc i) k
... | zero | t = t
... | suc j | t = t
thin-lookup r (drop th) (suc (suc i)) k = thin-lookup r th (suc i) k

{- a property of the variables that one of two terms uses -}
subL : ∀ {k ℓ} {u u' : Fin k → Bool} {P : Fin k → Set ℓ} → (∀ x → T (u x ∨ u' x) → P x) → ∀ x → T (u x) → P x
subL {u = u} h x t with u x | h x
... | true | h' = h' tt

subR : ∀ {k ℓ} {u u' : Fin k → Bool} {P : Fin k → Set ℓ} → (∀ x → T (u x ∨ u' x) → P x) → ∀ x → T (u' x) → P x
subR {u = u} h x t with u x | h x
... | true | h' = h' tt
... | false | h' = h' t
