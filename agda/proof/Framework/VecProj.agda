{-

  Projecting component i from a tuple of a given size (proj,
  Framework/ListUtil.agda) of a list related pointwise to a vector of m
  components: when m is the size, the projection is related to
  component i of the vector (proj-pw); otherwise it fails (proj-bad).

-}

module proof.Framework.VecProj where

open import Framework.ListUtil using (proj; has-length)

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

module _ {A B : Set} {R : A → B → Set} where

  len-ok : ∀ {n xs} {ws : Vec B n} → Pointwise R xs (toList ws) → has-length n xs ≡ true
  len-ok {ws = []} [] = refl
  len-ok {ws = _ ∷ _} (_ ∷ rs) = len-ok rs

  len-bad : ∀ {m n xs} {ws : Vec B m} → m ≢ n → Pointwise R xs (toList ws) → has-length n xs ≡ false
  len-bad {n = zero} {ws = []} ne [] with () ← ne refl
  len-bad {n = suc n} {ws = []} ne [] = refl
  len-bad {n = zero} {ws = _ ∷ _} ne (_ ∷ rs) = refl
  len-bad {n = suc n} {ws = _ ∷ _} ne (_ ∷ rs) = len-bad (λ e → ne (cong suc e)) rs

  proj-pw : ∀ {n} (i : Fin n) {xs} {ws : Vec B n} → Pointwise R xs (toList ws)
    → M.Pointwise R (proj i xs) (just (lookup ws i))
  proj-pw zero {ws = _ ∷ _} (r ∷ rs) rewrite len-ok rs = M.just r
  proj-pw (suc i) {ws = _ ∷ _} (r ∷ rs) = proj-pw i rs

  proj-bad : ∀ {m n} (i : Fin n) {xs} {ws : Vec B m} → m ≢ n → Pointwise R xs (toList ws)
    → proj i xs ≡ nothing
  proj-bad zero {ws = []} ne [] = refl
  proj-bad zero {ws = _ ∷ _} ne (r ∷ rs) rewrite len-bad (λ e → ne (cong suc e)) rs = refl
  proj-bad (suc i) {ws = []} ne [] = refl
  proj-bad (suc i) {ws = _ ∷ _} ne (r ∷ rs) = proj-bad i (λ e → ne (cong suc e)) rs
